"""
RK9 Tournament Monitor
Monitors live Pokemon tournament results and tracks player standings.

Two data modes:
  - JSON mode (recommended): parses RK9's structured standings JSON
    (the same shape as an exported "<id>_<division>.json" file - see
    --json-url / --json-file). This gives you the tournament's own
    authoritative placing (which accounts for resistance tie-breakers
    this script can't recompute on its own).
  - HTML mode (fallback): parses the public pairings page. Despite
    appearances, this page is server-rendered, not a JS-only SPA - each
    match row carries the players' current win/loss/tie record as HTML
    data attributes (data-wins/data-losses/data-ties/data-points), not
    as visible "(W-L-T) N pts" text. The original version of this script
    regex-matched visible text, which is how "Table 100 Paul Hinta" ended
    up recorded as a player name once table-number text sat next to a
    name with no separator - and, on the current page markup, why it
    found zero players at all (that visible text pattern no longer
    exists on the page anywhere). This version reads the structured
    data attributes directly instead, per round tab, and picks whichever
    division (Masters/Senior/Junior) you ask for. See CHANGES.md.

Note: rk9.gg's robots.txt disallows crawling /pairings/. HTML mode hits
that path directly, so it's meant for occasional personal/manual use,
not for unattended polling - use JSON mode for anything long-running.
"""

import argparse
import json
import logging
import os
import re
import signal
import sys
import tempfile
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Optional

import requests
from bs4 import BeautifulSoup
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

logger = logging.getLogger("rk9_monitor")

DEFAULT_USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
)

# Standard Pokemon VGC/TCG Swiss scoring: 3 points per win, 1 per tie.
# Used only when a data source (JSON) doesn't hand us points directly.
POINTS_PER_WIN = 3
POINTS_PER_TIE = 1

# Matches a trailing country tag like "Paul Chua [US]" -> ("Paul Chua", "US")
NAME_COUNTRY_RE = re.compile(r"^(.*?)\s*\[([A-Za-z]{2,3})\]\s*$")

# Matches a round tab-pane id like "P2R3" -> pod "P2", round 3.
ROUND_PANE_RE = re.compile(r"^(?P<pod>[A-Za-z0-9]+)R(?P<round>\d+)$")

DEFAULT_DIVISION = "masters"


@dataclass
class PlayerRecord:
    """A player's tournament record at a point in time."""

    name: str
    country: str
    wins: int
    losses: int
    ties: int
    points: Optional[int] = None
    placing: Optional[int] = None
    dropped: bool = False
    resistance_self: Optional[float] = None
    resistance_opp: Optional[float] = None
    resistance_oppopp: Optional[float] = None
    current_round: Optional[int] = None
    current_opponent: Optional[str] = None
    current_opponent_country: Optional[str] = None
    current_table: Optional[str] = None
    bye: bool = False

    def __post_init__(self):
        if self.points is None:
            self.points = self.wins * POINTS_PER_WIN + self.ties * POINTS_PER_TIE

    @property
    def record(self) -> str:
        return f"{self.wins}-{self.losses}-{self.ties}"

    @property
    def opponent_display(self) -> str:
        """Short human-readable description of the current-round matchup."""
        if self.bye:
            return "BYE"
        if self.current_opponent:
            country = f" [{self.current_opponent_country}]" if self.current_opponent_country else ""
            return f"{self.current_opponent}{country}"
        return "-"

    def __repr__(self):
        rank = f"#{self.placing} " if self.placing is not None else ""
        tag = " (DROPPED)" if self.dropped else ""
        return f"{rank}{self.name} [{self.country}] ({self.record}) {self.points} pts{tag}"

    def to_dict(self) -> Dict:
        d = {
            "name": self.name,
            "country": self.country,
            "wins": self.wins,
            "losses": self.losses,
            "ties": self.ties,
            "points": self.points,
            "record": self.record,
            "placing": self.placing,
            "dropped": self.dropped,
        }
        if self.resistance_self is not None:
            d["resistances"] = {
                "self": self.resistance_self,
                "opp": self.resistance_opp,
                "oppopp": self.resistance_oppopp,
            }
        if self.current_round is not None:
            d["current_round"] = self.current_round
            d["bye"] = self.bye
            d["current_opponent"] = self.current_opponent
            d["current_opponent_country"] = self.current_opponent_country
            d["current_table"] = self.current_table
        return d


def build_session(user_agent: str = DEFAULT_USER_AGENT) -> requests.Session:
    """A requests Session with sane timeouts and automatic retry/backoff
    on transient network errors and 5xx responses."""
    session = requests.Session()
    session.headers.update({"User-Agent": user_agent})
    retry = Retry(
        total=3,
        backoff_factor=1.5,
        status_forcelist=(429, 500, 502, 503, 504),
        allowed_methods=("GET",),
        raise_on_status=False,
    )
    adapter = HTTPAdapter(max_retries=retry)
    session.mount("https://", adapter)
    session.mount("http://", adapter)
    return session


DISCORD_EMBED_DESCRIPTION_LIMIT = 4096
DISCORD_FIELD_VALUE_LIMIT = 1024
DISCORD_EMBED_COLOR = 0x3B82F6  # a plain blue; purely cosmetic


class DiscordNotifier:
    """Posts standings to a Discord channel via an incoming webhook, then
    edits that same message on every later update - so the channel ends up
    with one continuously-updated "live scoreboard" message instead of a
    new post every refresh.

    The posted message's id is persisted to a small state file so the
    monitor can keep editing the same message even if it's restarted.
    """

    def __init__(
        self,
        webhook_url: str,
        state_path: str = "discord_message_state.json",
        username: str = "RK9 Tournament Monitor",
    ):
        self.webhook_url = webhook_url.rstrip("/")
        self.state_path = Path(state_path)
        self.username = username
        self.session = build_session()
        self.message_id = self._load_message_id()

    def _load_message_id(self) -> Optional[str]:
        try:
            with open(self.state_path, "r", encoding="utf-8") as f:
                data = json.load(f)
            if data.get("webhook_url") == self.webhook_url:
                return data.get("message_id")
        except (OSError, json.JSONDecodeError):
            pass
        return None

    def _save_message_id(self, message_id: Optional[str]):
        try:
            with open(self.state_path, "w", encoding="utf-8") as f:
                json.dump({"webhook_url": self.webhook_url, "message_id": message_id}, f)
        except OSError as e:
            logger.error("Couldn't save Discord message state to %s: %s", self.state_path, e)

    def send_or_update(self, embed: Dict) -> bool:
        """Edit the existing scoreboard message if we have one; otherwise
        (first run, or the old message is gone) post a new one and
        remember its id. Returns True on success."""
        payload = {"username": self.username, "embeds": [embed]}

        if self.message_id:
            try:
                response = self.session.patch(
                    f"{self.webhook_url}/messages/{self.message_id}", json=payload, timeout=15
                )
                if response.status_code == 404:
                    logger.warning(
                        "The Discord scoreboard message no longer exists (deleted?) - posting a new one."
                    )
                    self.message_id = None
                else:
                    response.raise_for_status()
                    return True
            except requests.RequestException as e:
                logger.error("Failed to edit Discord message, will try posting a new one instead: %s", e)
                self.message_id = None

        try:
            response = self.session.post(f"{self.webhook_url}?wait=true", json=payload, timeout=15)
            response.raise_for_status()
            self.message_id = response.json().get("id")
            self._save_message_id(self.message_id)
            return True
        except requests.RequestException as e:
            logger.error("Failed to post to Discord webhook: %s", e)
            return False


def build_discord_embed(
    players: List[PlayerRecord],
    changes: Dict,
    source_description: str,
    division: Optional[str] = None,
    max_rows: int = 40,
) -> Dict:
    """Build a Discord embed showing the current (filtered) standings as a
    monospace table, plus a short "recent changes" field when there's
    anything new since the last update."""
    header = f"{'#':<4} {'Player':<22} {'Cty':<3} {'Record':<8} {'Pts':>4}"
    rows = []
    for i, p in enumerate(players[:max_rows], 1):
        rank = p.placing if p.placing is not None else i
        status = " (DROPPED)" if p.dropped else ""
        name = p.name if len(p.name) <= 22 else p.name[:21] + "…"
        rows.append(f"{rank:<4} {name:<22} {p.country:<3} {p.record:<8} {p.points:>4}{status}")

    omitted = len(players) - max_rows
    table_lines = [header, "-" * len(header)] + (rows or ["(no players match the current filters)"])
    if omitted > 0:
        table_lines.append(f"... and {omitted} more")
    table = "\n".join(table_lines)

    description = f"```\n{table}\n```"
    if len(description) > DISCORD_EMBED_DESCRIPTION_LIMIT:
        cutoff = DISCORD_EMBED_DESCRIPTION_LIMIT - len("\n... (truncated)\n```") - 3
        description = description[:cutoff] + "\n... (truncated)\n```"

    embed = {
        "title": f"{division.title()} Standings" if division else "Tournament Standings",
        "description": description,
        "color": DISCORD_EMBED_COLOR,
        "footer": {"text": f"Source: {source_description}"},
        "timestamp": datetime.now(timezone.utc).isoformat(),
    }

    change_notes = []
    for rc in changes.get("rank_changes", [])[:10]:
        arrow = "↑" if rc["new_placing"] < rc["old_placing"] else "↓"
        change_notes.append(f"{arrow} **{rc['name']}**: #{rc['old_placing']} → #{rc['new_placing']}")
    for u in changes.get("updated_records", [])[:10]:
        change_notes.append(f"• **{u['name']}**: {u['old_record']} → {u['new_record']}")

    fields = []

    matchup_lines = []
    for p in players[:max_rows]:
        if p.dropped:
            continue
        matchup_lines.append(f"**{p.name}** vs {p.opponent_display}")
    if matchup_lines:
        value = "\n".join(matchup_lines)
        if len(value) > DISCORD_FIELD_VALUE_LIMIT:
            value = value[: DISCORD_FIELD_VALUE_LIMIT - 15] + "\n... (more)"
        round_label = f" (Round {players[0].current_round})" if players and players[0].current_round else ""
        fields.append({"name": f"Current Matchups{round_label}", "value": value, "inline": False})

    if change_notes:
        value = "\n".join(change_notes)
        if len(value) > DISCORD_FIELD_VALUE_LIMIT:
            value = value[: DISCORD_FIELD_VALUE_LIMIT - 15] + "\n... (more)"
        fields.append({"name": "Recent changes", "value": value, "inline": False})

    if fields:
        embed["fields"] = fields

    return embed


class RK9TournamentMonitor:
    """Monitors RK9-style tournament standings, either from a structured
    JSON source or (as a fallback) by scraping the pairings page."""

    def __init__(
        self,
        json_url: Optional[str] = None,
        json_file: Optional[str] = None,
        html_url: Optional[str] = None,
        division: str = DEFAULT_DIVISION,
        output_path: str = "tournament_data.json",
        discord: Optional[DiscordNotifier] = None,
    ):
        if not (json_url or json_file or html_url):
            raise ValueError("Provide one of json_url, json_file, or html_url")

        self.json_url = json_url
        self.json_file = json_file
        self.html_url = html_url
        self.division = division
        self.output_path = Path(output_path)
        self.discord = discord

        self.previous_data: Optional[List[PlayerRecord]] = None
        self.session = build_session()
        self._stop_requested = False

    @property
    def mode(self) -> str:
        if self.json_url or self.json_file:
            return "json"
        return "html"

    @property
    def source_description(self) -> str:
        if self.json_url:
            return self.json_url
        if self.json_file:
            return str(self.json_file)
        return self.html_url

    # ---- fetching -----------------------------------------------------

    def fetch_json(self) -> Optional[list]:
        """Fetch and parse the standings JSON, from a URL or a local file."""
        try:
            if self.json_file:
                with open(self.json_file, "r", encoding="utf-8") as f:
                    return json.load(f)
            response = self.session.get(self.json_url, timeout=15)
            response.raise_for_status()
            return response.json()
        except requests.RequestException as e:
            logger.error("Error fetching JSON from %s: %s", self.source_description, e)
            return None
        except (json.JSONDecodeError, OSError) as e:
            logger.error("Error reading JSON from %s: %s", self.source_description, e)
            return None

    def fetch_html(self) -> Optional[str]:
        """Fetch the tournament pairings page HTML."""
        try:
            response = self.session.get(self.html_url, timeout=15)
            response.raise_for_status()
            return response.text
        except requests.RequestException as e:
            logger.error("Error fetching page %s: %s", self.html_url, e)
            return None

    # ---- parsing --------------------------------------------------------

    @staticmethod
    def _split_name_country(raw_name: str) -> (str, str):
        match = NAME_COUNTRY_RE.match(raw_name.strip())
        if match:
            return match.group(1).strip(), match.group(2).upper()
        return raw_name.strip(), "??"

    def parse_json_players(self, data: list) -> List[PlayerRecord]:
        """Parse RK9-style standings JSON: a list of entries shaped like
        {"name": "Paul Chua [US]", "placing": 1,
         "record": {"wins": 15, "losses": 2, "ties": 0},
         "resistances": {...}, "decklist": [...], "drop": -1, "rounds": {...}}
        """
        players = []
        for entry in data:
            raw_name = entry.get("name", "")
            name, country = self._split_name_country(raw_name)
            rec = entry.get("record") or {}
            res = entry.get("resistances") or {}

            current_round = current_opponent = current_opponent_country = current_table = None
            is_bye = False
            rounds = entry.get("rounds") or {}
            if rounds:
                try:
                    latest_round_num = max(int(k) for k in rounds.keys())
                    latest = rounds[str(latest_round_num)]
                    opp_raw = (latest.get("name") or "").strip()
                    if opp_raw.upper() == "BYE":
                        is_bye = True
                    elif opp_raw:
                        current_opponent, current_opponent_country = self._split_name_country(opp_raw)
                    current_round = latest_round_num
                    table = latest.get("table")
                    current_table = str(table) if table not in (None, "") else None
                except (ValueError, TypeError, KeyError):
                    pass  # malformed rounds data - just skip the opponent info for this player

            players.append(
                PlayerRecord(
                    name=name,
                    country=country,
                    wins=int(rec.get("wins", 0)),
                    losses=int(rec.get("losses", 0)),
                    ties=int(rec.get("ties", 0)),
                    placing=entry.get("placing"),
                    dropped=entry.get("drop", -1) not in (-1, None),
                    resistance_self=res.get("self"),
                    resistance_opp=res.get("opp"),
                    resistance_oppopp=res.get("oppopp"),
                    current_round=current_round,
                    current_opponent=current_opponent,
                    current_opponent_country=current_opponent_country,
                    current_table=current_table,
                    bye=is_bye,
                )
            )
        return players

    @staticmethod
    def discover_divisions(soup: BeautifulSoup) -> Dict[str, str]:
        """Map each division's display label (e.g. "Masters") to its pod id
        (e.g. "P2") by reading the top-level division tabs. Pod ids aren't
        fixed across tournaments - they're just assigned in whatever order
        RK9 set up that event's pods - so this has to be discovered per page
        rather than hardcoded."""
        divisions = {}
        for tab in soup.select('a[id$="-tab"]'):
            tab_id = tab.get("id", "")
            # Division tabs look like "P2-tab"; round sub-tabs look like
            # "P2R1-tab" - skip those by requiring no digit right after the
            # pod's leading letter(s).
            pod_id = tab_id[: -len("-tab")]
            if re.search(r"R\d+$", pod_id):
                continue
            label = tab.get_text(strip=True)
            if label:
                divisions[label] = pod_id
        return divisions

    @staticmethod
    def _resolve_division(divisions: Dict[str, str], division: str) -> Optional[str]:
        """Case-insensitive, substring match of the requested division
        against discovered labels, e.g. "masters" matches "Masters in
        Round 3"."""
        wanted = division.strip().lower()
        for label, pod_id in divisions.items():
            if wanted in label.lower():
                return pod_id
        return None

    def parse_html_players(self, html: str) -> List[PlayerRecord]:
        """Extract player records from the pairings page for the configured
        division. The page renders each round's matches server-side, with
        each player's current record as data-wins/data-losses/data-ties/
        data-points attributes on a <span class="record">. Rounds are
        processed oldest-to-newest so that, per player, the latest round
        they appear in - which reflects their cumulative record entering
        (or completed within) that round - wins out.
        """
        soup = BeautifulSoup(html, "html.parser")

        divisions = self.discover_divisions(soup)
        if not divisions:
            logger.warning("Couldn't find any division tabs on the page at all.")
            return []

        pod_id = self._resolve_division(divisions, self.division)
        if pod_id is None:
            logger.warning(
                "Division '%s' not found on this page. Available divisions: %s",
                self.division,
                ", ".join(divisions.keys()),
            )
            return []

        round_panes = [
            pane
            for pane in soup.select(f'div[id^="{pod_id}R"]')
            if ROUND_PANE_RE.match(pane.get("id", ""))
        ]
        round_panes.sort(key=lambda p: int(ROUND_PANE_RE.match(p["id"]).group("round")))

        players: Dict[str, PlayerRecord] = {}
        for pane in round_panes:
            round_num = int(ROUND_PANE_RE.match(pane["id"]).group("round"))
            for row in pane.select("div.match"):
                # Skip the header row ("Player 1" / "Table #" / "Player 2"),
                # which is a plain div.match without the row-cols-3 class
                # that actual data rows carry.
                if "row-cols-3" not in row.get("class", []):
                    continue

                table_el = row.select_one(".tablenumber")
                table_num = table_el.get_text(strip=True) if table_el else None

                # Gather whichever player slots in this row actually have a
                # name+record (a bye leaves the second slot empty), so each
                # player can be recorded as the other's current opponent.
                seats = []
                for player_col in row.select("div.player"):
                    name_el = player_col.select_one("span.name")
                    record_el = player_col.select_one("span.record")
                    if name_el is None or record_el is None:
                        continue  # empty slot (e.g. a bye's absent opponent)
                    raw_name = name_el.get_text(" ", strip=True)
                    name, country = self._split_name_country(raw_name)
                    if name:
                        seats.append((name, country, record_el))

                for i, (name, country, record_el) in enumerate(seats):

                    def as_int(attr):
                        try:
                            return int(record_el.get(attr, 0))
                        except (TypeError, ValueError):
                            return 0

                    opponent = seats[1 - i] if len(seats) == 2 else None

                    players[name] = PlayerRecord(
                        name=name,
                        country=country,
                        current_round=round_num,
                        current_opponent=opponent[0] if opponent else None,
                        current_opponent_country=opponent[1] if opponent else None,
                        current_table=table_num,
                        bye=opponent is None,
                        wins=as_int("data-wins"),
                        losses=as_int("data-losses"),
                        ties=as_int("data-ties"),
                        points=as_int("data-points"),
                    )

        return list(players.values())

    # ---- standings --------------------------------------------------------

    @staticmethod
    def sort_players(players: List[PlayerRecord]) -> None:
        """Sort in place. Prefer the tournament's own placing (it accounts
        for resistance tie-breakers we don't have); fall back to points/wins
        when placing isn't available (HTML mode)."""
        if players and all(p.placing is not None for p in players):
            players.sort(key=lambda p: p.placing)
        else:
            players.sort(key=lambda p: (p.points, p.wins), reverse=True)

    def get_current_standings(self) -> Optional[List[PlayerRecord]]:
        """Fetch + parse + sort the current standings.

        Returns None only on an actual fetch failure (network error, bad
        status code, invalid JSON). An empty list is returned - and NOT
        treated as a failure here - when the request succeeded but no
        player records could be parsed out of the response; the caller is
        responsible for surfacing that distinction.
        """
        if self.mode == "json":
            data = self.fetch_json()
            if data is None:
                return None
            players = self.parse_json_players(data)
        else:
            html = self.fetch_html()
            if html is None:
                return None
            players = self.parse_html_players(html)
            if not players:
                self._save_html_debug_dump(html)

        self.sort_players(players)
        return players

    @staticmethod
    def _save_html_debug_dump(html: str, path: str = "last_fetch_debug.html"):
        """Save the raw HTML we received when 0 players could be parsed out
        of it, so it's easy to inspect why (wrong --division name, RK9
        changed the page markup again, the tournament hasn't started
        pairings yet, etc.)."""
        try:
            with open(path, "w", encoding="utf-8") as f:
                f.write(html)
            logger.warning(
                "Fetched the page successfully (HTTP OK) but found 0 player records in it. "
                "Saved the raw HTML received to '%s' for inspection. Check the warning above "
                "for the specific reason (unknown division, no matching pairings, etc.).",
                path,
            )
        except OSError as e:
            logger.error("Also failed to save debug HTML dump: %s", e)

    @staticmethod
    def apply_filters(
        players: List[PlayerRecord],
        filter_players: Optional[List[str]] = None,
        filter_countries: Optional[List[str]] = None,
    ) -> List[PlayerRecord]:
        """Filter players by name (case-insensitive partial match) or country."""
        filtered = players

        if filter_players:
            filter_lower = [name.lower() for name in filter_players]
            filtered = [
                p for p in filtered if any(fname in p.name.lower() for fname in filter_lower)
            ]

        if filter_countries:
            filter_upper = {code.upper() for code in filter_countries}
            filtered = [p for p in filtered if p.country in filter_upper]

        return filtered

    def detect_changes(self, current_players: List[PlayerRecord]) -> Dict:
        """Detect new players, record changes, and rank movement since the
        last fetch."""
        changes = {
            "new_players": [],
            "updated_records": [],
            "rank_changes": [],
            "timestamp": datetime.now().isoformat(),
        }

        if self.previous_data is None:
            changes["new_players"] = [p.to_dict() for p in current_players]
            return changes

        prev_by_name = {p.name: p for p in self.previous_data}

        for player in current_players:
            prev_player = prev_by_name.get(player.name)
            if prev_player is None:
                changes["new_players"].append(player.to_dict())
                continue

            if (player.wins, player.losses, player.ties) != (
                prev_player.wins,
                prev_player.losses,
                prev_player.ties,
            ):
                changes["updated_records"].append(
                    {
                        "name": player.name,
                        "old_record": prev_player.record,
                        "new_record": player.record,
                        "old_points": prev_player.points,
                        "new_points": player.points,
                    }
                )

            if (
                player.placing is not None
                and prev_player.placing is not None
                and player.placing != prev_player.placing
            ):
                changes["rank_changes"].append(
                    {
                        "name": player.name,
                        "old_placing": prev_player.placing,
                        "new_placing": player.placing,
                    }
                )

        return changes

    # ---- output --------------------------------------------------------

    @staticmethod
    def print_standings(players: List[PlayerRecord]):
        """Print current standings in a formatted table."""
        show_opponents = any(p.current_opponent or p.bye for p in players)

        print("\n" + "=" * 78)
        print(f"Tournament Standings - {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        print("=" * 78)
        header = f"{'Rank':<6} {'Player':<25} {'Country':<8} {'Record':<12} {'Points':<8}"
        if show_opponents:
            header += " Current Opponent"
        print(header)
        print("-" * 78)

        for i, player in enumerate(players, 1):
            rank = player.placing if player.placing is not None else i
            status = " (DROPPED)" if player.dropped else ""
            line = (
                f"{rank:<6} {player.name:<25} {player.country:<8} "
                f"{player.record:<12} {player.points:<8}{status}"
            )
            if show_opponents and not player.dropped:
                line += f"  vs {player.opponent_display}"
            print(line)

        print("=" * 78)

    def save_data(self, players: List[PlayerRecord], changes: Dict):
        """Save current data to a JSON file atomically (write to a temp
        file, then rename) so a crash or Ctrl+C mid-write can't corrupt
        the output."""
        data = {
            "timestamp": datetime.now().isoformat(),
            "source": self.source_description,
            "mode": self.mode,
            "standings": [p.to_dict() for p in players],
            "recent_changes": changes,
        }

        directory = self.output_path.parent if self.output_path.parent != Path("") else Path(".")
        fd, tmp_path = tempfile.mkstemp(prefix=".tournament_data_", dir=str(directory))
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2)
            os.replace(tmp_path, self.output_path)
        except OSError as e:
            logger.error("Failed to save data to %s: %s", self.output_path, e)
            if os.path.exists(tmp_path):
                os.remove(tmp_path)

    def load_previous_data(self) -> Optional[List[PlayerRecord]]:
        """Load standings saved by a previous run from self.output_path, if
        any. This is what lets change/rank-change detection work across
        separate process runs (e.g. one `--once` invocation per scheduled
        run, as opposed to one long-lived `monitor()` loop where state just
        stays in memory the whole time)."""
        if not self.output_path.exists():
            return None
        try:
            with open(self.output_path, "r", encoding="utf-8") as f:
                data = json.load(f)
            players = []
            for s in data.get("standings", []):
                resistances = s.get("resistances") or {}
                players.append(
                    PlayerRecord(
                        name=s["name"],
                        country=s["country"],
                        wins=s["wins"],
                        losses=s["losses"],
                        ties=s["ties"],
                        points=s.get("points"),
                        placing=s.get("placing"),
                        dropped=s.get("dropped", False),
                        resistance_self=resistances.get("self"),
                        resistance_opp=resistances.get("opp"),
                        resistance_oppopp=resistances.get("oppopp"),
                        current_round=s.get("current_round"),
                        current_opponent=s.get("current_opponent"),
                        current_opponent_country=s.get("current_opponent_country"),
                        current_table=s.get("current_table"),
                        bye=s.get("bye", False),
                    )
                )
            return players
        except (OSError, json.JSONDecodeError, KeyError) as e:
            logger.warning(
                "Couldn't load previous standings from %s (starting fresh): %s", self.output_path, e
            )
            return None

    # ---- monitor loop --------------------------------------------------------

    def request_stop(self, *_args):
        self._stop_requested = True

    def run_once(
        self,
        save_to_file: bool = True,
        filter_players: Optional[List[str]] = None,
        filter_countries: Optional[List[str]] = None,
    ) -> bool:
        """Do a single fetch/parse/print/save cycle. Returns True on success."""
        if self.previous_data is None:
            self.previous_data = self.load_previous_data()

        players = self.get_current_standings()
        if players is None:
            print("Failed to fetch data (network/HTTP error - see the message above)")
            return False
        if not players:
            print(
                "Fetched the page OK, but found 0 player records in it. "
                "See the warning above (and last_fetch_debug.html, in HTML mode) for why."
            )
            return False

        filtered_players = self.apply_filters(players, filter_players, filter_countries)
        changes = self.detect_changes(filtered_players)
        self.print_standings(filtered_players)

        if changes["rank_changes"]:
            print("\nRANK CHANGES:")
            for rc in changes["rank_changes"]:
                arrow = "up" if rc["new_placing"] < rc["old_placing"] else "down"
                print(f"  - {rc['name']}: #{rc['old_placing']} -> #{rc['new_placing']} ({arrow})")

        if changes["updated_records"]:
            print("\nRECORD UPDATES:")
            for update in changes["updated_records"]:
                print(
                    f"  - {update['name']}: {update['old_record']} -> {update['new_record']} "
                    f"({update['old_points']} -> {update['new_points']} pts)"
                )

        if changes["new_players"]:
            print(f"\nNEW PLAYERS: {len(changes['new_players'])} added")

        if save_to_file:
            self.save_data(filtered_players, changes)

        if self.discord:
            embed = build_discord_embed(
                filtered_players, changes, self.source_description, division=self.division
            )
            if self.discord.send_or_update(embed):
                print("\nDiscord scoreboard message updated")
            else:
                print("\nFailed to update Discord - see the error above")

        self.previous_data = filtered_players
        return True

    def monitor(
        self,
        refresh_interval: int = 60,
        save_to_file: bool = True,
        filter_players: Optional[List[str]] = None,
        filter_countries: Optional[List[str]] = None,
        max_consecutive_failures: int = 5,
    ):
        """Continuously monitor the tournament until stopped (Ctrl+C, or
        SIGTERM) or too many consecutive fetch failures occur."""
        print(f"Starting tournament monitor ({self.mode} mode): {self.source_description}")
        print(f"Refresh interval: {refresh_interval} seconds")

        if filter_players:
            print(f"Tracking players: {', '.join(filter_players)}")
        if filter_countries:
            print(f"Tracking countries: {', '.join(filter_countries)}")

        print("Press Ctrl+C to stop")

        signal.signal(signal.SIGINT, self.request_stop)
        try:
            signal.signal(signal.SIGTERM, self.request_stop)
        except (ValueError, AttributeError):
            pass  # SIGTERM isn't available on every platform (e.g. some Windows setups)

        iteration = 0
        consecutive_failures = 0

        while not self._stop_requested:
            iteration += 1
            print(f"\n[Refresh #{iteration}] Fetching data...")

            success = self.run_once(save_to_file, filter_players, filter_countries)
            consecutive_failures = 0 if success else consecutive_failures + 1

            if consecutive_failures >= max_consecutive_failures:
                print(
                    f"\n{consecutive_failures} consecutive failures - stopping. "
                    "Check the source URL and your connection."
                )
                break

            if self._stop_requested:
                break

            # Back off a bit longer if the last fetch failed, so we don't
            # hammer a struggling/blocked source.
            wait = refresh_interval * (2 if not success else 1)
            print(f"\nNext refresh in {wait} seconds...")
            for _ in range(wait):
                if self._stop_requested:
                    break
                time.sleep(1)

        print("\n\nMonitoring stopped")
        if save_to_file and self.previous_data:
            self.save_data(self.previous_data, self.detect_changes(self.previous_data))
            print(f"Final standings saved to {self.output_path}")


def main():
    parser = argparse.ArgumentParser(
        description="Monitor RK9-style tournament results in real-time",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Monitor from a local JSON snapshot (e.g. one you saved from your browser)
  python rk9_tournament_monitor.py --json-file 0000172_Masters.json --once

  # Monitor from a live JSON API endpoint, once you have that URL
  python rk9_tournament_monitor.py --json-url https://rk9.gg/.../Masters.json

  # Fall back to scraping the public pairings page (best-effort)
  python rk9_tournament_monitor.py --url https://rk9.gg/pairings/WCS02wAQpCIaqFmXxER4

  # Track specific players (still limited to Canada by default - add --countries ALL to lift that)
  python rk9_tournament_monitor.py --json-file data.json --players EricLuong JohnDoe

  # Track other/additional countries with a 30 second refresh
  python rk9_tournament_monitor.py --url ... --countries CA US UK --interval 30

  # Show every country, not just Canada
  python rk9_tournament_monitor.py --url ... --countries ALL

  # Monitor the Senior division instead of Masters
  python rk9_tournament_monitor.py --url ... --division senior

  # Post standings to Discord (one message, edited in place each refresh)
  python rk9_tournament_monitor.py --url ... --discord-webhook https://discord.com/api/webhooks/...
        """,
    )

    source = parser.add_mutually_exclusive_group()
    source.add_argument("--json-url", type=str, help="URL of the RK9 standings JSON endpoint")
    source.add_argument("--json-file", type=str, help="Path to a local standings JSON file")
    source.add_argument(
        "--url",
        type=str,
        help="Tournament pairings page URL to scrape (fallback mode; robots.txt-restricted, "
        "best used for occasional manual checks rather than long unattended runs)",
    )

    parser.add_argument(
        "--players", "-p", nargs="+", help="Filter by player name (partial match, case-insensitive)"
    )
    parser.add_argument(
        "--countries",
        "-c",
        nargs="+",
        default=["CA"],
        help="Filter by country codes, e.g. CA US UK (default: CA). Pass --countries ALL to show everyone.",
    )
    parser.add_argument(
        "--division",
        type=str,
        default=DEFAULT_DIVISION,
        help="Division to monitor in HTML mode: masters, senior, or junior (default: masters). "
        "Matched case-insensitively against whatever RK9 labels the tab, e.g. 'Masters in Round 3'.",
    )
    parser.add_argument(
        "--interval", "-i", type=int, default=60, help="Refresh interval in seconds (default: 60)"
    )
    parser.add_argument("--no-save", action="store_true", help="Disable saving to a JSON file")
    parser.add_argument(
        "--output", type=str, default="tournament_data.json", help="Path to save standings JSON to"
    )
    parser.add_argument(
        "--once", action="store_true", help="Fetch and print standings a single time, then exit"
    )
    parser.add_argument(
        "--log-level",
        type=str,
        default="WARNING",
        choices=["DEBUG", "INFO", "WARNING", "ERROR"],
        help="Logging verbosity for diagnostic messages (default: WARNING)",
    )

    discord_group = parser.add_argument_group("Discord")
    discord_group.add_argument(
        "--discord-webhook",
        type=str,
        help="Discord webhook URL to post standings to. One message is posted, then edited in "
        "place on every later refresh (a live scoreboard), instead of a new message each time.",
    )
    discord_group.add_argument(
        "--discord-username",
        type=str,
        default="RK9 Tournament Monitor",
        help="Display name the webhook posts as (default: 'RK9 Tournament Monitor')",
    )
    discord_group.add_argument(
        "--discord-state",
        type=str,
        default="discord_message_state.json",
        help="Where to remember the scoreboard message id between runs "
        "(default: discord_message_state.json)",
    )

    args = parser.parse_args()
    logging.basicConfig(level=getattr(logging, args.log_level), format="%(levelname)s: %(message)s")

    if not (args.json_url or args.json_file or args.url):
        # Default tournament to monitor when no source is specified.
        args.url = "https://rk9.gg/pairings/WCS02wAQpCIaqFmXxER4"

    if args.countries and len(args.countries) == 1 and args.countries[0].upper() == "ALL":
        args.countries = None

    discord_notifier = None
    if args.discord_webhook:
        discord_notifier = DiscordNotifier(
            webhook_url=args.discord_webhook,
            state_path=args.discord_state,
            username=args.discord_username,
        )

    monitor = RK9TournamentMonitor(
        json_url=args.json_url,
        json_file=args.json_file,
        html_url=args.url,
        division=args.division,
        output_path=args.output,
        discord=discord_notifier,
    )

    if args.once:
        ok = monitor.run_once(
            save_to_file=not args.no_save,
            filter_players=args.players,
            filter_countries=args.countries,
        )
        sys.exit(0 if ok else 1)

    monitor.monitor(
        refresh_interval=args.interval,
        save_to_file=not args.no_save,
        filter_players=args.players,
        filter_countries=args.countries,
    )


if __name__ == "__main__":
    main()
"""
Treasure Hunt Discord Bot
--------------------------
- /start         : [Organizer only, run once in #admin] Starts the hunt for ALL teams
                    at once — posts "HUNT IS LIVE" + each team's first clue in their
                    own channel. Blocked if already started; use /reset first to restart.
- /reset         : [Organizer only, run in #admin] Wipes ALL progress: clears every team's
                    private channel, #admin, and #team-standings; resets Team_Routes,
                    Teams timestamps, and the Results tab. For testing before the real event.
- /end           : [Organizer only, run in #admin] Ends the hunt, freezes further /scan
                    submissions, sends each team their final clue count + time in their
                    own channel, and snapshots final standings to a Results sheet tab.
- /announce      : [Organizer only, run in #admin] Sends every team a heads-up that the
                    hunt is starting soon, pointing them to #how-to-play. Auto-removed
                    the moment /start runs.
- /commands      : [Organizer only, run in #admin] Lists all organizer commands.
- /scan <code>   : verify a QR code against the team's next expected location.
                    On success, deletes the old clue message and posts the next one
                    (only one clue is ever visible in the channel at a time), and updates
                    a persistent "X/Y clues solved" progress message in that team's channel.
                    Wrong guesses stack (so a team can see their attempt history) but all
                    get cleared the instant they get it right.

- Silent Top 5 leaderboard, auto-refreshing in #leaderboard
- Full admin dashboard (progress + elapsed time per team) auto-refreshing in a dedicated
  #team-standings channel (kept separate from #admin so command confirmations and the
  heartbeat don't get buried once there are 20+ teams), plus an instant ping there
  when a team finishes
- Heartbeat message in #admin every 15 min (single message, edited in place — doesn't spam)
- Auto-created/refreshed #how-to-play channel under the "Information" category with
  player-facing rules and commands

MESSAGE STYLING: Embeds are used ONLY for three things — the clue itself (purple), the
"✅ Correct!" prompt (green), and the "❌ Not Quite" wrong-code message (red). Everything
else (HUNT IS LIVE banner, progress tracker, leaderboard, dashboard, announce, completion,
end-of-hunt results, heartbeat) is plain text. The progress tracker is created once, before
the first clue is ever posted, and is always edited in place afterward — since the clue
message gets deleted and freshly re-posted on every solve, this keeps progress positioned
above the clue in the channel without any extra bookkeeping.

PERFORMANCE NOTE: /scan is the hot path (called constantly by every team). To make it as
fast as possible, static/slow-changing data (Config clues+QR values, which Discord channel
belongs to which team, and each team's route/solved-state) is cached in memory and rebuilt
only at /start and /reset, instead of re-reading Google Sheets on every single scan attempt.
A correct scan still writes through to the Sheet for durability, but that write runs in the
background (a worker thread) concurrently with the Discord replies, instead of blocking them.

Setup:
  pip install -r requirements.txt
  Fill in .env with your bot token
  Place your Google service_account.json in the same folder
  Run: python bot.py

Discord permission notes:
  - The bot needs "Manage Messages" in team channels + #admin + #team-standings to delete/purge.
  - #admin and #team-standings must explicitly grant the bot's role View Channel / Send
    Messages / Read Message History / Manage Messages under Channel-specific permissions —
    server-wide role permissions alone are not enough if a channel has its own overwrites.
  - The bot needs "Manage Channels" to auto-create #admin, #team-standings, and #how-to-play.

Note on ephemeral messages: Discord does not allow a bot to edit or delete an ephemeral
message from an earlier, separate command invocation — each ephemeral reply is permanently
tied to the interaction that created it. That's why /scan's feedback (progress, wrong-code
notices, clues) is delivered as normal tracked channel messages instead: they can be
edited in place and deleted once solved, which is what actually stops them from stacking.
"""

import os
import io
import asyncio
import datetime
import discord
from discord import app_commands
from discord.ext import tasks
import gspread
from google.oauth2.service_account import Credentials
from dotenv import load_dotenv

load_dotenv()

BOT_TOKEN = os.getenv("DISCORD_BOT_TOKEN")
SPREADSHEET_NAME = os.getenv("SPREADSHEET_NAME", "TreasureHunt_Master")

LEADERBOARD_CHANNEL_NAME = "leaderboard"
ADMIN_CHANNEL_NAME = "admin"
STANDINGS_CHANNEL_NAME = "team-standings"
HOW_TO_PLAY_CHANNEL_NAME = "how-to-play"
PHOTO_CATEGORY_NAME = "Photo Proofs"
TEAM_CATEGORY_NAME = "Teams"
HOW_TO_PLAY_CATEGORY_NAME = "Information"
HEARTBEAT_INTERVAL_MINUTES = 15
PURPLE_ACCENT = 0x9B59B6  # Accent color for clue embeds ONLY
GREEN_ACCENT = 0x2ECC71   # Accent color for "correct" embeds
RED_ACCENT = 0xE74C3C     # Accent color for "wrong code" embeds

# ---------- Google Sheets setup ----------
SCOPES = [
    "https://www.googleapis.com/auth/spreadsheets",
    "https://www.googleapis.com/auth/drive.readonly",
]
creds = Credentials.from_service_account_file("service_account.json", scopes=SCOPES)
gc = gspread.authorize(creds)
sheet = gc.open(SPREADSHEET_NAME)

teams_ws = sheet.worksheet("Teams")
routes_ws = sheet.worksheet("Team_Routes")
config_ws = sheet.worksheet("Config")
settings_ws = sheet.worksheet("Settings")
# NOTE: "Registrations" (the Google Form response tab) is intentionally NOT opened here —
# it's optional and may be created/linked after the bot is already running. It's fetched
# lazily by get_registrations_ws() instead, so adding it later doesn't require a restart.

# ---------- Discord setup ----------
intents = discord.Intents.default()
intents.message_content = True
intents.guilds = True


class TreasureHuntBot(discord.Client):
    def __init__(self):
        super().__init__(intents=intents)
        self.tree = app_commands.CommandTree(self)

        self.leaderboard_message_id = None
        self.dashboard_message_id = None
        self.heartbeat_message_id = None
        self.active_clue_messages = {}   # team_name -> (channel_id, message_id) of the currently-visible clue
        self.progress_messages = {}      # team_name -> (channel_id, message_id) of the "X/Y solved" tracker
        self.status_messages = {}        # team_name -> list of (channel_id, message_id) "wrong code" attempts
        self.announce_messages = {}      # team_name -> (channel_id, message_id) of the pre-hunt heads-up
        self.live_header_messages = {}   # team_name -> (channel_id, message_id) of "HUNT IS LIVE" header

        # ---- In-memory caches (this is what makes /scan fast) ----
        self.config_cache = {}           # location_id -> {"clue_text": str, "qr_value": str}
        self.channel_team_cache = {}     # discord_channel_id (int) -> team_name
        self.team_row_cache = {}         # team_name -> row index in Teams sheet
        self.route_cache = {}            # team_name -> [{"row_index", "location_id", "solved"}, ...] in order
        self.hunt_started_at = None      # cached string, set at /start, cleared at /reset
        self.hunt_ended = False          # cached bool, set at /end, cleared at /reset
        self.team_locks = {}             # team_name -> asyncio.Lock, serializes /scan per team
        self.awaiting_photo = {}         # team_name -> {"location_id": str, "next_idx": int, "is_finished": bool}
        self.photo_prompt_messages = {}  # team_name -> (channel_id, message_id) of the "upload a photo" prompt
        self.photo_sent_messages = {}    # team_name -> (channel_id, message_id) of the latest "Photo is sent." confirmation

        # header_name -> 1-based column index, per sheet tab — resolved from row 1 instead of
        # hardcoded letters, so writes still land in the right place if you reorder columns.
        self.header_maps = {}

    async def setup_hook(self):
        await self.tree.sync()


client = TreasureHuntBot()


# ============================================================
# Cache builders — these do the actual Sheets reads. Called at
# startup, /start, and /reset — NEVER from inside /scan itself.
# ============================================================

def get_header_map(ws) -> dict:
    """Reads row 1 of a worksheet and returns {header_name: 1-based column index}. This is
    what lets every write below target a column by NAME instead of a hardcoded letter — so
    reordering columns in the Sheet (which people do) can't silently misdirect a write."""
    headers = ws.row_values(1)
    return {str(h).strip(): idx for idx, h in enumerate(headers, start=1) if str(h).strip()}


def refresh_header_maps():
    """Re-reads column positions for every sheet the bot writes to. Called alongside the
    other cache builders (startup, /start, /reset) so a column reorder is picked up the next
    time setup runs, without needing a header lookup on every single write."""
    client.header_maps = {
        "Teams": get_header_map(teams_ws),
        "Team_Routes": get_header_map(routes_ws),
        "Settings": get_header_map(settings_ws),
        "Config": get_header_map(config_ws),
    }


def col(sheet_key: str, header_name: str, fallback: int = None) -> int:
    """Look up a column's current index by header name. Falls back to the documented default
    position only if the header map hasn't been built yet or the header is genuinely missing
    (so a mid-event bot restart doesn't hard-crash on the very first write)."""
    hm = client.header_maps.get(sheet_key)
    if hm and header_name in hm:
        return hm[header_name]
    if fallback is not None:
        return fallback
    raise KeyError(f"Column '{header_name}' not found in the {sheet_key} sheet's header row.")


def build_static_caches():
    """Config (clue text + QR values) and Teams->channel mapping. Safe to call often;
    only run synchronously from setup commands, never per-scan."""
    refresh_header_maps()
    config_records = config_ws.get_all_records()
    client.config_cache = {
        row.get("Location_ID"): {
            "clue_text": row.get("Clue_Text", "(no clue text found)"),
            "qr_value": str(row.get("QR_Value", "")).strip(),
        }
        for row in config_records if row.get("Location_ID")
    }

    team_records = teams_ws.get_all_records()
    client.channel_team_cache = {}
    client.team_row_cache = {}
    for idx, row in enumerate(team_records, start=2):
        team_name = row.get("Team_Name")
        if not team_name:
            continue
        client.team_row_cache[team_name] = idx
        channel_id_raw = row.get("Discord_Channel_ID")
        if channel_id_raw:
            try:
                client.channel_team_cache[int(channel_id_raw)] = team_name
            except (TypeError, ValueError):
                pass


def build_route_cache():
    """team_name -> ordered list of route steps with live solved-state. Rebuilt at /start
    and /reset so it reflects the Sheet's current truth at those moments."""
    records = routes_ws.get_all_records()
    by_team = {}
    for idx, row in enumerate(records, start=2):  # sheet row number (row 1 = header)
        team = row.get("Team_Name")
        if not team:
            continue
        by_team.setdefault(team, []).append({
            "row_index": idx,
            "location_id": row.get("Location_ID"),
            "solved": str(row.get("Solved", "")).strip().upper() == "Y",
            "seq": row.get("Sequence_Position", 0),
        })
    for team in by_team:
        by_team[team].sort(key=lambda r: r["seq"])
    client.route_cache = by_team


def team_channel_id(team_name: str):
    """Reverse-lookup a team's channel ID from the cache."""
    for ch_id, name in client.channel_team_cache.items():
        if name == team_name:
            return ch_id
    return None


def get_team_lock(team_name: str) -> asyncio.Lock:
    """One lock per team, created on first use. Serializes /scan handling per team so two
    near-simultaneous submissions (e.g. two teammates both scanning quickly) can't both read
    the same 'not yet solved' cache state and double-process the same clue — which is the
    likely cause of old clues sometimes not getting cleaned up before a new one was posted."""
    lock = client.team_locks.get(team_name)
    if lock is None:
        lock = asyncio.Lock()
        client.team_locks[team_name] = lock
    return lock


# ============================================================
# Slow-path helpers — still hit the Sheet directly. Used only by
# infrequent commands (/end, dashboard loop) where a fresh read matters
# more than raw speed, or as one-off setup steps.
# ============================================================

def get_setting(key: str):
    records = settings_ws.get_all_records()
    for row in records:
        if row.get("Key") == key:
            return row.get("Value")
    return None


def set_setting(key: str, value):
    records = settings_ws.get_all_records()
    value_col = col("Settings", "Value", fallback=2)
    for idx, row in enumerate(records, start=2):
        if row.get("Key") == key:
            settings_ws.update_cell(idx, value_col, value)
            return
    settings_ws.append_row([key, value, "Auto-managed by bot"])


# ============================================================
# Registrations (Google Form sign-up) — team channel + membership setup
# ------------------------------------------------------------
# Expected setup: ONE Google Form response per TEAM, filled in by the team leader, listing
# every teammate's Discord User ID (the numeric ID from Discord's "Copy User ID" — NOT their
# username/tag). Link the Form's responses to a sheet tab named exactly "Registrations".
# Google Forms auto-adds a "Timestamp" column, which is fine and simply ignored.
#
# Required column:      Team_Name
# Discord ID columns:   any column whose header starts with "Discord_ID" — e.g.
#                        Discord_ID_1, Discord_ID_2, Discord_ID_3, Discord_ID_4 (one per
#                        Form question). Add/remove columns freely for teams of different
#                        sizes — the bot picks up however many are present and just skips
#                        any that are left blank for a given team.
# ============================================================

def get_registrations_ws():
    """Looked up fresh every time (not cached at import) so linking/creating the
    Registrations tab after the bot is already running doesn't require a restart."""
    try:
        return sheet.worksheet("Registrations")
    except gspread.exceptions.WorksheetNotFound:
        return None


def get_team_registrations():
    """Reads the Registrations tab (one row per TEAM, submitted by the team leader) and
    collects every Discord user ID listed for that team.

    Returns (teams, bad_rows):
      teams    -> dict[team_name] -> list[int Discord user IDs]
      bad_rows -> list[str] describing any value that couldn't be parsed (missing team name,
                  a non-numeric Discord ID in some column, etc.) so the organizer can fix the
                  Form response.
    """
    ws = get_registrations_ws()
    if ws is None:
        return {}, [
            "No 'Registrations' tab found. Link your Google Form's responses to a sheet "
            "tab named exactly 'Registrations' with a Team_Name column and one or more "
            "Discord_ID_1 / Discord_ID_2 / ... columns."
        ]

    records = ws.get_all_records()
    if not records:
        return {}, []

    # Any column whose header starts with "Discord_ID" is treated as one member's ID slot —
    # this way teams of 3, 4, 5+ members all work without changing the bot's code, just the
    # Form/sheet columns.
    id_columns = [key for key in records[0].keys() if str(key).strip().lower().startswith("discord_id")]
    if not id_columns:
        return {}, [
            "The Registrations tab has no columns starting with 'Discord_ID' "
            "(e.g. Discord_ID_1, Discord_ID_2, ...)."
        ]

    teams: dict = {}
    bad_rows = []
    for idx, row in enumerate(records, start=2):
        team = str(row.get("Team_Name", "")).strip()
        if not team:
            bad_rows.append(f"Row {idx}: missing Team_Name — skipped entirely.")
            continue

        member_ids = []
        for col in id_columns:
            raw = str(row.get(col, "")).strip()
            if not raw:
                continue  # blank slot (e.g. a 3-person team on a 4-slot form) — fine, skip
            if not raw.isdigit():
                bad_rows.append(
                    f"Row {idx} ({team}), column '{col}': \"{raw}\" isn't a plain numeric "
                    f"Discord user ID — that member was skipped."
                )
                continue
            member_ids.append(int(raw))

        if not member_ids:
            bad_rows.append(f"Row {idx} ({team}): no valid Discord IDs found — team skipped.")
            continue

        teams.setdefault(team, []).extend(member_ids)
    return teams, bad_rows


async def ensure_team_category(guild: discord.Guild):
    """Creates the private 'Teams' category once, reusing #admin's permissions so organizers
    can see every team channel by default (individual members are then added per-channel).
    Returns (category, error), same pattern as ensure_photo_category."""
    category = discord.utils.get(guild.categories, name=TEAM_CATEGORY_NAME)
    if category is not None:
        return category, None

    admin_channel = discord.utils.get(guild.text_channels, name=ADMIN_CHANNEL_NAME)
    overwrites = dict(admin_channel.overwrites) if admin_channel else {}
    overwrites[guild.default_role] = discord.PermissionOverwrite(view_channel=False)
    try:
        category = await guild.create_category(TEAM_CATEGORY_NAME, overwrites=overwrites)
        return category, None
    except discord.Forbidden:
        return None, (
            "missing permissions — the bot's role needs **Manage Channels** and "
            "**Manage Roles** to create a private category with custom overwrites."
        )
    except discord.HTTPException as e:
        return None, str(e)


async def create_or_update_team_channel(guild: discord.Guild, category, team_name: str, member_ids: list):
    """Creates (or updates) a team's private channel and grants view/send access to exactly
    the Discord user IDs registered for that team, on top of whatever the category already
    grants organizers. Returns (channel, found_members, missing_ids, error)."""
    channel_name = team_name.lower().replace(" ", "-")
    channel = discord.utils.get(category.text_channels, name=channel_name)

    overwrites = dict(channel.overwrites) if channel else {}
    overwrites[guild.default_role] = discord.PermissionOverwrite(view_channel=False)

    found_members, missing_ids = [], []
    for uid in member_ids:
        member = guild.get_member(uid)
        if member is None:
            missing_ids.append(uid)
            continue
        overwrites[member] = discord.PermissionOverwrite(
            view_channel=True, send_messages=True, read_message_history=True
        )
        found_members.append(member)

    try:
        if channel is None:
            channel = await guild.create_text_channel(channel_name, category=category, overwrites=overwrites)
        else:
            await channel.edit(overwrites=overwrites)
    except discord.Forbidden:
        return None, found_members, missing_ids, "missing permissions (Manage Channels / Manage Roles)"
    except discord.HTTPException as e:
        return None, found_members, missing_ids, str(e)

    return channel, found_members, missing_ids, None


def upsert_team_channel_id(team_name: str, channel_id: int):
    """Writes this team's channel ID into the Teams sheet — creates the row if the team
    doesn't have one yet (e.g. it only exists so far because of a Registrations submission)."""
    records = teams_ws.get_all_records()
    channel_col = col("Teams", "Discord_Channel_ID", fallback=2)
    for idx, row in enumerate(records, start=2):
        if row.get("Team_Name") == team_name:
            teams_ws.update_cell(idx, channel_col, str(channel_id))
            return
    teams_ws.append_row([team_name, str(channel_id), "", 0, "", ""])


def get_or_create_results_ws():
    try:
        return sheet.worksheet("Results")
    except gspread.exceptions.WorksheetNotFound:
        ws = sheet.add_worksheet(title="Results", rows=100, cols=6)
        ws.append_row(["Rank", "Team_Name", "Clues_Solved", "Clues_Required", "Time_Taken", "Ended_At"])
        return ws


def clear_results_ws():
    try:
        ws = sheet.worksheet("Results")
    except gspread.exceptions.WorksheetNotFound:
        return
    existing = ws.get_all_values()
    if len(existing) > 1:
        ws.delete_rows(2, len(existing))


def write_results_snapshot(status, ended_at):
    ws = get_or_create_results_ws()
    existing = ws.get_all_values()
    if len(existing) > 1:
        ws.delete_rows(2, len(existing))
    rows = []
    for rank, s in enumerate(status, start=1):
        rows.append([rank, s["team"], s["solved"], s["total"], s["elapsed"], ended_at])
    if rows:
        ws.append_rows(rows)


def format_duration(seconds: float):
    seconds = int(seconds)
    h, rem = divmod(seconds, 3600)
    m, s = divmod(rem, 60)
    if h > 0:
        return f"{h}h {m}m {s}s"
    if m > 0:
        return f"{m}m {s}s"
    return f"{s}s"


def get_full_team_status():
    """Full, authoritative per-team status straight from the Sheet. Used by /end and the
    slow-refreshing (30s) dashboard loop — not by /scan, so its cost doesn't matter there."""
    team_records = teams_ws.get_all_records()
    routes = routes_ws.get_all_records()

    counts, totals, last_solve = {}, {}, {}
    for row in routes:
        team = row.get("Team_Name")
        if not team:
            continue
        totals[team] = totals.get(team, 0) + 1
        counts.setdefault(team, 0)
        if str(row.get("Solved", "")).strip().upper() == "Y":
            counts[team] += 1
            solved_at = row.get("Solved_At")
            if solved_at:
                last_solve[team] = solved_at

    status = []
    now = datetime.datetime.now()
    for row in team_records:
        team = row.get("Team_Name")
        if not team:
            continue
        started_raw = str(row.get("Started_At", "")).strip()
        finished_raw = str(row.get("Finished_At", "")).strip()

        elapsed_str = "not started"
        if started_raw:
            try:
                started_dt = datetime.datetime.strptime(started_raw, "%Y-%m-%d %H:%M:%S")
                if finished_raw:
                    finished_dt = datetime.datetime.strptime(finished_raw, "%Y-%m-%d %H:%M:%S")
                    elapsed_str = format_duration((finished_dt - started_dt).total_seconds()) + " (finished)"
                else:
                    elapsed_str = format_duration((now - started_dt).total_seconds()) + " (in progress)"
            except ValueError:
                elapsed_str = "unknown"

        status.append({
            "team": team,
            "solved": counts.get(team, 0),
            "total": totals.get(team, 0),
            "elapsed": elapsed_str,
            "last_activity": last_solve.get(team, "—"),
        })

    status.sort(key=lambda x: x["solved"], reverse=True)
    return status


def get_top5():
    routes = routes_ws.get_all_records()
    counts = {}
    for row in routes:
        team = row.get("Team_Name")
        if not team:
            continue
        counts.setdefault(team, 0)
        if str(row.get("Solved", "")).strip().upper() == "Y":
            counts[team] += 1
    ranked = sorted(counts.items(), key=lambda x: x[1], reverse=True)
    return ranked[:5]


# ============================================================
# Embed styling helpers
# ------------------------------------------------------------
# Embeds are used ONLY for: the clue itself (purple), the "correct!"
# prompt (green), and the "wrong code" message (red). Every other
# bot message (banners, progress, leaderboard, dashboard, announce,
# completion, results, heartbeat, etc.) is plain text, as before.
# ============================================================

def build_embed(description: str, title: str = None, footer: str = None) -> discord.Embed:
    """Purple-accented embed — reserved for clues only."""
    embed = discord.Embed(description=description, color=PURPLE_ACCENT)
    if title:
        embed.title = title
    if footer:
        embed.set_footer(text=footer)
    return embed


def build_correct_embed(description: str, title: str = None) -> discord.Embed:
    """Green-accented embed — used only for the 'correct!' message."""
    embed = discord.Embed(description=description, color=GREEN_ACCENT)
    if title:
        embed.title = title
    return embed


def build_wrong_embed(description: str, title: str = None) -> discord.Embed:
    """Red-accented embed — used only for the 'wrong code' message."""
    embed = discord.Embed(description=description, color=RED_ACCENT)
    if title:
        embed.title = title
    return embed


# ============================================================
# Message lifecycle helpers (clue / progress / wrong-code / announce)
# ============================================================

async def delete_tracked_message(tracker: dict, team_name: str):
    """Generic helper: delete a message tracked in the given dict for this team, if any."""
    location = tracker.get(team_name)
    if not location:
        return
    channel_id, message_id = location
    channel = client.get_channel(channel_id)
    if channel is None:
        tracker.pop(team_name, None)
        return
    try:
        msg = await channel.fetch_message(message_id)
        await msg.delete()
    except (discord.NotFound, discord.Forbidden):
        pass
    finally:
        tracker.pop(team_name, None)


async def delete_active_clue_message(team_name: str):
    await delete_tracked_message(client.active_clue_messages, team_name)


async def cleanup_finished_team_channel(team_name: str):
    """Removes the leftover 'HUNT IS LIVE' header and any lingering clue/wrong-code/progress
    messages once a team is done — leaves the channel clean for the final message."""
    await delete_tracked_message(client.live_header_messages, team_name)
    await delete_tracked_message(client.active_clue_messages, team_name)
    await delete_tracked_message(client.progress_messages, team_name)
    await delete_tracked_message(client.photo_sent_messages, team_name)
    await clear_wrong_code_messages(team_name)


# ---------- Photo-proof verification ----------

async def ensure_photo_category(guild: discord.Guild):
    """Creates the private 'Photo Proofs' category once, reusing #admin's permissions so
    only organizers can see it. Safe to call repeatedly — no-ops if it already exists.

    Returns (category, error). `error` is None on success, or a short human-readable reason
    the category couldn't be created. Previously a Forbidden here was only printed to the
    console, so the organizer had no idea Photo Proofs silently never got created — now the
    caller surfaces this error directly."""
    category = discord.utils.get(guild.categories, name=PHOTO_CATEGORY_NAME)
    if category is not None:
        return category, None

    admin_channel = discord.utils.get(guild.text_channels, name=ADMIN_CHANNEL_NAME)
    overwrites = dict(admin_channel.overwrites) if admin_channel else {}
    overwrites[guild.default_role] = discord.PermissionOverwrite(view_channel=False)
    try:
        category = await guild.create_category(PHOTO_CATEGORY_NAME, overwrites=overwrites)
        return category, None
    except discord.Forbidden:
        return None, (
            "missing permissions — the bot's role needs **Manage Channels** and "
            "**Manage Roles** to create a private category with custom overwrites."
        )
    except discord.HTTPException as e:
        return None, str(e)


async def ensure_team_photo_channel(team_name: str, category, guild: discord.Guild):
    """Creates this team's channel under Photo Proofs if it doesn't exist yet. Called eagerly
    for every team at /start, so the full structure is visible from the start, not built
    piecemeal as teams happen to finish clues.

    Returns (channel, error), same pattern as ensure_photo_category."""
    if category is None:
        return None, "no Photo Proofs category available"
    channel_name = team_name.lower().replace(" ", "-") + "-photo"
    channel = discord.utils.get(category.text_channels, name=channel_name)
    if channel is not None:
        return channel, None
    try:
        channel = await guild.create_text_channel(channel_name, category=category)
        return channel, None
    except discord.Forbidden:
        return None, "missing permissions — the bot's role needs **Manage Channels**."
    except discord.HTTPException as e:
        return None, str(e)


async def mirror_photo_proof(team_name: str, guild: discord.Guild, location_id: str, file_bytes: bytes, filename: str):
    """Posts the team's photo into their Photo Proofs channel, tagged with the location."""
    category, cat_error = await ensure_photo_category(guild)
    if category is None:
        await warn_admin(f"⚠️ Couldn't archive {team_name}'s photo — {cat_error}")
        return
    channel, chan_error = await ensure_team_photo_channel(team_name, category, guild)
    if channel is None:
        await warn_admin(f"⚠️ Couldn't archive {team_name}'s photo — {chan_error}")
        return
    try:
        await channel.send(
            content=f"📸 **{team_name}** — location: `{location_id}`",
            file=discord.File(fp=io.BytesIO(file_bytes), filename=filename),
        )
    except (discord.Forbidden, discord.HTTPException) as e:
        print(f"[photo-proofs] Failed to post photo for {team_name}: {e}")


async def finalize_team_completion(team_name: str, channel: discord.abc.Messageable):
    """The actual 'you're done' sequence — writes Finished_At, cleans the channel, posts
    the completion message (no photo needed for the final step), and pings #admin."""
    now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    row_idx = client.team_row_cache.get(team_name)
    finished_col = col("Teams", "Finished_At", fallback=6)
    finish_write = asyncio.to_thread(teams_ws.update_cell, row_idx, finished_col, now) if row_idx else asyncio.sleep(0)

    await cleanup_finished_team_channel(team_name)
    completion_text = (
        "🔍 **YOU'VE CRACKED THE CIPHER!**\n\n"
        "Collect your item here, then run to the front of the mess block to complete the event! 🏃💨"
    )
    final_msg_task = channel.send(completion_text)
    await asyncio.gather(finish_write, final_msg_task)

    elapsed_str = "unknown"
    if client.hunt_started_at:
        try:
            started_dt = datetime.datetime.strptime(client.hunt_started_at, "%Y-%m-%d %H:%M:%S")
            finished_dt = datetime.datetime.strptime(now, "%Y-%m-%d %H:%M:%S")
            elapsed_str = format_duration((finished_dt - started_dt).total_seconds())
        except ValueError:
            pass
    await notify_admin_team_finished(team_name, elapsed_str, now)


async def post_clue_message(channel: discord.abc.Messageable, team_name: str, clue_text: str, heading: str = "📍 Your Clue"):
    """Posts a clue (text already resolved from cache — no Sheet read here) as a purple-
    accented embed, and remembers its ID so it can be deleted once solved."""
    embed = build_embed(f"**{clue_text}**", title=heading)
    msg = await channel.send(embed=embed)
    client.active_clue_messages[team_name] = (msg.channel.id, msg.id)
    return msg


async def show_wrong_code_message(team_name: str, channel: discord.abc.Messageable):
    """Sends a new message per wrong attempt (so the team can see their attempt history);
    all of them get wiped in one go once the clue is solved."""
    embed = build_wrong_embed("That code doesn't match your next location. Keep looking!", title="❌ Not Quite")
    msg = await channel.send(embed=embed)
    client.status_messages.setdefault(team_name, []).append((msg.channel.id, msg.id))


async def clear_wrong_code_messages(team_name: str):
    locations = client.status_messages.pop(team_name, [])
    for channel_id, message_id in locations:
        channel = client.get_channel(channel_id)
        if channel is None:
            continue
        try:
            msg = await channel.fetch_message(message_id)
            await msg.delete()
        except (discord.NotFound, discord.Forbidden):
            pass


def progress_text_from_cache(team_name: str) -> str:
    steps = client.route_cache.get(team_name, [])
    total = len(steps)
    solved = sum(1 for s in steps if s["solved"])
    return f"📊 **Progress:** {solved}/{total} clues solved"


async def update_team_progress_message(team_name: str, channel: discord.abc.Messageable):
    """Edits the persistent progress tracker (plain text) using the in-memory cache — no
    Sheet read. This message is created once (before the first clue is ever posted) and is
    always edited in place afterwards, so it naturally stays positioned above the clue,
    which gets deleted and re-posted fresh every time."""
    content = progress_text_from_cache(team_name)
    location = client.progress_messages.get(team_name)
    try:
        if location:
            ch = client.get_channel(location[0]) or channel
            msg = await ch.fetch_message(location[1])
            await msg.edit(content=content)
            return
    except (discord.NotFound, discord.Forbidden):
        pass
    msg = await channel.send(content)
    client.progress_messages[team_name] = (msg.channel.id, msg.id)


# ============================================================
# Admin-only permission check
# ============================================================

async def is_admin_user(interaction: discord.Interaction) -> bool:
    """True if this person can see the #admin channel — used as the 'organizer' check."""
    guild = interaction.guild
    if guild is None:
        return False
    admin_channel = discord.utils.get(guild.text_channels, name=ADMIN_CHANNEL_NAME)
    if admin_channel is None:
        return False
    member = interaction.user if isinstance(interaction.user, discord.Member) else guild.get_member(interaction.user.id)
    if member is None:
        return False
    return admin_channel.permissions_for(member).view_channel


async def require_admin_and_channel(interaction: discord.Interaction) -> bool:
    """Shared guard for organizer-only, #admin-only commands. Sends the rejection reply
    itself and returns False if the check fails, so callers can just `if not ...: return`."""
    if not await is_admin_user(interaction):
        await interaction.followup.send("🚫 This command is for organizers only.", ephemeral=True)
        return False
    if interaction.channel.name != ADMIN_CHANNEL_NAME:
        await interaction.followup.send(f"Run this command in #{ADMIN_CHANNEL_NAME}.", ephemeral=True)
        return False
    return True


# ============================================================
# /start — starts ALL teams at once, concurrently
# ============================================================

@client.tree.command(name="start", description="[Organizer only] Start the hunt for ALL teams at once. Run this once in #admin.")
async def start(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    if not await require_admin_and_channel(interaction):
        return

    already_started = get_setting("Hunt_Started_At")
    if already_started:
        await interaction.followup.send(
            f"⚠️ The hunt was already started at {already_started}. "
            f"Use /reset first if you want to restart it (this wipes all progress).",
            ephemeral=True,
        )
        return

    now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    # Refresh caches right before the real event starts, in case teams/clues changed since bot launch
    build_static_caches()
    build_route_cache()
    client.hunt_started_at = now
    client.hunt_ended = False

    # Create the Photo Proofs category ONCE up front (avoids a race where many teams'
    # concurrent tasks below all try to create it simultaneously), then every team's
    # channel gets created eagerly too, so the full structure is ready from the start
    # instead of only appearing piecemeal as teams happen to upload photos.
    photo_category, photo_cat_error = await ensure_photo_category(interaction.guild)
    photo_channel_errors = []

    async def start_one_team(team_name: str, channel_id: int):
        channel = client.get_channel(channel_id)
        if channel is None:
            return f"{team_name} (bot can't see that channel)"

        steps = client.route_cache.get(team_name, [])
        if not steps:
            return f"{team_name} (no route generated yet)"

        if photo_category is not None:
            _, chan_error = await ensure_team_photo_channel(team_name, photo_category, interaction.guild)
            if chan_error:
                photo_channel_errors.append(f"{team_name}: {chan_error}")

        await delete_tracked_message(client.announce_messages, team_name)
        await delete_active_clue_message(team_name)
        header_text = (
            "🔴 **HUNT IS LIVE**\n\n"
            "The hunt has officially begun — your first clue is right below!"
        )
        header_msg = await channel.send(header_text)
        client.live_header_messages[team_name] = (header_msg.channel.id, header_msg.id)

        # Progress is created (and always edited in place after this) BEFORE the clue is
        # first posted, so it naturally stays positioned above the clue in the channel.
        await update_team_progress_message(team_name, channel)

        location_id = steps[0]["location_id"]
        clue_text = client.config_cache.get(location_id, {}).get("clue_text", "(clue not found)")
        await post_clue_message(channel, team_name, clue_text)
        return None

    tasks_list = [
        start_one_team(team_name, ch_id)
        for ch_id, team_name in client.channel_team_cache.items()
    ]
    results = await asyncio.gather(*tasks_list)
    skipped = [r for r in results if r]
    started_count = len(results) - len(skipped)

    set_setting("Hunt_Started_At", now)
    all_teams_values = teams_ws.get_all_values()
    num_team_rows = len(all_teams_values) - 1
    if num_team_rows > 0:
        started_letter = gspread.utils.rowcol_to_a1(1, col("Teams", "Started_At", fallback=5)).rstrip("1")
        teams_ws.update(f"{started_letter}2:{started_letter}{1 + num_team_rows}", [[now] for _ in range(num_team_rows)])

    summary = f"✅ Hunt started for {started_count} team(s) at {now}."
    if photo_cat_error:
        summary += f"\n🚫 Photo Proofs category couldn't be created — {photo_cat_error}"
    if photo_channel_errors:
        summary += "\n🚫 Some Photo Proofs channels failed:\n" + "\n".join(photo_channel_errors[:10])
    if skipped:
        summary += "\n⚠️ Skipped: " + ", ".join(skipped)
    await interaction.followup.send(summary, ephemeral=True)


# ============================================================
# /reset — full wipe: Sheet data, Results tab, every channel, all caches
# ============================================================

@client.tree.command(name="reset", description="[Organizer only] Wipe everything (Sheet progress, Results tab, all channels). For testing.")
async def reset(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    if not await require_admin_and_channel(interaction):
        return

    # Fetch row counts concurrently (needed to build the write ranges below)
    all_routes, all_teams = await asyncio.gather(
        asyncio.to_thread(routes_ws.get_all_values),
        asyncio.to_thread(teams_ws.get_all_values),
    )
    num_route_rows = len(all_routes) - 1
    num_team_rows = len(all_teams) - 1

    def fill_column(ws, header_name: str, fallback_col: int, value, num_rows: int):
        """Writes `value` down a single named column for `num_rows` rows starting at row 2.
        Resolved by header name (not assumed adjacency to other columns), so it's safe even
        if the reset columns aren't next to each other after a reorder."""
        letter = gspread.utils.rowcol_to_a1(1, col(ws.title, header_name, fallback=fallback_col)).rstrip("1")
        ws.update(f"{letter}2:{letter}{1 + num_rows}", [[value] for _ in range(num_rows)])

    async def do_sheet_writes():
        write_tasks = []
        if num_route_rows > 0:
            write_tasks.append(asyncio.to_thread(fill_column, routes_ws, "Solved", 4, "N", num_route_rows))
            write_tasks.append(asyncio.to_thread(fill_column, routes_ws, "Solved_At", 5, "", num_route_rows))
        if num_team_rows > 0:
            write_tasks.append(asyncio.to_thread(fill_column, teams_ws, "Current_Position", 4, 0, num_team_rows))
            write_tasks.append(asyncio.to_thread(fill_column, teams_ws, "Started_At", 5, "", num_team_rows))
            write_tasks.append(asyncio.to_thread(fill_column, teams_ws, "Finished_At", 6, "", num_team_rows))
        write_tasks.append(asyncio.to_thread(set_setting, "Hunt_Started_At", ""))
        write_tasks.append(asyncio.to_thread(set_setting, "Hunt_Ended_At", ""))
        write_tasks.append(asyncio.to_thread(clear_results_ws))
        await asyncio.gather(*write_tasks)

    team_channel_ids = list(client.channel_team_cache.keys())
    admin_channel = discord.utils.get(interaction.guild.text_channels, name=ADMIN_CHANNEL_NAME)
    standings_channel = discord.utils.get(interaction.guild.text_channels, name=STANDINGS_CHANNEL_NAME)

    async def purge_channel(ch):
        if ch is None:
            return
        try:
            await ch.purge(limit=1000)
        except (discord.Forbidden, discord.HTTPException):
            pass

    async def do_purges():
        purge_tasks = [purge_channel(client.get_channel(cid)) for cid in team_channel_ids]
        purge_tasks.append(purge_channel(standings_channel))
        photo_category = discord.utils.get(interaction.guild.categories, name=PHOTO_CATEGORY_NAME)
        if photo_category is not None:
            purge_tasks.extend(purge_channel(ch) for ch in photo_category.text_channels)
        await asyncio.gather(*purge_tasks)

    # Sheet writes and channel purges are independent of each other — run them
    # at the same time instead of one after the other.
    await asyncio.gather(do_sheet_writes(), do_purges())

    client.hunt_started_at = None
    client.hunt_ended = False

    # Refresh caches (in case teams/channels changed) and rebuild routes fresh from the Sheet
    build_static_caches()
    build_route_cache()

    client.active_clue_messages.clear()
    client.progress_messages.clear()
    client.status_messages.clear()
    client.announce_messages.clear()
    client.live_header_messages.clear()
    client.team_locks.clear()
    client.awaiting_photo.clear()
    client.photo_prompt_messages.clear()
    client.photo_sent_messages.clear()
    client.leaderboard_message_id = None
    client.dashboard_message_id = None
    client.heartbeat_message_id = None

    # #admin is purged LAST (after everything above is confirmed done), then the command
    # guide is re-posted and the confirmation sent, so neither gets wiped by its own purge.
    if admin_channel is not None:
        try:
            await admin_channel.purge(limit=1000)
        except (discord.Forbidden, discord.HTTPException):
            pass
        await ensure_admin_command_guide()
        await admin_channel.send("Reset done.")

    try:
        await interaction.delete_original_response()
    except discord.NotFound:
        pass


# ============================================================
# /end — freeze scanning, notify every team concurrently, snapshot Results
# ============================================================

@client.tree.command(name="end", description="[Organizer only] End the hunt: freeze scanning and send each team their final results.")
async def end(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    if not await require_admin_and_channel(interaction):
        return

    already_ended = get_setting("Hunt_Ended_At")
    if already_ended:
        await interaction.followup.send(f"⚠️ The hunt was already ended at {already_ended}.", ephemeral=True)
        return

    now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    set_setting("Hunt_Ended_At", now)
    client.hunt_ended = True

    build_static_caches()  # refresh channel mapping before notifying every team
    status = get_full_team_status()  # sorted, most clues solved first
    write_results_snapshot(status, now)

    # Backup case: nobody reached the shared final location before time ran out.
    # /end already ranks by partial progress regardless, but this adds explicit
    # messaging so it's clear rankings are based on partial progress, not a bug.
    none_finished = bool(status) and not any("(finished)" in s["elapsed"] for s in status)

    async def notify_one_team(s):
        ch_id = team_channel_id(s["team"])
        if not ch_id:
            return
        channel = client.get_channel(ch_id)
        if channel is None:
            return
        await cleanup_finished_team_channel(s["team"])  # remove "HUNT IS LIVE" header + any leftover clue
        text = (
            f"🏁 **HUNT ENDED**\n\n"
            f"Your team solved **{s['solved']}/{s['total']}** clues.\n"
            f"⏱ Time: {s['elapsed']}\n\n"
            f"Thanks for participating! 🎉"
        )
        if none_finished:
            text += (
                "\n\n_No team reached the final location before time ran out — "
                "final rankings are based on clues solved and time taken._"
            )
        await channel.send(text)

    # Dispatched together instead of one-by-one, same fairness fix as /start and /announce
    await asyncio.gather(*(notify_one_team(s) for s in status))

    summary_lines = [f"🏁 **Hunt ended at {now}.** Final results (also saved to the Results sheet tab):"]
    if none_finished:
        summary_lines.append(
            "⚠️ No team fully finished — rankings below are based on partial progress (clues solved, then time)."
        )
    summary_lines.append("")
    for rank, s in enumerate(status, start=1):
        summary_lines.append(f"{rank}. **{s['team']}** — {s['solved']}/{s['total']} clues, {s['elapsed']}")
    await interaction.followup.send("\n".join(summary_lines), ephemeral=True)


# ============================================================
# /announce — pre-hunt heads-up, concurrent, auto-removed by /start
# ============================================================

@client.tree.command(name="announce", description="[Organizer only] Send all teams a heads-up that the hunt is starting soon. Run in #admin.")
async def announce(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    if not await require_admin_and_channel(interaction):
        return

    announce_text = (
        "📢 **Heads Up!**\n\n"
        "The hunt will be starting shortly.\n"
        f"If you have any confusion about how it works, check out #{HOW_TO_PLAY_CHANNEL_NAME} for the rules and commands.\n"
        "Good luck! 🍀"
    )

    build_static_caches()  # refresh in case teams/channels changed since the bot started

    async def announce_one_team(team_name: str, channel_id: int):
        channel = client.get_channel(channel_id)
        if channel is None:
            return None
        sent = await channel.send(announce_text)
        client.announce_messages[team_name] = (sent.channel.id, sent.id)
        return team_name

    results = await asyncio.gather(*(
        announce_one_team(team_name, ch_id) for ch_id, team_name in client.channel_team_cache.items()
    ))
    notified = [r for r in results if r]

    summary = f"📢 Announcement sent to {len(notified)} team(s)."
    await interaction.followup.send(summary, ephemeral=True)


# ============================================================
# /setup_teams — creates/updates private team channels from the Registrations
# tab (fed by the sign-up Google Form) and grants access to each member's
# Discord ID. Safe to re-run: existing channels are updated, not duplicated.
# ============================================================

@client.tree.command(
    name="setup_teams",
    description="[Organizer only] Create private team channels from Registrations, add members by Discord ID.",
)
async def setup_teams(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    if not await require_admin_and_channel(interaction):
        return

    teams, bad_rows = get_team_registrations()
    if not teams:
        text = "⚠️ No usable rows found in the Registrations tab."
        if bad_rows:
            text += "\n" + "\n".join(bad_rows[:15])
        await interaction.followup.send(text, ephemeral=True)
        return

    category, cat_error = await ensure_team_category(interaction.guild)
    if category is None:
        await interaction.followup.send(
            f"🚫 Couldn't create/find the '{TEAM_CATEGORY_NAME}' category — {cat_error}",
            ephemeral=True,
        )
        return

    lines = [f"📋 Processed {len(teams)} team(s) from Registrations:"]
    for team_name, member_ids in teams.items():
        channel, found_members, missing_ids, error = await create_or_update_team_channel(
            interaction.guild, category, team_name, member_ids
        )
        if error:
            lines.append(f"🚫 **{team_name}** — failed: {error}")
            continue
        upsert_team_channel_id(team_name, channel.id)
        member_summary = ", ".join(m.display_name for m in found_members) if found_members else "no members found"
        lines.append(f"✅ **{team_name}** → #{channel.name} — added: {member_summary}")
        if missing_ids:
            lines.append(f"   ⚠️ Discord ID(s) not found in this server: {', '.join(str(i) for i in missing_ids)}")

    build_static_caches()  # so /scan works in the new channels immediately, no restart needed

    if bad_rows:
        lines.append("\n⚠️ Some registration rows were skipped:")
        lines.extend(bad_rows[:15])

    text = "\n".join(lines)
    if len(text) > 1900:
        text = text[:1900] + "\n… (truncated — check the Registrations tab for the rest)"
    await interaction.followup.send(text, ephemeral=True)


# ============================================================
# /commands — lists organizer commands
# ============================================================

@client.tree.command(name="commands", description="[Organizer only] List all organizer commands.")
async def commands_list(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    if not await require_admin_and_channel(interaction):
        return

    text = (
        "🛠️ **Organizer Commands**\n\n"
        "`/setup_teams` — create/update private team channels from Registrations, add members by Discord ID\n"
        "`/announce` — send every team a pre-hunt heads-up (auto-removed when /start runs)\n"
        "`/start` — start the hunt for ALL teams at once (one-time; use /reset to redo)\n"
        "`/end` — freeze scanning, send final results to every team, snapshot standings\n"
        "`/reset` — wipe all progress + clear every channel, for testing\n"
        "`/commands` — show this list\n\n"
        "All of these only work in #admin, and only for people who can see #admin."
    )
    await interaction.followup.send(text, ephemeral=True)


# ============================================================
# /scan — the hot path. Cache-only lookups; the one necessary Sheet
# write runs in a background thread concurrently with the Discord replies.
# ============================================================

@client.tree.command(name="scan", description="Submit a code found at a location to unlock your next clue.")
@app_commands.describe(code="The code shown on the QR code you scanned")
async def scan(interaction: discord.Interaction, code: str):
    await interaction.response.defer(ephemeral=True)

    if client.hunt_ended:
        await interaction.followup.send("🚫 The hunt has ended. Scanning is no longer accepted.", ephemeral=True)
        return

    team_name = client.channel_team_cache.get(interaction.channel_id)
    if not team_name:
        await interaction.followup.send(
            "This channel isn't linked to a team yet, or the hunt hasn't been started. "
            "Ask the organizer.",
            ephemeral=True,
        )
        return

    async with get_team_lock(team_name):
        steps = client.route_cache.get(team_name)
        if not steps:
            await interaction.followup.send("No route found for your team yet. Ask the organizer.", ephemeral=True)
            return

        next_idx = next((i for i, s in enumerate(steps) if not s["solved"]), None)
        if next_idx is None:
            await interaction.followup.send(f"🏁 {team_name}, you've already completed all your clues! Great work.", ephemeral=True)
            return

        step = steps[next_idx]
        location_id = step["location_id"]
        expected_qr = client.config_cache.get(location_id, {}).get("qr_value", "")
        submitted = code.strip()

        if expected_qr and submitted.upper() == expected_qr.upper():
            # Update the in-memory cache immediately — this is what makes progress instant
            step["solved"] = True
            now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            is_finished = (next_idx + 1) >= len(steps)

            # The Sheet write is the only slow, blocking part — run it in a worker thread so
            # it happens IN PARALLEL with the Discord messages below, not before them.
            solved_col = col("Team_Routes", "Solved", fallback=4)
            solved_at_col = col("Team_Routes", "Solved_At", fallback=5)
            sheet_write = asyncio.to_thread(
                routes_ws.batch_update,
                [
                    {"range": gspread.utils.rowcol_to_a1(step["row_index"], solved_col), "values": [["Y"]]},
                    {"range": gspread.utils.rowcol_to_a1(step["row_index"], solved_at_col), "values": [[now]]},
                ],
            )

            # IMPORTANT: the old clue message must be fully deleted BEFORE anything else —
            # it both reads/writes the same active_clue_messages[team_name] tracker entry as
            # other operations, so running them concurrently can race. Delete first, sequentially.
            await delete_active_clue_message(team_name)

            if is_finished:
                # Final clue: no photo needed — they'll get a physical item in person instead.
                await finalize_team_completion(team_name, interaction.channel)
                await sheet_write
                await clear_wrong_code_messages(team_name)
            else:
                # Every OTHER clue requires a group photo at that location before the next
                # one unlocks — remember what's next so on_message can pick up where this left off.
                client.awaiting_photo[team_name] = {
                    "location_id": location_id,
                    "next_idx": next_idx + 1,
                    "is_finished": False,
                }
                prompt_embed = build_correct_embed(
                    "Take a group photo with your team here, then upload it right in this "
                    "channel to unlock your next clue.",
                    title="✅ Correct!",
                )
                prompt_task = interaction.channel.send(embed=prompt_embed)
                sheet_write_result, _, prompt_msg = await asyncio.gather(
                    sheet_write, clear_wrong_code_messages(team_name), prompt_task
                )
                client.photo_prompt_messages[team_name] = (prompt_msg.channel.id, prompt_msg.id)
        else:
            await show_wrong_code_message(team_name, interaction.channel)

    try:
        await interaction.delete_original_response()
    except discord.NotFound:
        pass


# ============================================================
# Leaderboard auto-update loop (#leaderboard) — Top 5 only, silent
# ============================================================

@tasks.loop(seconds=30)
async def update_leaderboard():
    try:
        refresh_val = get_setting("Leaderboard_Refresh_Seconds")  # looked up by Key, not a fixed cell
        if refresh_val and update_leaderboard.seconds != int(refresh_val):
            update_leaderboard.change_interval(seconds=int(refresh_val))
    except Exception:
        pass

    channel = discord.utils.get(client.get_all_channels(), name=LEADERBOARD_CHANNEL_NAME)
    if channel is None:
        return

    top5 = get_top5()
    if not top5:
        body = "No progress yet."
    else:
        lines = []
        medals = ["🥇", "🥈", "🥉", "4️⃣", "5️⃣"]
        for i, (team, count) in enumerate(top5):
            lines.append(f"{medals[i]} **{team}** — {count} clues solved")
        body = "\n".join(lines)
    content = (
        f"🏆 **Top 5 Leaderboard**\n\n{body}\n\n"
        f"_Last updated: {datetime.datetime.now().strftime('%H:%M:%S')}_"
    )

    try:
        if client.leaderboard_message_id:
            msg = await channel.fetch_message(client.leaderboard_message_id)
            await msg.edit(content=content)
        else:
            async for m in channel.history(limit=20):
                if m.author == client.user:
                    client.leaderboard_message_id = m.id
                    await m.edit(content=content)
                    return
            new_msg = await channel.send(content)
            client.leaderboard_message_id = new_msg.id
    except discord.NotFound:
        new_msg = await channel.send(content)
        client.leaderboard_message_id = new_msg.id


# ============================================================
# Standings channel: PURE periodic dashboard table, nothing else
# ============================================================

async def get_standings_channel():
    guild = client.guilds[0] if client.guilds else None
    if guild is None:
        return None
    channel = discord.utils.get(guild.text_channels, name=STANDINGS_CHANNEL_NAME)
    if channel is None:
        channel = await guild.create_text_channel(STANDINGS_CHANNEL_NAME)
    return channel


async def get_admin_channel():
    guild = client.guilds[0] if client.guilds else None
    if guild is None:
        return None
    channel = discord.utils.get(guild.text_channels, name=ADMIN_CHANNEL_NAME)
    if channel is None:
        channel = await guild.create_text_channel(ADMIN_CHANNEL_NAME)
    return channel


async def warn_admin(text: str):
    """Best-effort: posts a warning in #admin so failures are visible to the organizer
    instead of only ending up in the console (which nobody's watching during the event)."""
    channel = await get_admin_channel()
    if channel is None:
        print(f"[warn_admin] {text}")
        return
    try:
        await channel.send(text)
    except (discord.Forbidden, discord.HTTPException):
        print(f"[warn_admin] {text}")


async def notify_admin_team_finished(team_name: str, elapsed_str: str, finish_time: str):
    """Finish pings go to #admin (not #team-standings), which stays a clean, pure table."""
    channel = await get_admin_channel()
    if channel is None:
        return
    text = f"🏁 **{team_name} Finished!**\nTotal time: **{elapsed_str}** (at {finish_time})"
    await channel.send(text)


@tasks.loop(seconds=30)
async def update_admin_dashboard():
    channel = discord.utils.get(client.get_all_channels(), name=STANDINGS_CHANNEL_NAME)
    if channel is None:
        return

    status = get_full_team_status()
    if not status:
        body = "No teams found."
    else:
        lines = []
        for s in status:
            lines.append(
                f"**{s['team']}** — {s['solved']}/{s['total']} clues | "
                f"⏱ {s['elapsed']} | last activity: {s['last_activity']}"
            )
        body = "\n".join(lines)
    content = (
        f"📊 **Team Standings — Full Status**\n\n{body}\n\n"
        f"_Last updated: {datetime.datetime.now().strftime('%H:%M:%S')}_"
    )

    try:
        if client.dashboard_message_id:
            msg = await channel.fetch_message(client.dashboard_message_id)
            await msg.edit(content=content)
        else:
            async for m in channel.history(limit=50):
                if m.author == client.user and m.content.startswith("📊 **Team Standings"):
                    client.dashboard_message_id = m.id
                    await m.edit(content=content)
                    return
            new_msg = await channel.send(content)
            client.dashboard_message_id = new_msg.id
    except discord.NotFound:
        new_msg = await channel.send(content)
        client.dashboard_message_id = new_msg.id


# ============================================================
# Heartbeat loop (#admin) — single message, edited in place
# ============================================================

@tasks.loop(minutes=HEARTBEAT_INTERVAL_MINUTES)
async def heartbeat():
    guild = client.guilds[0] if client.guilds else None
    if guild is None:
        return

    channel = discord.utils.get(guild.text_channels, name=ADMIN_CHANNEL_NAME)
    if channel is None:
        channel = await guild.create_text_channel(ADMIN_CHANNEL_NAME)

    now = datetime.datetime.now().strftime("%H:%M:%S")
    content = f"✅ Bot still running — last check: {now}"

    try:
        if client.heartbeat_message_id:
            msg = await channel.fetch_message(client.heartbeat_message_id)
            await msg.edit(content=content)
            return
        async for m in channel.history(limit=50):
            if m.author == client.user and m.content.startswith("✅ Bot still running"):
                client.heartbeat_message_id = m.id
                await m.edit(content=content)
                return
        new_msg = await channel.send(content)
        client.heartbeat_message_id = new_msg.id
    except discord.NotFound:
        new_msg = await channel.send(content)
        client.heartbeat_message_id = new_msg.id


# ============================================================
# How-to-play channel (auto-created/refreshed under "Information" category)
# ============================================================

HOW_TO_PLAY_TEXT = (
    "📜 **How to Play — Cipher**\n\n"
    "1️⃣ Once the organizer starts the hunt, your team will get its first clue posted right here in your private team channel.\n"
    "2️⃣ Solve the riddle to figure out which location on campus it's pointing to.\n"
    "3️⃣ Go there and find the hidden QR code. Scan it with your phone's normal camera app.\n"
    "4️⃣ In your team channel, type `/scan` and paste the code shown, then send it.\n"
    "5️⃣ If it's correct, take a group photo with your team at that spot and upload it right here — that's what unlocks your next clue. Keep going until you've solved them all!\n"
    "6️⃣ Your final clue leads everyone to the same finish line — no photo needed there. Scan it, and you'll get an item to carry as you run to the front of the mess block to complete Cipher!\n\n"
    "**Commands you can use:**\n"
    "`/scan <code>` — submit the code you found to unlock your next clue\n\n"
    "Good luck, and have fun! 🏆"
)


async def ensure_how_to_play_channel():
    guild = client.guilds[0] if client.guilds else None
    if guild is None:
        return

    category = discord.utils.find(
        lambda c: c.name.strip().lower() == HOW_TO_PLAY_CATEGORY_NAME.lower(),
        guild.categories,
    )

    channel = discord.utils.get(guild.text_channels, name=HOW_TO_PLAY_CHANNEL_NAME)
    if channel is None:
        channel = await guild.create_text_channel(HOW_TO_PLAY_CHANNEL_NAME, category=category)
    elif category is not None and channel.category_id != category.id:
        await channel.edit(category=category)

    async for m in channel.history(limit=20):
        if m.author == client.user:
            if m.content != HOW_TO_PLAY_TEXT:
                await m.edit(content=HOW_TO_PLAY_TEXT)
            return
    await channel.send(HOW_TO_PLAY_TEXT)


# ============================================================
# Persistent organizer command guide, pinned at the top of #admin
# ============================================================

ADMIN_GUIDE_TEXT = (
    "🛠️ **Organizer Command Guide** (pinned reference)\n\n"
    "`/setup_teams` — create/update private team channels from Registrations, add members by Discord ID\n"
    "`/announce` — pre-hunt heads-up to every team (auto-removed when /start runs)\n"
    "`/start` — start the hunt for ALL teams at once, one-time (use /reset to redo)\n"
    "`/end` — freeze scanning, send final results to every team, snapshot standings\n"
    "`/reset` — wipe everything: Sheet progress, Results tab, and every channel — for testing\n"
    "`/commands` — show this list again on demand\n\n"
    "All commands only work here in #admin, and only for people who can see this channel."
)


async def ensure_admin_command_guide():
    channel = await get_admin_channel()
    if channel is None:
        return
    async for m in channel.history(limit=20):
        if m.author == client.user and m.content.startswith("🛠️"):
            if m.content != ADMIN_GUIDE_TEXT:
                await m.edit(content=ADMIN_GUIDE_TEXT)
            return
    msg = await channel.send(ADMIN_GUIDE_TEXT)
    try:
        await msg.pin()
    except (discord.Forbidden, discord.HTTPException):
        pass


# ============================================================
# Photo submission listener — detects a team's finish-line selfie
# ============================================================

# ============================================================
# Photo submission listener — every clue requires a group photo
# before the next one unlocks (or the hunt completes, on the last one)
# ============================================================

@client.event
async def on_message(message: discord.Message):
    if message.author == client.user or message.guild is None:
        return
    if not message.attachments:
        return

    team_name = client.channel_team_cache.get(message.channel.id)
    if not team_name or team_name not in client.awaiting_photo:
        return

    image_attachment = next(
        (a for a in message.attachments if a.content_type and a.content_type.startswith("image/")),
        None,
    )
    if image_attachment is None:
        return

    pending = client.awaiting_photo.pop(team_name)
    location_id = pending["location_id"]
    file_bytes = await image_attachment.read()

    # Delete the "upload a photo" prompt and the photo itself ("cut" it from the team
    # channel), archive it in Photo Proofs, then confirm with a short message.
    await delete_tracked_message(client.photo_prompt_messages, team_name)
    try:
        await message.delete()
    except (discord.Forbidden, discord.HTTPException):
        pass

    await mirror_photo_proof(team_name, message.guild, location_id, file_bytes, image_attachment.filename)

    # Only ever show the LATEST "Photo is sent." confirmation — delete the previous one
    # (if any) before sending the new one, instead of letting them stack up.
    await delete_tracked_message(client.photo_sent_messages, team_name)
    sent_msg = await message.channel.send("📸 Photo is sent.")
    client.photo_sent_messages[team_name] = (sent_msg.channel.id, sent_msg.id)

    steps = client.route_cache.get(team_name, [])
    next_idx = pending["next_idx"]
    if next_idx < len(steps):
        next_location_id = steps[next_idx]["location_id"]
        next_clue_text = client.config_cache.get(next_location_id, {}).get("clue_text", "(clue not found)")
        # Update progress first (it's an in-place edit, so this doesn't move it), then post
        # the new clue — keeps progress visually above the clue.
        await update_team_progress_message(team_name, message.channel)
        await post_clue_message(message.channel, team_name, next_clue_text)


# ============================================================
# Startup
# ============================================================

@client.event
async def on_ready():
    print(f"Logged in as {client.user}")

    # Build caches once at startup so they're ready even before /start is run
    # (e.g. so /scan doesn't crash if someone tests early — it'll just say "no route yet").
    build_static_caches()
    build_route_cache()
    client.hunt_started_at = get_setting("Hunt_Started_At") or None
    client.hunt_ended = bool(get_setting("Hunt_Ended_At"))

    await ensure_how_to_play_channel()
    await ensure_admin_command_guide()
    await get_standings_channel()

    if not update_leaderboard.is_running():
        update_leaderboard.start()
    if not update_admin_dashboard.is_running():
        update_admin_dashboard.start()
    if not heartbeat.is_running():
        heartbeat.start()


client.run(BOT_TOKEN)

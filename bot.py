"""
Discord Bot for Polandball Availability
======================================

Commands (slash commands: /)
----------------------------
1) /available ball
   → Replies with a comma-separated list of all available balls from your Google Sheet.

2) /available character: "Country X"
   → Replies with sprite/splash availability for that character.

3) /ping
   → Replies with pong.

4) /artist name: "Artist Name" (optional: kind = splash / sprite / both)
   → Shows all characters whose sprite or splash art was created by the specified artist.


Quick Start
-----------
1) Python 3.10+
2) pip install -r requirements.txt
3) Put your Discord bot token in the DISCORD_TOKEN env var.
4) On Cloud Run, attach a service account with Sheets+Drive read access.
5) Share your Google Sheet with that service account email.
6) Set these env vars:
   - GOOGLE_SHEET_ID = the Sheet ID from its URL
   - SHEET_NAME = the tab name (default: "Characters")
   - AVAILABLE_VALUES = comma-separated values considered available (default: "y")
   - UNAVAILABLE_VALUES = comma-separated values considered unavailable (default: "n")

Sheet layout (first row is headers):
------------------------------------
A: In Game?                         (Y/N or empty)
B: Character                        (name used by the bot)
C: Splash Art Artist (Primary)
D: Rdy (for Splash)                 (Y/N or empty)
E: Sprite Art Artist (Primary)
F: Rdy (for Sprite)                 (Y/N or empty)
G: Splash Art Artist (Alternate)
H: Sprite Art Artist (Alternate)
"""

from __future__ import annotations
import asyncio
import difflib
import json
import logging
import os
import re
import time
import unicodedata
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple
from enum import Enum


import discord
from discord.ext import commands
from discord import app_commands

import gspread
from google.oauth2.service_account import Credentials
from google.auth import default as google_auth_default

import tempfile
import uuid

from googleapiclient.discovery import build
from googleapiclient.http import MediaFileUpload

from PIL import Image

# For local test only
from dotenv import load_dotenv
load_dotenv()


DISCORD_TOKEN = os.getenv("DISCORD_TOKEN")
GOOGLE_SHEET_ID = os.getenv("GOOGLE_SHEET_ID")
SHEET_NAME = os.getenv("SHEET_NAME", "Characters")
GOOGLE_SHEET_URL = os.getenv(
    "GOOGLE_SHEET_URL",
    "https://docs.google.com/spreadsheets/d/1Sud0s7EbgAfBCHR7w21OmnYF-VcG64O8WGM1ixYoRz0/edit?gid=0#gid=0",
)
AVAILABLE_VALUES = set(
    v.strip().lower()
    for v in os.getenv("AVAILABLE_VALUES", "y").split(",")
    if v.strip()
)
UNAVAILABLE_VALUES = set(
    v.strip().lower()
    for v in os.getenv("UNAVAILABLE_VALUES", "n").split(",")
    if v.strip()
)

ART_ROOT_FOLDER_ID = "1683upwuV6g3zIamCaY4o1lhtfFDIJHMG"
CACHE_TTL_SECS = int(os.getenv("CACHE_TTL_SECS", "60"))

SERVICE_ACCOUNT_JSON = os.getenv("SERVICE_ACCOUNT_JSON")
SERVICE_ACCOUNT_FILE = os.getenv("SERVICE_ACCOUNT_FILE", "service_account.json")

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("polandball-bot")


@dataclass
class CountryRecord:
    country: str
    in_game: str
    splash_artist: str
    splash_rdy: str
    sprite_artist: str
    sprite_rdy: str

    def _parse(self, raw: str) -> Optional[bool]:
        if not raw:
            return True  # Empty = available
        s = raw.strip().lower()
        if s in AVAILABLE_VALUES:
            return True
        if s in UNAVAILABLE_VALUES:
            return False
        return False  # Any non-empty value (if not in AVAILABLE_VALUES) = unavailable

    def in_game_status(self) -> Optional[bool]:
        """Return True/False/None for the 'In Game?' column.

        - Returns True if the cell matches `AVAILABLE_VALUES`.
        - Returns False if it matches `UNAVAILABLE_VALUES`.
        - Returns None if empty or unknown.
        """
        raw = self.in_game
        if not raw:
            return None
        s = raw.strip().lower()
        if s in AVAILABLE_VALUES:
            return True
        if s in UNAVAILABLE_VALUES:
            return False
        return None

    def is_available(self, kind: str) -> Optional[bool]:
        if kind == "splash":
            return self._parse(self.splash_artist)
        if kind == "sprite":
            return self._parse(self.sprite_artist)
        return None


class SheetClient:
    def __init__(self):
        scopes = [
            "https://www.googleapis.com/auth/spreadsheets.readonly",
            "https://www.googleapis.com/auth/drive.readonly",
        ]

        if SERVICE_ACCOUNT_JSON:
            info = json.loads(SERVICE_ACCOUNT_JSON)
            creds = Credentials.from_service_account_info(info, scopes=scopes)
        elif SERVICE_ACCOUNT_FILE and os.path.exists(SERVICE_ACCOUNT_FILE):
            creds = Credentials.from_service_account_file(SERVICE_ACCOUNT_FILE, scopes=scopes)
        else:
            creds, _ = google_auth_default(scopes=scopes)

        self.gc = gspread.authorize(creds)
        if not GOOGLE_SHEET_ID:
            raise RuntimeError("GOOGLE_SHEET_ID env var is required.")
        self.sheet = self.gc.open_by_key(GOOGLE_SHEET_ID).worksheet(SHEET_NAME)
        logger.info("Connected to Google Sheet '%s' tab '%s'", GOOGLE_SHEET_ID, SHEET_NAME)

    def fetch_records(self) -> List[CountryRecord]:
        values = self.sheet.get_all_values()

        def col_letter_to_index(letter: str):
            letter = (letter or "").strip()
            if not letter or not letter.isalpha():
                return None
            idx = 0
            for ch in letter.upper():
                idx = idx * 26 + (ord(ch) - 64)
            return idx - 1

        in_game_i = col_letter_to_index("A")
        character_i = col_letter_to_index("B")
        splash_artist_i = col_letter_to_index("C")
        splash_rdy_i = col_letter_to_index("D")
        sprite_artist_i = col_letter_to_index("E")
        sprite_rdy_i = col_letter_to_index("F")

        records: List[CountryRecord] = []

        for row in values[1:]:
            in_game = (
                row[in_game_i].strip()
                if in_game_i is not None and in_game_i < len(row)
                else ""
            )

            country = (
                row[character_i].strip()
                if character_i is not None and character_i < len(row)
                else ""
            )
            splash_artist = (
                row[splash_artist_i].strip()
                if splash_artist_i is not None and splash_artist_i < len(row)
                else ""
            )
            splash_rdy = (
                row[splash_rdy_i].strip()
                if splash_rdy_i is not None and splash_rdy_i < len(row)
                else ""
            )
            sprite_artist = (
                row[sprite_artist_i].strip()
                if sprite_artist_i is not None and sprite_artist_i < len(row)
                else ""
            )
            sprite_rdy = (
                row[sprite_rdy_i].strip()
                if sprite_rdy_i is not None and sprite_rdy_i < len(row)
                else ""
            )

            if country:
                records.append(
                    CountryRecord(
                        country=country,
                        in_game=in_game,
                        splash_artist=splash_artist,
                        splash_rdy=splash_rdy,
                        sprite_artist=sprite_artist,
                        sprite_rdy=sprite_rdy,
                    )
                )
        return records


class Cache:
    def __init__(self, ttl: int):
        self.ttl = ttl
        self._data: Optional[Tuple[float, List[CountryRecord]]] = None

    def get(self) -> Optional[List[CountryRecord]]:
        if not self._data:
            return None
        ts, data = self._data
        if time.time() - ts > self.ttl:
            return None
        return data

    def set(self, data: List[CountryRecord]):
        self._data = (time.time(), data)


_STOPWORDS = {"ball"}
_WORDS_RE = re.compile(r"[\w']+")


def normalize_country(text: str) -> str:
    words = [w.lower() for w in _WORDS_RE.findall(text)]
    words = [w for w in words if w not in _STOPWORDS]
    return " ".join(words)

def create_drive_service():
    """
    Create a Google Drive API client using the same credential logic as SheetClient,
    but with write access (drive.file).
    """
    scopes = ["https://www.googleapis.com/auth/drive.file"]

    if SERVICE_ACCOUNT_JSON:
        info = json.loads(SERVICE_ACCOUNT_JSON)
        creds = Credentials.from_service_account_info(info, scopes=scopes)
    elif SERVICE_ACCOUNT_FILE and os.path.exists(SERVICE_ACCOUNT_FILE):
        creds = Credentials.from_service_account_file(SERVICE_ACCOUNT_FILE, scopes=scopes)
    else:
        creds, _ = google_auth_default(scopes=scopes)

    return build("drive", "v3", credentials=creds)


def get_or_create_folder(service, name: str, parent_id: Optional[str] = None) -> str:
    """
    Find or create a folder in Google Drive or a Shared Drive.

    If parent_id is a folder inside a Shared Drive, everything stays under that.
    """
    if parent_id:
        q = (
            "mimeType='application/vnd.google-apps.folder' "
            f"and name='{name}' and '{parent_id}' in parents and trashed=false"
        )
    else:
        q = (
            "mimeType='application/vnd.google-apps.folder' "
            f"and name='{name}' and trashed=false"
        )

    result = service.files().list(
        q=q,
        spaces="drive",
        fields="files(id, name)",
        pageSize=1,
        supportsAllDrives=True,
        includeItemsFromAllDrives=True,
    ).execute()

    files = result.get("files", [])
    if files:
        return files[0]["id"]

    metadata = {
        "name": name,
        "mimeType": "application/vnd.google-apps.folder",
    }
    if parent_id:
        metadata["parents"] = [parent_id]

    folder = service.files().create(
        body=metadata,
        fields="id",
        supportsAllDrives=True,
    ).execute()
    return folder["id"]

def sanitize_for_filename(value: str) -> str:
    """
    Make a value safe for use in a filename:
    - strip outer spaces
    - normalize unicode
    - keep only letters/digits and a few safe symbols
    - replace whitespace with underscores
    """
    value = (value or "").strip()
    if not value:
        return "unnamed"

    value = unicodedata.normalize("NFKD", value)
    allowed = "-_.() "
    value = "".join(ch for ch in value if ch.isalnum() or ch in allowed)
    value = re.sub(r"\s+", "_", value)
    return value or "unnamed"

def upload_art_to_drive(
    service,
    local_path: str,
    *,
    category: str,           # "Sprite" or "Splash"
    country: str,
    discord_username: str,
    artist_name: str,
):
    """
    Upload the local file into:
        ART_ROOT_FOLDER_ID / [country] / [category] / [file]

    where [file] = discordUser.artistName.country.png
    """
    root_parent = ART_ROOT_FOLDER_ID

    # Country folder
    country_folder_id = get_or_create_folder(service, country, root_parent)

    # Sprite / Splash subfolder under country
    category_folder_id = get_or_create_folder(service, category, country_folder_id)

    # We enforce PNG only, so just use .png
    _, ext = os.path.splitext(local_path)
    ext = ext.lower()

    base_name = f"{discord_username}.{artist_name}.{country}"
    safe_base = sanitize_for_filename(base_name)
    drive_filename = f"{safe_base}{ext}"

    metadata = {
        "name": drive_filename,
        "parents": [category_folder_id],
    }

    media = MediaFileUpload(local_path, mimetype="image/png", resumable=True)

    drive_file = service.files().create(
        body=metadata,
        media_body=media,
        fields="id, webViewLink, webContentLink",
        supportsAllDrives=True,
    ).execute()

    drive_path = f"{country}/{category}/{drive_filename}"
    return drive_file, drive_path


@dataclass
class AvailabilityIndex:
    by_norm: Dict[str, CountryRecord]
    all_names: List[str]

    @classmethod
    def build(cls, records: List[CountryRecord]) -> "AvailabilityIndex":
        by_norm: Dict[str, CountryRecord] = {}
        names: List[str] = []
        for r in records:
            key = normalize_country(r.country)
            if key:
                by_norm[key] = r
                names.append(r.country)
        return cls(by_norm=by_norm, all_names=sorted(set(names), key=str.lower))

    def find(self, query: str) -> Tuple[Optional[CountryRecord], Optional[str]]:
        q = normalize_country(query)
        logger.debug("AvailabilityIndex.find: query=%r normalized=%r", query, q)
        if not q:
            return None, None

        # Exact normalized match
        if q in self.by_norm:
            return self.by_norm[q], None
        
        keys = list(self.by_norm.keys())
        
        candidates = difflib.get_close_matches(q, keys, n=1, cutoff=0.75)
        if candidates:
            best = candidates[0]
            return None, self.by_norm[best].country

        # Try matching against normalized original names with a slightly lower cutoff
        norm_map = {normalize_country(n): n for n in self.all_names if normalize_country(n)}
        candidates2 = difflib.get_close_matches(q, list(norm_map.keys()), n=1, cutoff=0.6)
        if candidates2:
            return None, norm_map[candidates2[0]]

        # Fallback: substring match
        for k in keys:
            if q in k or k in q:
                return None, self.by_norm[k].country

        logger.info("AvailabilityIndex.find: no match for query=%r normalized=%r (keys=%d)", query, q, len(keys))
        return None, None


class PolandballBot(commands.Bot):
    def __init__(self):
        intents = discord.Intents.default()
        intents.message_content = True
        super().__init__(command_prefix="/", intents=intents, help_command=None)
        self.sheet_client: Optional[SheetClient] = None
        self.cache = Cache(ttl=CACHE_TTL_SECS)
        self._command_lock = False
        # NEW: Google Drive upload client
        self.drive_service = create_drive_service()

    async def on_ready(self):
        logger.info("Logged in as %s (id=%s)", self.user, self.user.id)
        try:
            synced = await self.tree.sync()
            logger.info(
                "Synced %d command(s): %s",
                len(synced),
                [c.name for c in synced],
            )
        except Exception as e:
            logger.exception("Failed to sync commands: %s", e)


    def _load_index(self) -> AvailabilityIndex:
        cached = self.cache.get()
        if cached is None:
            if self.sheet_client is None:
                self.sheet_client = SheetClient()
            records = self.sheet_client.fetch_records()
            self.cache.set(records)
        else:
            records = cached
        return AvailabilityIndex.build(records)


bot = PolandballBot()


@bot.tree.command(name="available", description="Check availability of characters or view all available characters")
@app_commands.describe(character="Character name (leave blank to see all available)")
async def available(interaction: discord.Interaction, character: Optional[str] = None):
    await interaction.response.defer()
    try:
        idx = bot._load_index()
    except Exception as e:
        logger.exception("Sheet load failed")
        await interaction.followup.send(f"Sorry, I couldn't load the availability sheet: {e}")
        return

    arg_str = (character or "").strip()

    if arg_str.lower() in {"ball", "balls", ""}:
        sprite_list = sorted(
            {r.country for r in idx.by_norm.values() if r.is_available("sprite") is True},
            key=str.lower,
        )
        splash_list = sorted(
            {r.country for r in idx.by_norm.values() if r.is_available("splash") is True},
            key=str.lower,
        )

        # Helper to split long lists into multiple embed fields (Discord field limit ~1024 chars)
        def fields_from_list(title: str, values: List[str]) -> List[Tuple[str, str, bool]]:
            if not values:
                return [(f"{title} (0)", "_none_", False)]

            max_len = 900
            chunks: List[List[str]] = [[]]
            for v in sorted(values, key=str.lower):
                current = chunks[-1]
                candidate = "\n".join(current + [f"• {v}"])
                if len(candidate) > max_len:
                    chunks.append([f"• {v}"])
                else:
                    current.append(f"• {v}")

            fields: List[Tuple[str, str, bool]] = []
            for i, chunk in enumerate(chunks, start=1):
                name_suffix = f" (page {i})" if len(chunks) > 1 else ""
                fields.append((f"{title} ({len(values)}){name_suffix}", "\n".join(chunk), False))
            return fields

        embed = discord.Embed(
            title="Available Characters",
            description=f"Sourced from [{SHEET_NAME}]({GOOGLE_SHEET_URL})\nUpdated every {CACHE_TTL_SECS}s",
            color=discord.Color.blurple(),
        )
        embed.set_thumbnail(url="https://raw.githubusercontent.com/EitanJoseph/polandball-art-helper/refs/heads/main/profile%20picx.png")

        for title, content, inline in fields_from_list("Sprites", sprite_list):
            embed.add_field(name=title, value=content, inline=False)
        for title, content, inline in fields_from_list("Splashes", splash_list):
            embed.add_field(name=title, value=content, inline=False)

        await interaction.followup.send(embed=embed)
        return

    rec, suggestion = idx.find(arg_str)
    if rec:
        s_sprite = rec.is_available("sprite")
        s_splash = rec.is_available("splash")

        if s_sprite is True:
            sprite_status = "✅ **Available**"
        elif s_sprite is False:
            sprite_status = "☑️ **Claimed**"
        else:
            sprite_status = "⚪ **Unknown**"

        if s_splash is True:
            splash_status = "✅ **Available**"
        elif s_splash is False:
            splash_status = "☑️ **Claimed**"
        else:
            splash_status = "⚪ **Unknown**"

        ig = rec.in_game_status()
        if ig is True:
            ig_text = "🟢 In Game"
        elif ig is False:
            ig_text = "🔴 Not In Game"
        else:
            ig_text = "⚪ In-game status unknown"

        sprite_lines = [sprite_status]
        if rec.sprite_artist:
            sprite_lines.append(f"Artist: `{rec.sprite_artist}`")
        if rec.sprite_rdy:
            sprite_lines.append(f"Status: `{format_ready_flag(rec.sprite_rdy)}`")

        splash_lines = [splash_status]
        if rec.splash_artist:
            splash_lines.append(f"Artist: `{rec.splash_artist}`")
        if rec.splash_rdy:
            splash_lines.append(f"Status: `{format_ready_flag(rec.splash_rdy)}`")

        embed = discord.Embed(
            title=rec.country,
            description=ig_text,
            url=GOOGLE_SHEET_URL,
            color=discord.Color.light_grey() if ig is True else discord.Color.green(),
        )
        embed.set_thumbnail(url="https://polandballgo.com/assets/logo.png")

        embed.add_field(name="Sprite", value="\n".join(sprite_lines), inline=True)
        embed.add_field(name="Splash", value="\n".join(splash_lines), inline=True)

        embed.set_footer(text=f"Sourced from {SHEET_NAME}")
        await interaction.followup.send(embed=embed)
        return

    if suggestion:
        await interaction.followup.send(f"I couldn't find that exactly.\nDid you mean **{suggestion}**?")
    else:
        await interaction.followup.send("I couldn't find that country in the sheet.")


def format_ready_flag(raw: str) -> str:
    s = (raw or "").strip().lower()
    if not s:
        return "No status"
    if s in {"y", "yes", "ready", "rdy"}:
        return "Complete"
    if s in {"n", "no"}:
        return "In progress"
    return raw

def ready_icon(label: str) -> str:
    if label == "Complete":
        return "✅"
    if label == "In progress":
        return "⏳"
    if label == "No status":
        return "⚪"
    return "⚪"

@bot.tree.command(name="ping", description="Ping the bot")
async def ping(interaction: discord.Interaction):
    await interaction.response.send_message("pong")


class ArtType(Enum):
    splash = "splash"
    sprite = "sprite"
    both = "both"

@bot.tree.command(name="artist", description="Search for all characters done by a given artist")
@app_commands.describe(
    name="Artist name (full or partial)",
    kind="Filter by splash, sprite, or both",
)
@app_commands.choices(
    kind=[
        app_commands.Choice(name="Both", value="both"),
        app_commands.Choice(name="Splash only", value="splash"),
        app_commands.Choice(name="Sprite only", value="sprite"),
    ]
)
async def artist(
    interaction: discord.Interaction,
    name: str,
    kind: app_commands.Choice[str] = None,
):
    await interaction.response.defer()

    art_type = (kind.value if kind else "both").lower()

    # Load records (reuse cache logic)
    try:
        records = bot.cache.get()
        if records is None:
            if bot.sheet_client is None:
                bot.sheet_client = SheetClient()
            records = bot.sheet_client.fetch_records()
            bot.cache.set(records)
    except Exception as e:
        logger.exception("Sheet load failed for /artist")
        await interaction.followup.send(f"Sorry, I couldn't load the sheet: {e}")
        return
    
    def normalize_name(s: str) -> str:
        """
        Normalize artist / query text for fuzzy matching:
        - Unicode normalize (NFKD)
        - keep only letters (drop emoji, punctuation, bullets, etc.)
        - lowercase
        """
        if not s:
            return ""
        # decompose fancy unicode characters
        s = unicodedata.normalize("NFKD", s)
        # keep only alphabetic characters
        s = "".join(ch for ch in s if ch.isalpha())
        return s.lower()

    FUZZY_THRESHOLD = 0.7  # or whatever you're using

    def fuzzy_score(query: str, target: str) -> float:
        """
        Returns a similarity score between 0 and 1.

        - If query is 1 letter, only treat exact 1-letter names as matches.
        - If normalized query is a substring of normalized target (len >= 3), treat as strong match.
        - Otherwise, use a fuzzy similarity ratio on normalized strings.
        """
        if not target:
            return 0.0

        q = normalize_name(query)
        t = normalize_name(target)

        if not q:
            return 0.0

        # one-letter special case
        if len(q) == 1:
            return 1.0 if t == q else 0.0

        # substring boost: "bread" in "Bread_from_Seoul", "jose" in "Jose11santamari"
        if len(q) >= 3 and q in t:
            return 1.0

        return difflib.SequenceMatcher(None, q, t).ratio()

    raw_query = name.strip()
    query_norm = normalize_name(raw_query)
    if not query_norm:
        await interaction.followup.send(
            "Please provide at least one letter of an artist name."
        )
        return

    # --- FIRST PASS: exact matches only (normalized equality) ---
    exact_splash: List[CountryRecord] = []
    exact_sprite: List[CountryRecord] = []
    exact_artist_names: List[str] = []

    for r in records:
        raw_splash = (r.splash_artist or "").strip()
        raw_sprite = (r.sprite_artist or "").strip()

        nsplash = normalize_name(raw_splash)
        nsprite = normalize_name(raw_sprite)

        if nsplash and nsplash == query_norm:
            exact_splash.append(r)
            exact_artist_names.append(raw_splash)

        if nsprite and nsprite == query_norm:
            exact_sprite.append(r)
            exact_artist_names.append(raw_sprite)

    if exact_splash or exact_sprite:
        # We found at least one exact artist name match → use ONLY these.
        matches_splash = exact_splash
        matches_sprite = exact_sprite

        # pick a display name (just take the first exact artist name)
        real_artist = exact_artist_names[0]

        # apply type filter
        if art_type == "splash":
            matches_sprite = []
        elif art_type == "sprite":
            matches_splash = []

        if not matches_splash and not matches_sprite:
            await interaction.followup.send(
                f"I couldn't find any characters for an artist matching `{name}`."
            )
            return

    else:
            matches_splash: List[CountryRecord] = []
            matches_sprite: List[CountryRecord] = []
            artist_scores: Dict[str, float] = {}

            for r in records:
                raw_splash = (r.splash_artist or "").strip()
                raw_sprite = (r.sprite_artist or "").strip()

                splash_score = fuzzy_score(query_norm, raw_splash) if raw_splash else 0.0
                sprite_score = fuzzy_score(query_norm, raw_sprite) if raw_sprite else 0.0

                if splash_score >= FUZZY_THRESHOLD:
                    matches_splash.append(r)
                    artist_scores[raw_splash] = max(artist_scores.get(raw_splash, 0.0),
                                                    splash_score)

                if sprite_score >= FUZZY_THRESHOLD:
                    matches_sprite.append(r)
                    artist_scores[raw_sprite] = max(artist_scores.get(raw_sprite, 0.0),
                                                    sprite_score)

            if art_type == "splash":
                matches_sprite = []
            elif art_type == "sprite":
                matches_splash = []

            if not matches_splash and not matches_sprite:
                await interaction.followup.send(
                    f"I couldn't find any characters for an artist matching `{name}`."
                )
                return

            if artist_scores:
                real_artist = max(artist_scores.items(), key=lambda kv: kv[1])[0]
            else:
                real_artist = name

            # 🔽 NEW: filter to only that artist
            target_norm = normalize_name(real_artist)

            def same_artist(a: str) -> bool:
                return normalize_name(a) == target_norm

            matches_splash = [r for r in matches_splash if same_artist(r.splash_artist)]
            matches_sprite = [r for r in matches_sprite if same_artist(r.sprite_artist)]

            if not matches_splash and not matches_sprite:
                await interaction.followup.send(
                    f"I couldn't find any characters for an artist matching `{real_artist}`."
                )
                return

    embed = discord.Embed(
        title=f"Art by {real_artist}",
        description=(
            f"Sourced from [{SHEET_NAME}]({GOOGLE_SHEET_URL})\n"
        ),
        color=discord.Color.blurple(),
    )
    embed.set_thumbnail(url="https://polandballgo.com/assets/logo.png")

    def format_list(title: str, recs: List[CountryRecord], get_flag) -> None:
        if not recs:
        # consistent bold + count even when empty
            embed.add_field(
                name=f"**{title} (0)**",
                value="_none_",   # italic 'none'
                inline=False,
            )
            return

        recs_sorted = sorted(recs, key=lambda r: r.country.lower())

        buckets = {
            "Complete": [],
            "In progress": [],
            "No status": [],
            "Other": [],
        }

        for r in recs_sorted:
            label = format_ready_flag(get_flag(r))
            if label not in buckets:
                buckets["Other"].append(r)
            else:
                buckets[label].append(r)

        max_len = 1000  # keep some headroom under Discord's 1024 limit
        lines: List[str] = []
        current_len = 0
        hidden_count = 0

        order = ["Complete", "In progress", "No status", "Other"]

        for label in order:
            items = buckets[label]
            if not items:
                continue

            icon = ready_icon(label)
            header = f"{icon} **{label} ({len(items)})**"

            # If even the header doesn't fit, bail out
            if current_len + len(header) + 1 > max_len:
                hidden_count += sum(len(buckets[l]) for l in order[order.index(label):])
                break

            lines.append(header)
            current_len += len(header) + 1  # + newline

            for r in items:
                line = f"• {r.country}"
                if current_len + len(line) + 1 > max_len:
                    # count this item + all remaining items in all remaining buckets
                    hidden_count += 1  # this one
                    # remaining in this bucket
                    remaining_here = len(items) - (items.index(r) + 1)
                    hidden_count += remaining_here
                    # remaining in later buckets
                    for later_label in order[order.index(label) + 1:]:
                        hidden_count += len(buckets[later_label])
                    # stop adding lines entirely
                    break
                lines.append(line)
                current_len += len(line) + 1
            else:
                # finished this bucket normally -> add a blank line
                lines.append("")
                current_len += 1
                continue  # go to next bucket

            # we broke from the inner loop because of length, so stop outer too
            break

        # remove trailing blank
        if lines and lines[-1] == "":
            lines.pop()

        if hidden_count > 0:
            lines.append(f"… and {hidden_count} more")

        value = "\n".join(lines)

        embed.add_field(
            name=f"**{title} ({len(recs_sorted)}**)",  
            value=value,
            inline=False,
        )


    if art_type in ("both", "splash"):
        format_list("*🎨 Splash Art*", matches_splash, lambda r: r.splash_rdy)

    if art_type in ("both", "sprite"):
        divider = "⠂" * 12
        embed.add_field(name=divider, value="", inline=False)
        format_list("*🎨 Sprite Art*", matches_sprite, lambda r: r.sprite_rdy)

    await interaction.followup.send(embed=embed)

CATEGORY_CHOICES = ["Sprite", "Splash"]


def convert_png_to_webp(png_path: str) -> str:
    """
    Converts a PNG file to WEBP and returns the new WEBP path.
    Keeps transparency intact.
    """
    webp_path = os.path.splitext(png_path)[0] + ".webp"

    with Image.open(png_path) as img:
        img.save(
            webp_path,
            format="WEBP",
            lossless=True,   # preserve crisp pixel edges
            quality=100,
        )

    return webp_path

def get_custom_emoji(bot: commands.Bot, emoji_name: str) -> str:
    """
    Returns the Discord representation of a custom emoji by name.
    Falls back to text if not found.
    """
    emoji = discord.utils.get(bot.emojis, name=emoji_name)
    return str(emoji) if emoji else f":{emoji_name}:"


@bot.tree.command(name="submit", description="Submit art")
@app_commands.describe(
    category="Art category (Sprite or Splash)",
    artist_name="Folder artist name (as you want it to appear)",
    country="Country / character name (from the game list)",
    image="Attach your art file (PNG only)",
)
@app_commands.choices(
    category=[app_commands.Choice(name=c, value=c) for c in CATEGORY_CHOICES]
)
async def submit_art(
    interaction: discord.Interaction,
    category: app_commands.Choice[str],
    artist_name: str,
    country: str,
    image: discord.Attachment,
):
    await interaction.response.defer(ephemeral=True)

    tmp_path: Optional[str] = None

    try:
        # --- 1) Enforce country must be from spreadsheet ---
        try:
            idx = bot._load_index()  # AvailabilityIndex built from your sheet
            valid_countries = set(idx.all_names)
        except Exception as e:
            logger.exception("Failed to load index for submit_art: %s", e)
            await interaction.followup.send(
                "❌ I couldn't load the country list from the sheet. Please try again later.",
                ephemeral=True,
            )
            return

        if country not in valid_countries:
            await interaction.followup.send(
                f"❌ `{country}` is not a valid country in the game list.\n"
                "Please choose a country from the autocomplete suggestions.",
                ephemeral=True,
            )
            return

        # --- 2) Enforce PNG only ---
        filename = image.filename or ""
        _, ext = os.path.splitext(filename)
        ext = ext.lower()

        # Optionally also check content_type: image.content_type == "image/png"
        if ext != ".png":
            await interaction.followup.send(
                "❌ Only **PNG** files are allowed.\n"
                f"You uploaded `{filename}`.\n"
                "Please export your art as a `.png` file and try again.",
                ephemeral=True,
            )
            return

        # 3) Use system temp directory (cross-platform)
        tmp_dir = tempfile.gettempdir()
        os.makedirs(tmp_dir, exist_ok=True)

        tmp_path = os.path.join(tmp_dir, f"{uuid.uuid4()}{ext}")

        # Save Discord attachment to temp file
        await image.save(tmp_path)

        # 4) Upload to Drive: Country / [Sprite|Splash] / discordUser.artist.country.png
        service = interaction.client.drive_service
        discord_username = interaction.user.name  # or .display_name if you want

        # Convert PNG → WEBP
        webp_path = convert_png_to_webp(tmp_path)

        # Upload PNG
        drive_file_png, drive_path_png = upload_art_to_drive(
            service=service,
            local_path=tmp_path,
            category=category.value,
            country=country,
            discord_username=discord_username,
            artist_name=artist_name,
        )

        # Upload WEBP
        drive_file_webp, drive_path_webp = upload_art_to_drive(
            service=service,
            local_path=webp_path,
            category=category.value,
            country=country,
            discord_username=discord_username,
            artist_name=artist_name,
        )

        view_link_png = drive_file_png.get("webViewLink", "")
        view_link_webp = drive_file_webp.get("webViewLink", "")

        fire_emoji = get_custom_emoji(bot, "PoleonFire")
        await interaction.followup.send(
            "✅ **Submission received!**\n\n"
            "Your art has been successfully submitted.\n"
            "You'll be contacted if any changes are needed. Thank you for helping bring Polandball Go to life! {fire_emoji}",
            # f"**PNG:** {drive_path_png}\n{view_link_png}\n\n"
            # f"**WEBP:** {drive_path_webp}\n{view_link_webp}",
            ephemeral=True,
        )

    except Exception as e:
        logger.exception("submit_art failed")
        await interaction.followup.send(
            f"❌ Something went wrong while uploading your art:\n`{e}`",
            ephemeral=True,
        )

    finally:
        if tmp_path and os.path.exists(tmp_path):
            try:
                os.remove(tmp_path)
            except OSError:
                pass

SPRITE_EXAMPLE_URL = "https://raw.githubusercontent.com/wwxiao09/polandball-art-helper/669d6100bce364b77d74b90885830fa85b6b0231/denmark.png"

SPLASH_EXAMPLE_URL = "https://raw.githubusercontent.com/wwxiao09/polandball-art-helper/669d6100bce364b77d74b90885830fa85b6b0231/Baekje.png"



@submit_art.autocomplete("country")
async def submit_art_country_autocomplete(
    interaction: discord.Interaction,
    current: str,
):
    """
    Autocomplete callback for the 'country' option.
    Suggests country names from column B of the sheet.
    """
    try:
        idx = bot._load_index()  # AvailabilityIndex
        all_countries = idx.all_names  # already sorted list of names
    except Exception as e:
        logger.exception("Failed to load index for autocomplete: %s", e)
        return []

    current_lower = (current or "").lower()
    if not current_lower:
        # first open: show first 25 countries
        matches = all_countries[:25]
    else:
        matches = [
            name for name in all_countries
            if current_lower in name.lower()
        ][:25]

    return [app_commands.Choice(name=m, value=m) for m in matches]

@bot.tree.command(
    name="help",
    description="Show all bot commands and Polandball art guidelines",
)
async def help_command(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)

    # --- Commands section ---
    commands_text = (
        "**/submit** – Submit art to the Polandball Go Drive\n"
        "• `category` – **Sprite** or **Splash**\n"
        "• `artist_name` – How you want to be credited in folders\n"
        "• `country` – Pick from the autocomplete list (only countries from the game sheet)\n"
        "• `image` – **PNG only**\n\n"
        "**/available** `[character]`\n"
        "• No name → lists all characters that are available as sprites / splashes\n"
        "• With a name → shows if that character’s sprite/splash is available or claimed\n\n"
        "**/artist** `name` `[kind]`\n"
        "• Shows which characters a given artist has done (sprite / splash / both)\n\n"
        "**/ping**\n"
        "• Quick check that the bot is alive (replies with `pong`)."
    )

    # --- Sprite vs Splash section ---
    art_types_text = (
        "**Splash Art**\n"
        "• Detailed, stylized illustration (often with a background)\n"
        "• Used in character / showcase screens\n"
        "• Wide banners (around 3:2) look best\n"
        "• Main focus must be the **main countryball** – side characters are okay "
        "as long as they don't steal the spotlight\n\n"
        "**Sprite Art**\n"
        "• Simple, clean countryball with **no background**\n"
        "• Used as the in-game character model\n"
        "• Less detail – they’ll be small on screen, too much detail won’t be visible\n"
        "• A subtle shadow under the ball helps it feel grounded in-game\n"
        "• Think of sprites as the **playable** versions of the balls."
    )

    # --- Core Polandball drawing rules (short version) ---
    polandball_rules_text = (
        "**Basic style**\n"
        "• Draw the ball **by hand with the mouse** – no circle tools, shape tools or "
        "vector-perfect outlines.\n"
        "• **No anti-aliasing** – outlines must be **hard-edged and pixel-clean** (no soft or blurry edges).\n"
        "• Simple colours, no fancy gradients or 3D rendering.\n"
        "• Eyes only (no mouths or noses in normal cases) – two white circles with black pupils.\n\n"
        "**Flags & shapes**\n"
        "• Use the **correct flag colours and layout** for each country.\n"
        "• Polandball is traditionally drawn **upside down** (white on top, red on bottom, "
        "but the ball is flipped).\n"
        "• Balls stay round – no country-shaped blobs or detailed maps."
    )

    embed = discord.Embed(
        title="Polandball Go Art Helper – Help",
        description=(
            "Here’s how to use the bot and the basics of Polandball art style.\n"
            "You can submit either **Sprite Art**, **Splash Art**, or both."
        ),
        color=discord.Color.blurple(),
    )
    embed.add_field(name="Commands", value=commands_text, inline=False)
    embed.add_field(name="Sprite vs Splash", value=art_types_text, inline=False)
    embed.add_field(
        name="Polandball Art Rules (Short Version)",
        value=polandball_rules_text,
        inline=False,
    )
    embed.set_footer(
        text="Based on the r/Polandball “Académie Polandballaise” tutorial and community rules."
    )

    await interaction.followup.send(embed=embed, ephemeral=True)

    # --- Sprite Example ---
    sprite_embed = discord.Embed(
        title="✅ Sprite Art — Good Example",
        color=discord.Color.green(),
    )
    sprite_embed.set_image(url=SPRITE_EXAMPLE_URL)

    await interaction.followup.send(embed=sprite_embed)


    # --- Splash Example ---
    splash_embed = discord.Embed(
        title="✅ Splash Art — Good Example",
        color=discord.Color.orange(),
    )
    splash_embed.set_image(url=SPLASH_EXAMPLE_URL)

    await interaction.followup.send(embed=splash_embed)



async def handle_client(reader, writer):
    try:
        await reader.read(1024)
        response = b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nOK"
        writer.write(response)
        await writer.drain()
    finally:
        writer.close()
        await writer.wait_closed()


async def main():
    if not DISCORD_TOKEN:
        raise RuntimeError("DISCORD_TOKEN env var is required.")
    port = int(os.getenv("PORT", "8080"))
    server = await asyncio.start_server(handle_client, host="0.0.0.0", port=port)
    async with server:
        await asyncio.gather(
            bot.start(DISCORD_TOKEN),
            server.serve_forever(),
        )


if __name__ == "__main__":
    asyncio.run(main())
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

5) /submit
   → Submit Sprite or Splash art for a character (PNG only).

6) /help
   → View all bot commands and Polandball art guidelines.


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
import math
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple
from enum import Enum

import discord
from discord.ext import commands
from discord import app_commands
from discord.errors import NotFound, HTTPException

import gspread
from google.oauth2.service_account import Credentials
from google.auth import default as google_auth_default

import tempfile
import uuid

import errno
import random

import functools

from googleapiclient.discovery import build
from googleapiclient.http import MediaFileUpload
from googleapiclient.errors import HttpError

from datetime import datetime, timezone

from PIL import Image
Image.MAX_IMAGE_PIXELS = 12_000_000  # ~12MP safety cap to prevent memory spikes

# For local test only
# from dotenv import load_dotenv
# load_dotenv()


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


ART_ROOT_FOLDER_ID = os.getenv("ART_ROOT_FOLDER_ID")
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
    splash_artist_alt: str
    sprite_artist_alt: str

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
        splash_artist_alt_i = col_letter_to_index("G")
        sprite_artist_alt_i = col_letter_to_index("H")

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
            splash_artist_alt = (
            row[splash_artist_alt_i].strip()
            if splash_artist_alt_i is not None and splash_artist_alt_i < len(row)
            else ""
            )
            sprite_artist_alt = (
                row[sprite_artist_alt_i].strip()
                if sprite_artist_alt_i is not None and sprite_artist_alt_i < len(row)
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
                        splash_artist_alt=splash_artist_alt,
                        sprite_artist_alt=sprite_artist_alt,
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

def drive_execute_with_retry(request, *, retries: int = 5, base_delay: float = 0.7):
    """
    Execute a googleapiclient request with exponential backoff retries for transient errors.
    Retries on 500/503/504 and rate-limit 429.
    """
    for attempt in range(retries):
        try:
            return request.execute()
        except HttpError as e:
            status = getattr(e.resp, "status", None)
            # transient / retryable statuses
            if status in (429, 500, 503, 504):
                # exponential backoff + jitter
                sleep_s = base_delay * (2 ** attempt) + random.uniform(0, 0.25)
                time.sleep(min(sleep_s, 8))
                continue
            raise

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

    result = drive_execute_with_retry(
        service.files().list(
            q=q,
            spaces="drive",
            fields="files(id, name)",
            pageSize=1,
            supportsAllDrives=True,
            includeItemsFromAllDrives=True,
        )
    )


    files = result.get("files", [])
    if files:
        return files[0]["id"]

    metadata = {
        "name": name,
        "mimeType": "application/vnd.google-apps.folder",
    }
    if parent_id:
        metadata["parents"] = [parent_id]

    folder = drive_execute_with_retry(
        service.files().create(
            body=metadata,
            fields="id",
            supportsAllDrives=True,
        )
    )

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

    timestamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
    base_name = f"{discord_username}.{artist_name}.{country}.{timestamp}"
    safe_base = sanitize_for_filename(base_name)
    drive_filename = f"{safe_base}{ext}"

    metadata = {
        "name": drive_filename,
        "parents": [category_folder_id],
    }

    media = MediaFileUpload(local_path, mimetype="image/png", resumable=False)

    drive_file = drive_execute_with_retry(
        service.files().create(
            body=metadata,
            media_body=media,
            fields="id, webViewLink, webContentLink",
            supportsAllDrives=True,
        )
    )


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
        self._countries_cache: list[str] = []
        self._countries_cache_ts: float = 0.0

        self._command_lock = False
        # NEW: Google Drive upload client
        self.drive_service = create_drive_service()

    async def on_ready(self):
        logger.info("Logged in as %s (id=%s)", self.user, self.user.id)
        try:
            synced = await self.tree.sync()
            logger.info("Synced %d command(s): %s", len(synced), [c.name for c in synced])
        except Exception as e:
            logger.exception("Failed to sync commands: %s", e)

        # ✅ ADD THIS: warm up sheet/cache for autocomplete
        async def _warm():
            try:
                await self.get_country_names_cached()
                logger.info("Warmed country cache for autocomplete.")
            except Exception:
                logger.exception("Failed to warm country cache")

        asyncio.create_task(_warm())

    async def setup_hook(self):
        """Setup hook to register error handlers"""
        self.tree.error(self.on_app_command_error)

    async def on_app_command_error(self, interaction: discord.Interaction, error: app_commands.AppCommandError):
        """Global error handler for app commands"""
        # Log the error
        logger.error(
            "Command '%s' raised an error for user %s: %s",
            interaction.command.name if interaction.command else "unknown",
            interaction.user,
            error,
            exc_info=error
        )

        # Handle specific error types
        if isinstance(error, app_commands.CommandInvokeError):
            original = error.original

            # Handle Discord API errors
            if isinstance(original, discord.errors.NotFound):
                if original.code == 10062:  # Unknown interaction
                    logger.warning(
                        "Interaction expired (>3s) for command '%s' by user %s",
                        interaction.command.name if interaction.command else "unknown",
                        interaction.user
                    )
                    # Can't respond - interaction is already expired
                    return

            elif isinstance(original, discord.errors.HTTPException):
                if original.code == 40060:  # Interaction already acknowledged
                    logger.warning(
                        "Interaction already acknowledged for command '%s' by user %s",
                        interaction.command.name if interaction.command else "unknown",
                        interaction.user
                    )
                    # Can't respond - already acknowledged
                    return

        # Try to send an error message to the user if possible
        try:
            error_message = "An error occurred while processing your command. Please try again."

            if not interaction.response.is_done():
                await interaction.response.send_message(error_message, ephemeral=True)
            else:
                await interaction.followup.send(error_message, ephemeral=True)
        except Exception as e:
            logger.error("Failed to send error message to user: %s", e)

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

    async def get_country_names_cached(self) -> list[str]:
        # return cached if fresh
        if self._countries_cache and (time.time() - self._countries_cache_ts) < CACHE_TTL_SECS:
            return self._countries_cache

        # Refresh in a thread so autocomplete doesn't block the event loop
        idx = await asyncio.to_thread(self._load_index)
        self._countries_cache = idx.all_names
        self._countries_cache_ts = time.time()
        return self._countries_cache


bot = PolandballBot()

PAGE_SIZE = 20

def chunk_list(items: List[str], page: int, page_size: int = PAGE_SIZE) -> List[str]:
    start = page * page_size
    end = start + page_size
    return items[start:end]

def build_available_embed(
    *,
    kind: str,
    page: int,
    sprite_needs_primary: List[str],
    sprite_has_primary: List[str],
    splash_needs_primary: List[str],
    splash_has_primary: List[str],
) -> discord.Embed:
    PER_PAGE = 20

    if kind == "sprite":
        needs = sprite_needs_primary
        has = sprite_has_primary
        title = "🎨 Sprite List"
        thumb = "https://polandballgo.com/assets/logo.png"
    else:
        needs = splash_needs_primary
        has = splash_has_primary
        title = "🖼️ Splash List"
        thumb = "https://polandballgo.com/assets/logo.png"

    combined = needs + has
    total = len(combined)
    total_pages = max(1, (total + PER_PAGE - 1) // PER_PAGE)
    page = max(0, min(page, total_pages - 1))

    start = page * PER_PAGE
    end = start + PER_PAGE
    chunk = combined[start:end]

    # split this page chunk back into sections
    needs_set = set(needs)
    chunk_needs = [c for c in chunk if c in needs_set]
    chunk_has = [c for c in chunk if c not in needs_set]

    embed = discord.Embed(
        title=title,
        description=f"Sourced from [{SHEET_NAME}]({GOOGLE_SHEET_URL})\nUpdated every {CACHE_TTL_SECS}s",
        color=discord.Color.blurple(),
    )
    embed.set_thumbnail(url=thumb)
    embed.add_field(name=f"Page {page+1}/{total_pages} • {total} total", value="\u200b", inline=False)

    if chunk_needs:
        embed.add_field(
            name="✅ Currently no primary artist (needs main art)",
            value="\n".join(f"• {c}" for c in chunk_needs),
            inline=False,
        )

    if chunk_has:
        embed.add_field(
            name="✨ Has primary artist (alt submissions welcome)",
            value="\n".join(f"• {c}" for c in chunk_has),
            inline=False,
        )

    if not chunk_needs and not chunk_has:
        embed.add_field(name="Characters", value="_none_", inline=False)

    return embed

class AvailableKindSelect(discord.ui.Select):
    def __init__(self, parent_view: "AvailableListView"):
        self.parent_view = parent_view
        options = [
            discord.SelectOption(label="Sprites", value="sprite", emoji="🎨"),
            discord.SelectOption(label="Splashes", value="splash", emoji="🖼️"),
        ]
        super().__init__(
            placeholder="Choose Sprite or Splash…",
            min_values=1,
            max_values=1,
            options=options,
        )

    async def callback(self, interaction: discord.Interaction):
        self.parent_view.kind = self.values[0]
        self.parent_view.page = 0  # reset when switching kind

        embed = build_available_embed(
            kind=self.parent_view.kind,
            page=self.parent_view.page,
            sprite_needs_primary=self.parent_view.sprite_needs_primary,
            sprite_has_primary=self.parent_view.sprite_has_primary,
            splash_needs_primary=self.parent_view.splash_needs_primary,
            splash_has_primary=self.parent_view.splash_has_primary,
        )

        self.parent_view._sync_buttons()
        await interaction.response.edit_message(embed=embed, view=self.parent_view)


class PageJumpModal(discord.ui.Modal, title="Jump to page"):
    page = discord.ui.TextInput(
        label="Page number",
        placeholder="Enter an integer (e.g. 1)",
        required=True,
        max_length=5,
    )

    def __init__(self, parent_view: "AvailableListView"):
        super().__init__()
        self.parent_view = parent_view

        # Optional: make the placeholder show the real range
        total = self.parent_view._total_pages()
        self.page.placeholder = f"1 - {total} (integer only)"

    async def on_submit(self, interaction: discord.Interaction):
        total_pages = self.parent_view._total_pages()
        raw = (self.page.value or "").strip()

        # allow only digits, no decimals, no minus, no spaces
        if not re.fullmatch(r"\d+", raw):
            await interaction.response.send_message(
                f"Please enter a whole number between **1** and **{total_pages}**.",
                ephemeral=True,
            )
            return

        n = int(raw)  # safe because digits only
        if not (1 <= n <= total_pages):
            await interaction.response.send_message(
                f"Page must be between **1** and **{total_pages}**.",
                ephemeral=True,
            )
            return

        self.parent_view.page = n - 1

        embed = build_available_embed(
            kind=self.parent_view.kind,
            page=self.parent_view.page,
            sprite_needs_primary=self.parent_view.sprite_needs_primary,
            sprite_has_primary=self.parent_view.sprite_has_primary,
            splash_needs_primary=self.parent_view.splash_needs_primary,
            splash_has_primary=self.parent_view.splash_has_primary,
        )
        self.parent_view._sync_buttons()
        await interaction.response.edit_message(embed=embed, view=self.parent_view)

class AvailableListView(discord.ui.View):
    def __init__(
        self,
        *,
        user_id: int,
        sprite_needs_primary: List[str],
        sprite_has_primary: List[str],
        splash_needs_primary: List[str],
        splash_has_primary: List[str],
        kind: str = "sprite",
    ):
        super().__init__(timeout=600)
        self.user_id = user_id
        self.message: discord.Message | None = None

        self.sprite_needs_primary = sprite_needs_primary
        self.sprite_has_primary = sprite_has_primary
        self.splash_needs_primary = splash_needs_primary
        self.splash_has_primary = splash_has_primary

        self.kind = kind
        self.page = 0

        self.add_item(AvailableKindSelect(self))
        self._sync_buttons()

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.user_id:
            await interaction.response.send_message(
                "This page control isn’t for you — run `/available` to get your own.",
                ephemeral=True,
            )
            return False
        return True

    def _current_combined(self) -> List[str]:
        """Needs primary first, then has primary."""
        if self.kind == "sprite":
            return self.sprite_needs_primary + self.sprite_has_primary
        return self.splash_needs_primary + self.splash_has_primary

    def _total_pages(self) -> int:
        total = len(self._current_combined())
        return max(1, (total + PAGE_SIZE - 1) // PAGE_SIZE)

    def _sync_buttons(self):
        total_pages = self._total_pages()
        on_first = (self.page <= 0)
        on_last = (self.page >= total_pages - 1)

        for child in self.children:
            if isinstance(child, discord.ui.Button):
                if child.custom_id == "avail_prev":
                    child.disabled = on_first
                elif child.custom_id == "avail_next":
                    child.disabled = on_last
                elif child.custom_id == "avail_first":
                    child.disabled = on_first
                elif child.custom_id == "avail_last":
                    child.disabled = on_last

    @discord.ui.button(label="First", style=discord.ButtonStyle.secondary, custom_id="avail_first")
    async def first_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.page = 0
        embed = build_available_embed(
            kind=self.kind,
            page=self.page,
            sprite_needs_primary=self.sprite_needs_primary,
            sprite_has_primary=self.sprite_has_primary,
            splash_needs_primary=self.splash_needs_primary,
            splash_has_primary=self.splash_has_primary,
        )
        self._sync_buttons()
        await interaction.response.edit_message(embed=embed, view=self)

    @discord.ui.button(label="Prev", style=discord.ButtonStyle.secondary, custom_id="avail_prev")
    async def prev_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.page = max(0, self.page - 1)
        embed = build_available_embed(
            kind=self.kind,
            page=self.page,
            sprite_needs_primary=self.sprite_needs_primary,
            sprite_has_primary=self.sprite_has_primary,
            splash_needs_primary=self.splash_needs_primary,
            splash_has_primary=self.splash_has_primary,
        )
        self._sync_buttons()
        await interaction.response.edit_message(embed=embed, view=self)

    @discord.ui.button(label="Next", style=discord.ButtonStyle.secondary, custom_id="avail_next")
    async def next_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.page = min(self._total_pages() - 1, self.page + 1)
        embed = build_available_embed(
            kind=self.kind,
            page=self.page,
            sprite_needs_primary=self.sprite_needs_primary,
            sprite_has_primary=self.sprite_has_primary,
            splash_needs_primary=self.splash_needs_primary,
            splash_has_primary=self.splash_has_primary,
        )
        self._sync_buttons()
        await interaction.response.edit_message(embed=embed, view=self)

    @discord.ui.button(label="Last", style=discord.ButtonStyle.secondary, custom_id="avail_last")
    async def last_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.page = self._total_pages() - 1
        embed = build_available_embed(
            kind=self.kind,
            page=self.page,
            sprite_needs_primary=self.sprite_needs_primary,
            sprite_has_primary=self.sprite_has_primary,
            splash_needs_primary=self.splash_needs_primary,
            splash_has_primary=self.splash_has_primary,
        )
        self._sync_buttons()
        await interaction.response.edit_message(embed=embed, view=self)

    @discord.ui.button(label="Jump", style=discord.ButtonStyle.primary, custom_id="avail_jump")
    async def jump_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.send_modal(PageJumpModal(self))

    async def on_timeout(self):
        for item in self.children:
            item.disabled = True
        if self.message:
            try:
                await self.message.edit(content="(Expired — run `/available` again.)", view=self)
            except Exception:
                pass

class SuggestionView(discord.ui.View):
    def __init__(self, *, user_id: int, suggestion: str, idx: "AvailabilityIndex"):
        super().__init__(timeout=60)
        self.user_id = user_id
        self.suggestion = suggestion
        self.idx = idx

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.user_id:
            await interaction.response.send_message(
                "This prompt isn’t for you — run `/available` yourself 🙂",
                ephemeral=True,
            )
            return False
        return True

    @discord.ui.button(label="Yes — show it", style=discord.ButtonStyle.primary)
    async def yes_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        rec, _ = self.idx.find(self.suggestion)
        if not rec:
            await interaction.response.edit_message(
                content="Sorry — I couldn’t load that character anymore.",
                view=None,
            )
            return

        embed = build_character_embed(rec)
        await interaction.response.edit_message(
            content=None,
            embed=embed,
            view=None,
        )

    @discord.ui.button(label="No", style=discord.ButtonStyle.secondary)
    async def no_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.edit_message(
            content="Okay — try `/available <character>` again with a different name.",
            view=None,
        )

def build_character_embed(rec: "CountryRecord") -> discord.Embed:
    ig = rec.in_game_status()
    if ig is True:
        ig_text = "🔵 In Game"
        color = discord.Color.blue()
    elif ig is False:
        ig_text = "🟢 Available"
        color = discord.Color.green()
    else:
        ig_text = "⚪ In-game status unknown"
        color = discord.Color.light_grey()

    def fmt_name(s: str) -> str:
        s = (s or "").strip()
        return f"`{s}`" if s else "`—`"

    sprite_lines = []

    if not has_primary_artist(rec.sprite_artist):
        sprite_lines.append("✅ **Primary art submission available**")
    else:
        sprite_lines.extend([
            f"🖌️ **Current Artist:** {fmt_name(rec.sprite_artist)}",
            f"**Status:** `{format_ready_flag(rec.sprite_rdy)}`",
            "",
            f"🧩 **Alternative Artist(s):** {fmt_name(rec.sprite_artist_alt)}",
            "**Alt submissions:** ✅ Open",
        ])

    splash_lines = []

    if not has_primary_artist(rec.splash_artist):
        splash_lines.append("✅ **Primary art submission available**")
    else:
        splash_lines.extend([
            f"🖌️ **Current Artist:** {fmt_name(rec.splash_artist)}",
            f"**Status:** `{format_ready_flag(rec.splash_rdy)}`",
            "",
            f"🧩 **Alternative Artist(s):** {fmt_name(rec.splash_artist_alt)}",
            "**Alt submissions:** ✅ Open",
        ])

    embed = discord.Embed(
        title=rec.country,
        description=ig_text,
        url=GOOGLE_SHEET_URL,
        color=color,
    )
    embed.set_thumbnail(url="https://polandballgo.com/assets/logo.png")
    # add a little padding at the end of sprite so mobile has a gap before Splash
    sprite_lines_padded = sprite_lines + ["\u200b"]  # invisible spacer lines

    embed.add_field(name="Sprite", value="\n".join(sprite_lines_padded), inline=True)
    embed.add_field(name="Splash", value="\n".join(splash_lines), inline=True)

    embed.set_footer(text=f"Sourced from {SHEET_NAME}\nUpdated every {CACHE_TTL_SECS}s")
    return embed


@bot.tree.command(name="available", description="Check availability of characters or view all available characters")
@app_commands.describe(character="Character name (leave blank to see all available)")
async def available(interaction: discord.Interaction, character: Optional[str] = None):
    if not interaction.response.is_done():
        await interaction.response.defer()

    try:
        idx = bot._load_index()
    except Exception as e:
        logger.exception("Sheet load failed")
        await interaction.followup.send(f"Sorry, I couldn't load the availability sheet: {e}")
        return

    arg_str = (character or "").strip()

    if arg_str.lower() in {"ball", "balls", ""}:
        # --- Needs Primary (no primary artist) ---
        sprite_needs_primary = sorted(
            {r.country for r in idx.by_norm.values() if not (r.sprite_artist or "").strip()},
            key=str.lower,
        )
        splash_needs_primary = sorted(
            {r.country for r in idx.by_norm.values() if not (r.splash_artist or "").strip()},
            key=str.lower,
        )

        # --- Has Primary (still open to alt submissions) ---
        sprite_has_primary = sorted(
            {r.country for r in idx.by_norm.values() if (r.sprite_artist or "").strip()},
            key=str.lower,
        )
        splash_has_primary = sorted(
            {r.country for r in idx.by_norm.values() if (r.splash_artist or "").strip()},
            key=str.lower,
        )

        view = AvailableListView(
            user_id=interaction.user.id,
            sprite_needs_primary=sprite_needs_primary,
            sprite_has_primary=sprite_has_primary,
            splash_needs_primary=splash_needs_primary,
            splash_has_primary=splash_has_primary,
            kind="sprite",
        )

        embed = build_available_embed(
            kind="sprite",
            page=0,
            sprite_needs_primary=sprite_needs_primary,
            sprite_has_primary=sprite_has_primary,
            splash_needs_primary=splash_needs_primary,
            splash_has_primary=splash_has_primary,
        )

        msg = await interaction.followup.send(embed=embed, view=view)
        view.message = msg
        return


    rec = None
    suggestion = None

    try:
        rec, suggestion = idx.find(arg_str)
    except Exception as e:
        logger.exception("available: idx.find failed for query=%r", arg_str)
        await interaction.followup.send(
            "Sorry — something went wrong while searching that character name.",
            ephemeral=True,
        )
        return
    
    if rec:
        embed = build_character_embed(rec)
        await interaction.followup.send(embed=embed)
        return
    # ✅ No exact match:
    if suggestion:
        view = SuggestionView(
            user_id=interaction.user.id,
            suggestion=suggestion,
            idx=idx,
    )
        await interaction.followup.send(
            content=f"I couldn't find that exactly.\nDid you mean **{suggestion}**?",
            view=view,
            ephemeral=True,
        )
        return


    await interaction.followup.send(
        "I couldn't find that country in the sheet.",
        ephemeral=True,
    )
    return

def has_primary_artist(name: str) -> bool:
    return bool((name or "").strip())

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
    try:
        if not interaction.response.is_done():
            await interaction.response.send_message("pong")
        else:
            await interaction.followup.send("pong")
    except (discord.errors.NotFound, discord.errors.HTTPException) as e:
        logger.warning("Failed to respond to ping command: %s", e)


class ArtType(Enum):
    splash = "splash"
    sprite = "sprite"
    both = "both"

def build_artist_embed(
    *,
    artist_name: str,
    kind: str,
    page: int,
    sprite_items: list[tuple[str, str]],
    splash_items: list[tuple[str, str]],
) -> discord.Embed:
    # Pick data set
    items = sprite_items if kind == "sprite" else splash_items
    total = len(items)

    # --- overall totals (ALL pages) ---
    complete_all = [c for (c, status) in items if status == "Complete"]
    inprog_all = [c for (c, status) in items if status == "In progress"]
    other_all = [c for (c, status) in items if status not in {"Complete", "In progress"}]

    # --- pagination ---
    total_pages = max(1, (total + PAGE_SIZE - 1) // PAGE_SIZE)
    page = max(0, min(page, total_pages - 1))

    start = page * PAGE_SIZE
    end = min(total, start + PAGE_SIZE)
    page_slice = items[start:end]

    # --- page-only groups ---
    complete_page = [c for (c, status) in page_slice if status == "Complete"]
    inprog_page = [c for (c, status) in page_slice if status == "In progress"]
    other_page = [c for (c, status) in page_slice if status not in {"Complete", "In progress"}]

    # --- embed base ---
    embed = discord.Embed(
        title=f"Art by {artist_name}",
        description=f"Sourced from [{SHEET_NAME}]({GOOGLE_SHEET_URL})",
        color=discord.Color.blurple(),
    )
    embed.set_thumbnail(url="https://polandballgo.com/assets/logo.png")

    kind_label = "Sprite Art" if kind == "sprite" else "Splash Art"
    embed.add_field(
        name=f"🎨 {kind_label}",
        value=f"Page {page + 1}/{total_pages} • {total} total",
        inline=False,
    )

    # --- content ---
    lines = []

    # ✅ show OVERALL totals, list PAGE items
    if complete_page:
        lines.append(f"✅ **Complete ({len(complete_all)})**")
        lines.extend(f"• {c}" for c in complete_page)

    if complete_page and inprog_page:
        lines.append("")

    if inprog_page:
        lines.append(f"⏳ **In progress ({len(inprog_all)})**")
        lines.extend(f"• {c}" for c in inprog_page)

    if complete_page and inprog_page:
        lines.append("")

    if other_page:
        lines.append(f"⚪ **Other ({len(other_all)})**")
        lines.extend(f"• {c}" for c in other_page)

    embed.add_field(name="\u200b", value="\n".join(lines), inline=False)

    return embed


class ArtistKindSelect(discord.ui.Select):
    def __init__(self, parent_view: "ArtistListView"):
        self.parent_view = parent_view
        options = [
            discord.SelectOption(label="Sprites", value="sprite", emoji="🎨"),
            discord.SelectOption(label="Splashes", value="splash", emoji="🖼️"),
        ]
        super().__init__(
            placeholder="Choose Sprite or Splash…",
            min_values=1,
            max_values=1,
            options=options,
        )

    async def callback(self, interaction: discord.Interaction):
        self.parent_view.kind = self.values[0]
        self.parent_view.page = 0

        embed = build_artist_embed(
            artist_name=self.parent_view.artist_name,
            kind=self.parent_view.kind,
            page=self.parent_view.page,
            sprite_items=self.parent_view.sprite_items,
            splash_items=self.parent_view.splash_items,
        )
        self.parent_view._sync_buttons()
        await interaction.response.edit_message(embed=embed, view=self.parent_view)


class ArtistJumpModal(discord.ui.Modal, title="Jump to page"):
    page = discord.ui.TextInput(
        label="Page number",
        placeholder="e.g. 1",
        required=True,
        max_length=5,
    )

    def __init__(self, parent_view: "ArtistListView"):
        super().__init__()
        self.parent_view = parent_view
        total = self.parent_view._total_pages()
        self.page.placeholder = f"1 - {total} (integer only)"

    async def on_submit(self, interaction: discord.Interaction):
        total_pages = self.parent_view._total_pages()
        raw = (self.page.value or "").strip()

        if not re.fullmatch(r"\d+", raw):
            await interaction.response.send_message(
                f"Please enter a whole number between **1** and **{total_pages}**.",
                ephemeral=True,
            )
            return

        n = int(raw)
        if not (1 <= n <= total_pages):
            await interaction.response.send_message(
                f"Page must be between **1** and **{total_pages}**.",
                ephemeral=True,
            )
            return

        self.parent_view.page = n - 1

        embed = build_artist_embed(
            artist_name=self.parent_view.artist_name,
            kind=self.parent_view.kind,
            page=self.parent_view.page,
            sprite_items=self.parent_view.sprite_items,
            splash_items=self.parent_view.splash_items,
        )
        self.parent_view._sync_buttons()
        await interaction.response.edit_message(embed=embed, view=self.parent_view)


class ArtistListView(discord.ui.View):
    def __init__(
        self,
        *,
        user_id: int,
        artist_name: str,
        sprite_items: List[tuple[str, str]],
        splash_items: List[tuple[str, str]],
        kind: str = "sprite",
    ):
        super().__init__(timeout=600)  # 10 minutes
        self.message: discord.Message | None = None

        self.user_id = user_id
        self.artist_name = artist_name
        self.sprite_items = sprite_items
        self.splash_items = splash_items
        self.kind = kind
        self.page = 0

        self.add_item(ArtistKindSelect(self))
        self._sync_buttons()

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.user_id:
            await interaction.response.send_message(
                "This control isn’t for you — run `/artist` to get your own view 🙂",
                ephemeral=True,
            )
            return False
        return True

    def _current_items(self):
        return self.sprite_items if self.kind == "sprite" else self.splash_items

    def _total_pages(self) -> int:
        total = len(self._current_items())
        return max(1, (total + PAGE_SIZE - 1) // PAGE_SIZE)

    def _sync_buttons(self):
        total_pages = self._total_pages()
        on_first = (self.page <= 0)
        on_last = (self.page >= total_pages - 1)

        for child in self.children:
            if isinstance(child, discord.ui.Button):
                if child.custom_id == "artist_first":
                    child.disabled = on_first
                elif child.custom_id == "artist_prev":
                    child.disabled = on_first
                elif child.custom_id == "artist_next":
                    child.disabled = on_last
                elif child.custom_id == "artist_last":
                    child.disabled = on_last

    @discord.ui.button(label="First", style=discord.ButtonStyle.secondary, custom_id="artist_first")
    async def first_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.page = 0
        embed = build_artist_embed(
            artist_name=self.artist_name,
            kind=self.kind,
            page=self.page,
            sprite_items=self.sprite_items,
            splash_items=self.splash_items,
        )
        self._sync_buttons()
        await interaction.response.edit_message(embed=embed, view=self)

    @discord.ui.button(label="Prev", style=discord.ButtonStyle.secondary, custom_id="artist_prev")
    async def prev_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.page = max(0, self.page - 1)
        embed = build_artist_embed(
            artist_name=self.artist_name,
            kind=self.kind,
            page=self.page,
            sprite_items=self.sprite_items,
            splash_items=self.splash_items,
        )
        self._sync_buttons()
        await interaction.response.edit_message(embed=embed, view=self)

    @discord.ui.button(label="Next", style=discord.ButtonStyle.secondary, custom_id="artist_next")
    async def next_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.page = min(self._total_pages() - 1, self.page + 1)
        embed = build_artist_embed(
            artist_name=self.artist_name,
            kind=self.kind,
            page=self.page,
            sprite_items=self.sprite_items,
            splash_items=self.splash_items,
        )
        self._sync_buttons()
        await interaction.response.edit_message(embed=embed, view=self)

    @discord.ui.button(label="Last", style=discord.ButtonStyle.secondary, custom_id="artist_last")
    async def last_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.page = self._total_pages() - 1
        embed = build_artist_embed(
            artist_name=self.artist_name,
            kind=self.kind,
            page=self.page,
            sprite_items=self.sprite_items,
            splash_items=self.splash_items,
        )
        self._sync_buttons()
        await interaction.response.edit_message(embed=embed, view=self)

    @discord.ui.button(label="Jump", style=discord.ButtonStyle.primary, custom_id="artist_jump")
    async def jump_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.send_modal(ArtistJumpModal(self))

    async def on_timeout(self):
        for item in self.children:
            item.disabled = True
        if self.message:
            try:
                await self.message.edit(content="(Expired — run `/artist` again.)", view=self)
            except Exception:
                pass


@bot.tree.command(name="artist", description="Search for all characters done by a given artist")
@app_commands.describe(name="Artist name (full or partial)")
async def artist(interaction: discord.Interaction, name: str):
    if not interaction.response.is_done():
        await interaction.response.defer()


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
        s = unicodedata.normalize("NFKD", s)
        s = "".join(ch for ch in s if ch.isalpha())
        return s.lower()

    FUZZY_THRESHOLD = 0.7

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

        if len(q) == 1:
            return 1.0 if t == q else 0.0

        if len(q) >= 3 and q in t:
            return 1.0

        return difflib.SequenceMatcher(None, q, t).ratio()

    raw_query = name.strip()
    query_norm = normalize_name(raw_query)
    if not query_norm:
        await interaction.followup.send("Please provide at least one letter of an artist name.")
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
        matches_splash = exact_splash
        matches_sprite = exact_sprite
        real_artist = exact_artist_names[0] if exact_artist_names else name
    else:
        matches_splash = []
        matches_sprite = []
        artist_scores: Dict[str, float] = {}

        for r in records:
            raw_splash = (r.splash_artist or "").strip()
            raw_sprite = (r.sprite_artist or "").strip()

            splash_score = fuzzy_score(query_norm, raw_splash) if raw_splash else 0.0
            sprite_score = fuzzy_score(query_norm, raw_sprite) if raw_sprite else 0.0

            if splash_score >= FUZZY_THRESHOLD:
                matches_splash.append(r)
                artist_scores[raw_splash] = max(artist_scores.get(raw_splash, 0.0), splash_score)

            if sprite_score >= FUZZY_THRESHOLD:
                matches_sprite.append(r)
                artist_scores[raw_sprite] = max(artist_scores.get(raw_sprite, 0.0), sprite_score)

        if not matches_splash and not matches_sprite:
            await interaction.followup.send(
                f"I couldn't find any characters for an artist matching `{name}`."
            )
            return

        real_artist = max(artist_scores.items(), key=lambda kv: kv[1])[0] if artist_scores else name

        # Filter to ONLY that artist
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

    # Convert matched records -> (country, status) pairs (DEDUP by country)
    sprite_map: dict[str, str] = {}
    for r in matches_sprite:
        if not r.country:
            continue
        country = r.country.strip()
        status = format_ready_flag(r.sprite_rdy)

        # Prefer "Complete" if duplicates exist
        if country not in sprite_map or (sprite_map[country] != "Complete" and status == "Complete"):
            sprite_map[country] = status

    sprite_items = sorted(sprite_map.items(), key=lambda x: x[0].lower())

    splash_map: dict[str, str] = {}
    for r in matches_splash:
        if not r.country:
            continue
        country = r.country.strip()
        status = format_ready_flag(r.splash_rdy)

        # Prefer "Complete" if duplicates exist
        if country not in splash_map or (splash_map[country] != "Complete" and status == "Complete"):
            splash_map[country] = status

    splash_items = sorted(splash_map.items(), key=lambda x: x[0].lower())


    if not sprite_items and not splash_items:
        await interaction.followup.send(
            f"I couldn't find any characters for an artist matching `{real_artist}`."
        )
        return

    # Default tab: Sprite if any, else Splash
    kind = "sprite" if sprite_items else "splash"

    view = ArtistListView(
        user_id=interaction.user.id,
        artist_name=real_artist,
        sprite_items=sprite_items,
        splash_items=splash_items,
        kind=kind,
    )

    embed = build_artist_embed(
        artist_name=real_artist,
        kind=kind,
        page=0,
        sprite_items=sprite_items,
        splash_items=splash_items,
    )

    msg = await interaction.followup.send(embed=embed, view=view)
    view.message = msg

async def run_blocking(fn, *args, timeout: int = 60, **kwargs):
    return await asyncio.wait_for(asyncio.to_thread(fn, *args, **kwargs), timeout=timeout)


CATEGORY_CHOICES = ["Sprite", "Splash"]

def get_custom_emoji(bot: commands.Bot, emoji_name: str) -> str:
    """
    Returns the Discord representation of a custom emoji by name.
    Falls back to text if not found.
    """
    emoji = discord.utils.get(bot.emojis, name=emoji_name)
    return str(emoji) if emoji else f":{emoji_name}:"

async def retry_run_blocking(callable_fn, attempts: int = 3, base_delay: float = 1.0):
    last_exc = None
    for i in range(attempts):
        try:
            return await callable_fn()
        except (BrokenPipeError, ConnectionResetError, TimeoutError, OSError) as e:
            last_exc = e
            if isinstance(e, OSError) and e.errno not in (errno.EPIPE, errno.ECONNRESET, errno.ETIMEDOUT, None):
                raise
            await asyncio.sleep(base_delay * (2 ** i) + random.random())
    raise last_exc

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
    if not interaction.response.is_done():
        await interaction.response.defer(ephemeral=True)
    await interaction.followup.send(
        "Step 1/3: Validating submission…",
        ephemeral=True,
    )

    tmp_path: Optional[str] = None

    try:
        # --- 1) Enforce country must be from spreadsheet ---
        try:
            idx = await run_blocking(bot._load_index, timeout=30)  # AvailabilityIndex built from your sheet
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

        tmp_path = os.path.join(tempfile.gettempdir(), f"polandball_{uuid.uuid4()}{ext}")

        await image.save(tmp_path)

        service = interaction.client.drive_service
        discord_username = interaction.user.name

        await interaction.followup.send(
            "Step 2/3: Uploading PNG to Google Drive…",
            ephemeral=True,
        )

        try:
            async def do_upload():
                return await run_blocking(
                    upload_art_to_drive,
                    service,
                    tmp_path,
                    category=category.value,
                    country=country,
                    discord_username=discord_username,
                    artist_name=artist_name,
                    timeout=180,
                )

            drive_file, drive_path = await retry_run_blocking(do_upload)

            await interaction.followup.send(
                "Step 3/3: Finalizing Submission...",
                ephemeral=True,
            )

            fire_emoji = get_custom_emoji(bot, "PoleonFire")
            await interaction.followup.send(
                "✅ **Submission received!**\n\n"
                "Your art has been uploaded successfully.\n"
                f"You'll be contacted if any changes are needed. Thank you for helping bring Polandball Go to life! {fire_emoji}",
                ephemeral=True,
            )
            return

        finally:
            if tmp_path:
                try:
                    os.remove(tmp_path)
                except OSError:
                    pass



    except Exception as e:
        import traceback
        traceback.print_exc()  # shows full error in your bot logs/console

        await interaction.followup.send(
            f"❌ Something went wrong while uploading your art:\n`{type(e).__name__}: {str(e) or repr(e)}`",
            ephemeral=True,
        )


SPRITE_EXAMPLE_URL = "https://raw.githubusercontent.com/wwxiao09/polandball-art-helper/669d6100bce364b77d74b90885830fa85b6b0231/denmark.png"

SPLASH_EXAMPLE_URL = "https://raw.githubusercontent.com/wwxiao09/polandball-art-helper/669d6100bce364b77d74b90885830fa85b6b0231/Baekje.png"



@submit_art.autocomplete("country")
async def submit_art_country_autocomplete(interaction: discord.Interaction, current: str):
    try:
        # ✅ FAST PATH: if cache already exists, use it immediately
        if interaction.client._countries_cache:
            all_countries = interaction.client._countries_cache
        else:
            # kick off warmup but don't block autocomplete
            asyncio.create_task(interaction.client.get_country_names_cached())
            return []

        return [
            app_commands.Choice(name=c, value=c)
            for c in all_countries
            if current.lower() in c.lower()
        ][:25]
    except Exception:
        logger.exception("Autocomplete failed")
        return []


@bot.tree.command(
    name="help",
    description="Show all bot commands and Polandball art guidelines",
)
async def help_command(interaction: discord.Interaction):
    try:
        if not interaction.response.is_done():
            await interaction.response.defer(ephemeral=True, thinking=True)
    except discord.InteractionResponded:
        pass


    # --- Commands section ---
    commands_text = (
        "**/submit** – Submit art to Polandball Go\n"
        "• `category` – **Sprite** or **Splash**\n"
        "• `artist_name` – How you want to be credited in game\n"
        "• `country` – Pick from the autocomplete list (only countries from the game sheet)\n"
        "• `image` – **PNG only**\n\n"
        "**/available** `[character]`\n"
        "• No name → lists all characters that are available as sprites / splashes\n"
        "• With a name → shows if that character’s sprite/splash is available\n\n"
        "**/artist** `[name]`\n"
        "• Shows which characters a given artist has done (sprites & splashes)\n\n"
        "**/ping**\n"
        "• Quick check that the bot is alive (replies with `pong`)\n\n"
         "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
    )

    SPACER = "\u200b"

    embed = discord.Embed(
        title="Polandball Go Art Helper – Help",
        description=(
            "Here’s how to use the bot and how to contribute artwork to Polandball Go.\n"
            "You can submit either **Sprite Art**, **Splash Art**, or both."
        ),
        color=discord.Color.blurple(),
    )
    embed.add_field(name="**Commands**", value=commands_text, inline=False)

    # embed.add_field(name=SPACER, value=" ", inline=False)

    embed.add_field(
        name="🖌️ **Art Rules (Applies to ALL Art)**",
        value=(
            "• No eyelashes, hair, limbs, pupils, or mouths\n"
            "• No lines separating the flag colors\n"
            "• No circle, line, or shape tools of any kind\n"
            "• Everything must be hand-drawn\n"
            "⚠️ **Art that does not follow these rules may not be accepted.**\n\n"
             "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
        ),
        inline=False,
    )

    # embed.add_field(name=SPACER, value=" ", inline=False)

    embed.add_field(
        name="**1) Splash Art (Example Below)**",
        value=(
            "• Detailed illustrations, often with backgrounds or extra elements\n"
            "• Used in character screens\n"
            "• **Aspect ratio:** 3:2\n"
            "• Should primarily feature the main countryball\n"
            "• Other balls may appear as side characters\n"
            "• Avoid placing the main ball too close to the canvas edges\n\n"
             "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
        ),
        inline=False,
    )

    # embed.add_field(name=SPACER, value=" ", inline=False)

    embed.add_field(
        name="**2) Sprite Art (Example Below)**",
        value=(
            "• Simple, clean designs with no background\n"
            "• Less detailed than splash art (appears smaller in-game)\n"
            "• Too much detail may not be visible\n"
            "• **Aspect ratio:** 1:1\n"
            "• **Recommended canvas size:** 2500 × 2500\n"
            "• Sprite size should be proportional to the country\n"
            "  (e.g. San Marino smaller than the USA)\n"
            "• A subtle bottom shadow is **required**\n\n"
             "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
        ),
        inline=False,
    )

    # embed.add_field(name=SPACER, value=" ", inline=False)

    embed.add_field(
        name="📌 **Submitting Rules**",
        value=(
            "• Anyone may submit art for any country at any time\n"
            "• This includes countries that are already in-game\n"
            "• PBGO supports alternate character forms\n"
            "• Your submission may be used as an alternate form\n"
            "• **Submitting art does not guarantee it will be added to the game**\n\n"
            "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
        ),
        inline=False,
    )

    # embed.add_field(name=SPACER, value=" ", inline=False)

    embed.add_field(
        name="📩 **Support**",
        value="Contact <@1091755544177557626> for any bot-related questions.",
        inline=False,
    )

    embed.set_footer(
        text="Based on the r/Polandball “Académie Polandballaise” tutorial and community rules."
    )

    await interaction.followup.send(embed=embed, ephemeral=True)

    # --- Sprite Example (image + short description in same box) ---
    sprite_embed = discord.Embed(
        title="✅ Sprite Art — Good Example",
        description="Sprite art = the in-game character model (simple, clean, no background).",
        color=discord.Color.green(),
    )
    sprite_embed.set_image(url=SPRITE_EXAMPLE_URL)
    await interaction.followup.send(embed=sprite_embed, ephemeral=True)

    # --- Splash Example (image + short description in same box) ---
    splash_embed = discord.Embed(
        title="✅ Splash Art — Good Example",
        description="Splash art = detailed, stylized illustration for character screens.",
        color=discord.Color.orange(),
    )
    splash_embed.set_image(url=SPLASH_EXAMPLE_URL)
    await interaction.followup.send(embed=splash_embed, ephemeral=True)




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
"""
Discord Bot for Polandball Availability
======================================

Commands (prefix: !)
---------------------
1) !available ball
   → Replies with a comma-separated list of all available balls from your Google Sheet.

2) !available "Country X"
   → Replies with sprite/splash availability for that character.

Quick Start
-----------
1) Python 3.10+
2) pip install -r requirements.txt
3) Put your Discord bot token in the DISCORD_TOKEN env var.
4) On Cloud Run, attach a service account with Sheets+Drive read access.
5) Share your Google Sheet with that service account email.
6) Set these env vars:
   - GOOGLE_SHEET_ID = the Sheet ID from its URL
   - SHEET_NAME = the tab name (default: "Availability")
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
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

import discord
from discord.ext import commands

import gspread
from google.oauth2.service_account import Credentials
from google.auth import default as google_auth_default

DISCORD_TOKEN = os.getenv("DISCORD_TOKEN")
GOOGLE_SHEET_ID = os.getenv("GOOGLE_SHEET_ID")
SHEET_NAME = os.getenv("SHEET_NAME", "Characters")
AVAILABLE_VALUES = set(
    v.strip().lower()
    for v in os.getenv("AVAILABLE_VALUES", "").split(",")
    if v.strip()
)
UNAVAILABLE_VALUES = set(
    v.strip().lower()
    for v in os.getenv("UNAVAILABLE_VALUES", "").split(",")
    if v.strip()
)
CACHE_TTL_SECS = int(os.getenv("CACHE_TTL_SECS", "60"))

SERVICE_ACCOUNT_JSON = os.getenv("SERVICE_ACCOUNT_JSON")
SERVICE_ACCOUNT_FILE = os.getenv("SERVICE_ACCOUNT_FILE", "service_account.json")

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("polandball-bot")


@dataclass
class CountryRecord:
    country: str
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
                row[in_game_i].strip().lower()
                if in_game_i is not None and in_game_i < len(row)
                else ""
            )
            if in_game in UNAVAILABLE_VALUES:
                continue

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
        if q in self.by_norm:
            return self.by_norm[q], None
        candidates = difflib.get_close_matches(q, self.by_norm.keys(), n=1, cutoff=0.75)
        if candidates:
            best = candidates[0]
            suggestion = self.by_norm[best].country
            return None, suggestion
        return None, None


class PolandballBot(commands.Bot):
    def __init__(self):
        intents = discord.Intents.default()
        intents.message_content = True
        super().__init__(command_prefix="!", intents=intents, help_command=None)
        self.sheet_client: Optional[SheetClient] = None
        self.cache = Cache(ttl=CACHE_TTL_SECS)

    async def on_ready(self):
        logger.info("Logged in as %s (id=%s)", self.user, self.user.id)

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


@bot.command(name="available")
async def available(ctx: commands.Context, *args: str):
    try:
        idx = bot._load_index()
    except Exception as e:
        logger.exception("Sheet load failed")
        await ctx.reply(f"Sorry, I couldn't load the availability sheet: {e}")
        return

    if not args:
        await ctx.reply('Try `!available ball` or `!available "Country Name"`.')
        return

    arg_str = " ".join(args).strip()

    if arg_str.strip().lower() in {"ball", "balls"}:
        sprite_list = sorted(
            {r.country for r in idx.by_norm.values() if r.is_available("sprite") is True},
            key=str.lower,
        )
        splash_list = sorted(
            {r.country for r in idx.by_norm.values() if r.is_available("splash") is True},
            key=str.lower,
        )

        def fmt(lst):
            return "(none)" if not lst else ", ".join(lst)

        await ctx.reply(
            f"🎨 **Sprites available:** {fmt(sprite_list)}\n\n"
            f"🖼️ **Splash art available:** {fmt(splash_list)}"
        )
        return

    rec, suggestion = idx.find(arg_str)
    if rec:
        def label(available, artist, rdy):
            if available is True:
                return "✅ AVAILABLE"
            if available is False:
                rdy_status = "✅ Rdy" if rdy.lower() == "y" else "⏳ Not Rdy" if rdy else "❓ No status"
                return f"🎨 {artist} ({rdy_status})"
            return "⚠️ Unknown"

        s_sprite = rec.is_available("sprite")
        s_splash = rec.is_available("splash")

        await ctx.reply(
            f"**{rec.country}**\n"
            f"• Sprite: {label(s_sprite, rec.sprite_artist, rec.sprite_rdy)}\n"
            f"• Splash: {label(s_splash, rec.splash_artist, rec.splash_rdy)}"
        )
        return

    if suggestion:
        await ctx.reply(f"I couldn't find that exactly. Did you mean **{suggestion}**?")
    else:
        await ctx.reply("I couldn't find that country in the sheet.")


@bot.command(name="ping")
async def ping(ctx: commands.Context):
    await ctx.reply("pong")


async def start_health_check_server():
    async def handle_client(reader, writer):
        try:
            await reader.readexactly(1)
            response = b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nOK"
            writer.write(response)
            await writer.drain()
        except asyncio.IncompleteReadError:
            pass
        finally:
            writer.close()
            await writer.wait_closed()

    port = int(os.getenv("PORT", "8080"))
    server = await asyncio.start_server(handle_client, host="0.0.0.0", port=port)
    async with server:
        await server.serve_forever()


async def main():
    if not DISCORD_TOKEN:
        raise RuntimeError("DISCORD_TOKEN env var is required.")
    
    # Start health check server in background
    health_task = asyncio.create_task(start_health_check_server())
    
    # Start the Discord bot
    try:
        await bot.start(DISCORD_TOKEN)
    finally:
        health_task.cancel()


if __name__ == "__main__":
    asyncio.run(main())

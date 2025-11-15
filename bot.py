"""
Discord Bot for Polandball Availability
======================================

Commands (prefix: !)
---------------------
1) !available ball
   → Replies with a comma‑separated list of all *available* balls from your Google Sheet.

2) !available "Country X"
   → Replies "Available" or "Not available" for the requested country (case‑insensitive; supports close matches).

Quick Start
-----------
1) Python 3.10+
2) pip install -r requirements.txt
3) Put your Discord bot token in the DISCORD_TOKEN env var.
4) Create a Google Cloud service account with Google Sheets API enabled.
5) Download the JSON key as service_account.json (same folder) **and** share your Google Sheet with the service account email.
6) Set these env vars:
   - GOOGLE_SHEET_ID = the Sheet ID from its URL
   - SHEET_NAME = the tab name (default: "Availability")
   - COUNTRY_COLUMN = header text for country column (default: "Country")
   - STATUS_COLUMN  = header text for status column (default: "Status")
   - AVAILABLE_VALUES = comma‑separated values considered available (default: "available,open,true,yes")
   - UNAVAILABLE_VALUES = comma‑separated values considered unavailable (default: "unavailable,claimed,taken,false,no")

Example layout (first row is headers):
--------------------------------------
| Country | Status     |
|---------|------------|
| France  | Available  |
| Spain   | Claimed    |

Run
---
$ python bot.py

Notes
-----
- Results are cached in memory for ~60 seconds to reduce API calls.
- Country matching is case‑insensitive and trims words like "ball" and punctuation.
- Fuzzy matching (difflib) suggests the closest country if there’s no exact match.

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


# Google Sheets
import gspread
from google.oauth2.service_account import Credentials
from google.auth import default as google_auth_default

# -----------------------------
# Configuration & Environment
# -----------------------------
DISCORD_TOKEN = os.getenv("DISCORD_TOKEN")
GOOGLE_SHEET_ID = os.getenv("GOOGLE_SHEET_ID")
SHEET_NAME = os.getenv("SHEET_NAME", "Availability")
COUNTRY_COLUMN = os.getenv("COUNTRY_COLUMN", "Country").strip()
STATUS_COLUMN = os.getenv("STATUS_COLUMN", "Status").strip()
AVAILABLE_VALUES = set(v.strip().lower() for v in os.getenv("AVAILABLE_VALUES", "available,open,true,yes").split(","))
UNAVAILABLE_VALUES = set(v.strip().lower() for v in os.getenv("UNAVAILABLE_VALUES", "unavailable,claimed,taken,false,no").split(","))
CACHE_TTL_SECS = int(os.getenv("CACHE_TTL_SECS", "60"))

# If you prefer embedding credentials via env var:
#   SERVICE_ACCOUNT_JSON env var may contain the raw JSON string.
SERVICE_ACCOUNT_JSON = os.getenv("SERVICE_ACCOUNT_JSON")
SERVICE_ACCOUNT_FILE = os.getenv("SERVICE_ACCOUNT_FILE", "service_account.json")

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("polandball-bot")

# -----------------------------
# Google Sheets Client
# -----------------------------
@dataclass
class CountryRecord:
    country: str
    splash_raw: str
    sprite_raw: str

    def _parse(self, raw: str) -> Optional[bool]:
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
            return self._parse(self.splash_raw)
        if kind == "sprite":
            return self._parse(self.sprite_raw)
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
            # Running on Cloud Run → use ADC (service account attached to service)
            creds, _ = google_auth_default(scopes=scopes)

        self.gc = gspread.authorize(creds)
        if not GOOGLE_SHEET_ID:
            raise RuntimeError("GOOGLE_SHEET_ID env var is required.")
        self.sheet = self.gc.open_by_key(GOOGLE_SHEET_ID).worksheet(SHEET_NAME)
        logger.info("Connected to Google Sheet '%s' tab '%s'", GOOGLE_SHEET_ID, SHEET_NAME)

    def fetch_records(self) -> List[CountryRecord]:
        # Read raw grid; ignore headers so duplicates don't matter
        values = self.sheet.get_all_values()  # 2D list

        def col_letter_to_index(letter: str):
            letter = (letter or "").strip()
            if not letter or not letter.isalpha():
                return None
            idx = 0
            for ch in letter.upper():
                idx = idx * 26 + (ord(ch) - 64)
            return idx - 1  # zero-based

        ci = col_letter_to_index("A")  # Polandball (country name)
        ki = col_letter_to_index("K")  # Splash Artist Status
        li = col_letter_to_index("L")  # Sprite Artist Status

        records: List[CountryRecord] = []
        # assume first row is headers; start from row 2
        for row in values[1:]:
            country = row[ci].strip() if ci is not None and ci < len(row) else ""
            splash  = row[ki].strip() if ki is not None and ki < len(row) else ""
            sprite  = row[li].strip() if li is not None and li < len(row) else ""
            if country:
                records.append(CountryRecord(country=country, splash_raw=splash, sprite_raw=sprite))
        return records


# -----------------------------
# Caching Layer
# -----------------------------
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

# -----------------------------
# Utility Functions
# -----------------------------
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
        # Fuzzy suggest
        candidates = difflib.get_close_matches(q, self.by_norm.keys(), n=1, cutoff=0.75)
        if candidates:
            best = candidates[0]
            suggestion = self.by_norm[best].country
            return None, suggestion
        return None, None

# -----------------------------
# Bot Implementation
# -----------------------------
class PolandballBot(commands.Bot):
    def __init__(self):
        intents = discord.Intents.default()
        intents.message_content = True
        super().__init__(command_prefix="!", intents=intents, help_command=None)
        self.sheet_client: Optional[SheetClient] = None
        self.cache = Cache(ttl=CACHE_TTL_SECS)

    async def on_ready(self):        logger.info("Logged in as %s (id=%s)", self.user, self.user.id)

    # Internal: load + index
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

# -----------------------------
# Commands
# -----------------------------
@bot.command(name="available")
async def available(ctx: commands.Context, *args: str):
    """
    Usage:
      !available ball                  → lists Sprite-available and Splash-available separately
      !available "Country X"          → shows Sprite and Splash status for that country
    """
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

    # Mode 1: list all (separate sprite/splash)
    if arg_str.strip().lower() in {"ball", "balls"}:
        sprite_list = sorted(
            {r.country for r in idx.by_norm.values() if r.is_available("sprite") is True},
            key=str.lower
        )
        splash_list = sorted(
            {r.country for r in idx.by_norm.values() if r.is_available("splash") is True},
            key=str.lower
        )

        def fmt(lst): 
            return "(none)" if not lst else ", ".join(lst)

        await ctx.reply(
            f"🎨 **Sprites available:** {fmt(sprite_list)}\n\n"
            f"🖼️ **Splash art available:** {fmt(splash_list)}"
        )
        return

    # Mode 2: check one country (show both statuses)
    rec, suggestion = idx.find(arg_str)
    if rec:
        def label(v, raw):
            if v is True: return "✅ AVAILABLE"
            if v is False: return "❌ NOT available"
            return f"⚠️ Unknown (`{raw}`)"

        s_sprite = rec.is_available("sprite")
        s_splash = rec.is_available("splash")

        await ctx.reply(
            f"**{rec.country}**\n"
            f"• Sprite: {label(s_sprite, rec.sprite_raw)}\n"
            f"• Splash: {label(s_splash, rec.splash_raw)}"
        )
        return

    if suggestion:
        await ctx.reply(f"I couldn't find that exactly. Did you mean **{suggestion}**?")
    else:
        await ctx.reply("I couldn't find that country in the sheet.")

# Optional: simple ping
@bot.command(name="ping")
async def ping(ctx: commands.Context):
    await ctx.reply("pong")

if __name__ == "__main__":
    if not DISCORD_TOKEN:
        raise RuntimeError("DISCORD_TOKEN env var is required.")
    bot.run(DISCORD_TOKEN)

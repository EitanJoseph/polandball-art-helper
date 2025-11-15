# Polandball Art Helper

A Discord bot for the **Polandball Go** project that checks sprite and splash art availability from a Google Sheet.

## Features

- Query available characters: `!available ball`
- Check specific character status: `!available "Character Name"`
- Shows artist assignments and ready status for in-progress work

## Deployment

This bot runs on **Google Cloud Run** with automatic deployment:

- Push to `main` branch → automatically deploys to production
- Requires `DISCORD_TOKEN` and `GOOGLE_SHEET_ID` environment variables

## Setup

1. Install dependencies: `pip install -r requirements.txt`
2. Set environment variables for Discord token, Google Sheet ID, and service account
3. Deploy to Cloud Run or run locally

Part of the **Polandball Go** Discord project.

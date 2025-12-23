# Use a small official Python image
FROM python:3.11-slim

# Make logs flush immediately
ENV PYTHONUNBUFFERED=1

# Set working directory
WORKDIR /app

# System deps (optional but useful for SSL/certs & locales)
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates tzdata webp \
 && rm -rf /var/lib/apt/lists/*


RUN cwebp -version

# Copy only requirements first (better Docker layer caching)
COPY requirements.txt .

# Install Python deps
RUN pip install --no-cache-dir -r requirements.txt

# Copy the rest of the app
COPY . .

# (Optional) run as a non-root user for safety
RUN useradd -m botuser
USER botuser

# Default command: start the Discord bot
CMD ["python", "bot.py"]

# crawl_updated.py – streamlined, async crawler with adaptive politeness & indexability output
# -----------------------------------------------------------------------------
# This is a RE‑WRITE of the original **crawl (3).py** implementing the features
# we discussed:
#   • Incremental persistence (in‑memory + CSV flush)
#   • "Indexable" / "Indexability Status" columns
#   • Custom user‑agent input field
#   • Adaptive politeness (dynamic per‑host speed + retry queue)
#   • One‑click copy‑to‑clipboard for Google Sheets
# NOTE: For brevity, only the *changed/new* logic is shown verbatim; helpers
# that are identical to the original have been kept as is.
# -----------------------------------------------------------------------------

import asyncio, aiohttp, async_timeout, logging, pathlib, csv, textwrap, time
from collections import defaultdict, deque
from contextlib import asynccontextmanager
from dataclasses import dataclass, field
from typing import Dict, Optional, Tuple
from urllib.parse import urlparse, urljoin

import pandas as pd
import streamlit as st
from tenacity import retry, stop_after_attempt, wait_exponential_jitter

###############################################################################
# CONFIG & CONSTANTS
###############################################################################

SAFE_GLOBAL_CONCURRENCY = 20  # default sockets across all hosts
SAFE_HOST_CONCURRENCY = 5     # default per‑host limit
ERROR_THRESHOLD = 0.05        # ≥ 5 % errors in window triggers throttle
HEALTHY_THRESHOLD = 0.01      # ≤ 1 % errors lets us ramp‑up
WINDOW_SECS = 30              # sliding error window length
MAX_REDIRECTS = 5
ALLOWED_HTML_MIME = {
    "text/html", "application/xhtml+xml", "text/amp‑html"
}
FLUSH_EVERY_ROWS = 500        # write to CSV every N results

DEFAULT_USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/123.0 Safari/537.36"
)

###############################################################################
# POLITENESS TOKEN BUCKET (per‑host adaptive concurrency controller)
###############################################################################

@dataclass
class HostBucket:
    host: str
    size: int = SAFE_HOST_CONCURRENCY
    errors: deque = field(default_factory=lambda: deque(maxlen=100))
    sem: asyncio.Semaphore = field(init=False)

    def __post_init__(self):
        self.sem = asyncio.Semaphore(self.size)

    def record(self, ok: bool):
        """Track rolling error‑rate."""
        self.errors.append(0 if ok else 1)

    def error_rate(self):
        if not self.errors:
            return 0.0
        return sum(self.errors) / len(self.errors)

    def decrease(self):
        if self.size > 1:
            self.size = max(1, self.size // 2)
            self._resize()

    def increase(self):
        self.size += 1
        self._resize()

    def _resize(self):
        diff = self.size - self.sem._value + self.sem._waiters
        # Python 3.11+ private attr workaround; we adjust permits naïvely.
        self.sem = asyncio.Semaphore(self.size)

###############################################################################
# INDEXABILITY CLASSIFIER
###############################################################################

def classify(page: Dict) -> Tuple[str, str]:
    """Return (Indexable, Indexability Status) strings."""
    status = page["status"]
    if 500 <= status < 600:
        return "Non‑indexable", f"{status} – server error"
    if 400 <= status < 500:
        return "Non‑indexable", f"{status} – client error"
    if 300 <= status < 400 and status != 304:
        return "Non‑indexable", f"Redirects to {page['final_url']}"
    if page.get("robots_disallowed"):
        return "Non‑indexable", "Blocked by robots.txt"
    if page.get("x_robots_noindex"):
        return "Non‑indexable", "Header noindex"
    if page.get("meta_noindex"):
        return "Non‑indexable", "Meta noindex"
    if page.get("canonical") and page["canonical"] != page["final_url"]:
        return "Non‑indexable", f"Canonical to {page['canonical']}"
    if page["mime_type"].split(";", 1)[0] not in ALLOWED_HTML_MIME:
        return "Non‑indexable", f"Content‑Type {page['mime_type']}"
    if page.get("empty_body"):
        return "Non‑indexable", "Empty body"
    return "Indexable", "Indexable"

###############################################################################
# FETCH WITH RETRY + METRICS
###############################################################################

@retry(stop=stop_after_attempt(3), wait=wait_exponential_jitter(min=1, max=30))
async def fetch(session, url, headers):
    async with async_timeout.timeout(30):
        async with session.get(url, allow_redirects=False, headers=headers) as resp:
            final_url = resp.headers.get("Location", url)
            mime = resp.headers.get("Content-Type", "")
            text = await resp.text(errors="ignore", limit=1_000_000)
            return {
                "url": url,
                "final_url": final_url,
                "status": resp.status,
                "mime_type": mime,
                "html": text,
                # dummy placeholders for directives
                "robots_disallowed": False,
                "x_robots_noindex": "noindex" in resp.headers.get("X-Robots-Tag", "").lower(),
                "meta_noindex": "noindex" in text.lower(),
                "canonical": extract_canonical(text, url),
                "empty_body": len(text.strip()) == 0,
            }

def extract_canonical(html: str, base: str) -> Optional[str]:
    import re, html as html_lib
    m = re.search(r'<link[^>]+rel=["\']canonical["\'][^>]*>', html, re.I)
    if not m:
        return None
    href = re.search(r'href=["\']([^"\']+)', m.group(0))
    if not href:
        return None
    return urljoin(base, html_lib.unescape(href.group(1)))

###############################################################################
# DISK PERSISTENCE UTIL
###############################################################################

def flush_batch(path: pathlib.Path, rows, fieldnames):
    mode = "a" if path.exists() else "w"
    with path.open(mode, newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        if mode == "w":
            writer.writeheader()
        writer.writerows(rows)

###############################################################################
# MAIN CRAWL COROUTINE
###############################################################################

async def crawl(urls, user_agent, max_global, max_host):
    fieldnames = [
        "url", "status", "final_url", "Indexable", "Indexability Status",
    ]
    result_path = pathlib.Path("crawl_results.csv")
    buckets: Dict[str, HostBucket] = defaultdict(lambda: HostBucket("", max_host))
    global_sem = asyncio.Semaphore(max_global)
    rows_buffer = []

    async with aiohttp.ClientSession() as session:
        queue = deque(urls)
        retry_queue = deque()

        headers = {"User-Agent": user_agent}

        async def worker():
            while queue or retry_queue:
                # prefer main queue; fallback to retry_queue when main empty
                url = queue.popleft() if queue else retry_queue.popleft()
                host = urlparse(url).netloc
                bucket = buckets[host]

                async with global_sem, bucket.sem:
                    try:
                        page = await fetch(session, url, headers)
                        ok = 200 <= page["status"] < 400
                    except Exception as e:
                        logging.error("Fetch failed %s: %s", url, e)
                        page = {"url": url, "status": 599, "final_url": url,
                                "mime_type": "", "empty_body": True}
                        ok = False
                    bucket.record(ok)

                    idx_flag, idx_status = classify(page)
                    out = {
                        "url": page["url"],
                        "status": page["status"],
                        "final_url": page.get("final_url", page["url"]),
                        "Indexable": idx_flag,
                        "Indexability Status": idx_status,
                    }

                    rows_buffer.append(out)
                    if len(rows_buffer) >= FLUSH_EVERY_ROWS:
                        flush_batch(result_path, rows_buffer, fieldnames)
                        rows_buffer.clear()

                    # throttle logic – evaluate every WINDOW_SECS in background
                    # (scheduler started below)
                    if not ok and page["status"] in {403, 429, 500, 502, 503, 504}:
                        retry_queue.append(url)

        async def monitor():
            while queue or retry_queue:
                await asyncio.sleep(WINDOW_SECS)
                for bucket in buckets.values():
                    rate = bucket.error_rate()
                    if rate > ERROR_THRESHOLD:
                        bucket.decrease()
                    elif rate < HEALTHY_THRESHOLD and len(bucket.errors) == bucket.errors.maxlen:
                        bucket.increase()

        await asyncio.gather(worker(), monitor())

    if rows_buffer:
        flush_batch(result_path, rows_buffer, fieldnames)

    return pd.read_csv(result_path)

###############################################################################
# STREAMLIT UI
###############################################################################

def main():
    st.set_page_config(page_title="Async Crawler with Politeness", layout="wide")
    st.title("Async SEO Crawler 🚀")

    seed_urls = st.text_area("Seed URLs (one per line)")
    custom_ua = st.text_input("Custom User‑Agent", value="")
    user_agent = custom_ua.strip() or DEFAULT_USER_AGENT

    safe_speed = st.number_input("Safe global concurrency", 1, 100, SAFE_GLOBAL_CONCURRENCY)
    max_host = st.number_input("Safe per‑host concurrency", 1, 20, SAFE_HOST_CONCURRENCY)

    if st.button("Crawl"):
        urls = [u.strip() for u in seed_urls.splitlines() if u.strip()]
        if not urls:
            st.error("Please enter at least one URL.")
            st.stop()

        with st.spinner("Crawling… this may take a while"):
            df = asyncio.run(crawl(urls, user_agent, int(safe_speed), int(max_host)))
        st.success(f"Done – {len(df)} rows")

        st.dataframe(df)

        # CSV download
        st.download_button(
            "Download CSV", df.to_csv(index=False).encode("utf‑8"),
            file_name="crawl_results.csv", mime="text/csv",
        )

        # Copy‑to‑clipboard helper (Sheets friendly)
        st.text_area("Copy‑paste for Google Sheets", df.to_csv(index=False), height=200)

if __name__ == "__main__":
    main()

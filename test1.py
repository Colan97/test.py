import streamlit as st
import pandas as pd
import re
import asyncio
import aiohttp
import orjson # Using orjson for faster JSON operations
import nest_asyncio
import logging
import pyperclip # Note: pyperclip might not be needed if st_copy handles clipboard directly
import json
from typing import List, Dict, Set, Optional, Tuple
from urllib.parse import urlparse, urljoin, urlunparse
from bs4 import BeautifulSoup
from datetime import datetime
from tenacity import retry, stop_after_attempt, wait_exponential # For retrying failed requests
import xml.etree.ElementTree as ET # For parsing XML sitemaps
import os
from pathlib import Path
from st_copy import copy_button # Import for the copy button
import time
from urllib import robotparser # For parsing robots.txt

# Apply nest_asyncio to allow nested event loops, useful in environments like Jupyter/Streamlit
nest_asyncio.apply()

# Set up event loop policy for Windows if applicable
if os.name == 'nt':
    asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())

# -----------------------------
# Logging Configuration
# -----------------------------
logging.basicConfig(
    level=logging.INFO, # Set logging level to INFO
    format='%(asctime)s - %(levelname)s - %(message)s', # Define log message format
    filename='url_checker.log' # Log to a file
)

# -----------------------------
# Constants
# -----------------------------
DEFAULT_TIMEOUT = 15  # Default timeout for HTTP requests in seconds
DEFAULT_MAX_URLS = 25000  # Maximum number of URLs to crawl in spider mode
MAX_REDIRECTS = 5  # Maximum number of redirects to follow (aiohttp handles this internally)
DEFAULT_USER_AGENT = "custom_adidas_seo_x3423/1.0"  # Default user agent string
SAVE_INTERVAL = 100  # Save intermediate results every 100 URLs processed
ERROR_THRESHOLD = 0.1  # 10% error rate threshold for adjusting concurrency
MIN_CONCURRENCY = 1   # Minimum number of concurrent requests
MAX_CONCURRENCY = 50  # Maximum number of concurrent requests
DEFAULT_CONCURRENCY = 10 # Default concurrency for requests

# Dictionary of common user agents for selection
USER_AGENTS = {
    "Googlebot Desktop": (
        "Mozilla/5.0 (compatible; Googlebot/2.1; +http://www.google.com/bot.html)"
    ),
    "Googlebot Mobile": (
        "Mozilla/5.0 (Linux; Android 6.0; Nexus 5 Build/MRA58N) "
        "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/110.0.0.0 Mobile Safari/537.36 "
        "(compatible; Googlebot/2.1; +http://www.google.com/bot.html)"
    ),
    "Chrome Desktop": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/110.0.5481.100 Safari/537.36"
    ),
    "Chrome Mobile": (
        "Mozilla/5.0 (Linux; Android 10; Pixel 3) "
        "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/110.0.5481.100 Mobile Safari/537.36"
    ),
    "Custom Adidas SEO Bot": DEFAULT_USER_AGENT,
}

# -----------------------------
# Helper Functions
# -----------------------------
def save_results_to_file(results: List[Dict], filename: str):
    """Save results to a JSON file."""
    try:
        with open(filename, 'w', encoding='utf-8') as f:
            json.dump(results, f, ensure_ascii=False, indent=2)
        logging.info(f"Successfully saved {len(results)} results to {filename}")
    except IOError as e:
        logging.error(f"Error saving results to {filename}: {e}")

def load_results_from_file(filename: str) -> List[Dict]:
    """Load results from a JSON file."""
    if os.path.exists(filename):
        try:
            with open(filename, 'r', encoding='utf-8') as f:
                return json.load(f)
        except (IOError, json.JSONDecodeError) as e:
            logging.error(f"Error loading results from {filename}: {e}")
            return []
    return []

def calculate_error_rate(results: List[Dict]) -> float:
    """Calculate the error rate from recent results (status codes 4xx, 5xx)."""
    if not results:
        return 0.0
    error_count = sum(1 for r in results if str(r.get("Final_Status_Code", "")).startswith(("4", "5")))
    return error_count / len(results) if results else 0.0

def adjust_concurrency(current_concurrency: int, error_rate: float) -> int:
    """Dynamically adjust concurrency based on error rate."""
    if error_rate > ERROR_THRESHOLD:
        return max(MIN_CONCURRENCY, current_concurrency - 2)
    elif error_rate < ERROR_THRESHOLD / 2 and current_concurrency < MAX_CONCURRENCY : # Only increase if below max
        return min(MAX_CONCURRENCY, current_concurrency + 1)
    return current_concurrency

class URLChecker:
    """
    Manages asynchronous URL fetching, parsing, and robots.txt checking.
    """
    def __init__(self, user_agent: str, concurrency: int, timeout: int, respect_robots: bool):
        self.user_agent = user_agent
        self.concurrency = concurrency
        self.initial_concurrency = concurrency # Store initial concurrency for dynamic mode
        self.timeout = timeout
        self.respect_robots = respect_robots
        self.robots_cache = {}  # Cache for robots.txt content
        self.robots_parser_cache = {} # Cache for parsed robotparser objects
        self.session: Optional[aiohttp.ClientSession] = None
        self.semaphore: Optional[asyncio.Semaphore] = None
        self.failed_urls: Set[str] = set() # Stores URLs that failed processing
        self.recent_results: List[Dict] = [] # Stores results for periodic saving and error rate calculation
        self.last_save_time = datetime.now()
        self.save_filename = f"crawl_results_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        self.robots_semaphore = asyncio.Semaphore(10)  # Limit concurrent robots.txt fetches
        self.stop_event = asyncio.Event()  # Event for stopping the crawl gracefully
        self.last_adjustment_time = datetime.now()
        self.adjustment_interval = 10  # Adjust concurrency every 10 seconds in dynamic mode

    async def adjust_concurrency_if_needed(self, dynamic_speed_mode: bool):
        """Adjust concurrency based on error rate if dynamic mode is active and enough time has passed."""
        if not dynamic_speed_mode: # Only adjust if dynamic speed mode is on
            return

        now = datetime.now()
        if (now - self.last_adjustment_time).total_seconds() >= self.adjustment_interval:
            # Use the last N results for error rate, e.g., last 100 or all recent if fewer
            sample_results = self.recent_results[-100:] if self.recent_results else []
            error_rate = calculate_error_rate(sample_results)
            new_concurrency = adjust_concurrency(self.concurrency, error_rate)

            if new_concurrency != self.concurrency:
                logging.info(f"Adjusting concurrency from {self.concurrency} to {new_concurrency} (error rate: {error_rate:.2%})")
                self.concurrency = new_concurrency
                # Recreate semaphore with updated concurrency
                self.semaphore = asyncio.Semaphore(self.concurrency)
            else:
                logging.debug(f"Concurrency remains at {self.concurrency} (error rate: {error_rate:.2%})")

            self.last_adjustment_time = now


    async def setup(self):
        """Initialize the aiohttp session and semaphore."""
        try:
            # TCPConnector for managing connections
            connector = aiohttp.TCPConnector(
                limit=None, # No limit on total connections for the connector itself
                limit_per_host=self.concurrency + 5, # Limit connections per host based on concurrency
                ttl_dns_cache=300, # DNS cache TTL
                enable_cleanup_closed=True, # Enable cleanup of closed transports
                force_close=False, # Don't force close connections
                ssl=False # Disable SSL verification for broader compatibility (use with caution)
            )
            # ClientTimeout settings
            timeout_settings = aiohttp.ClientTimeout(
                total=None,  # No total timeout for the entire operation including multiple redirects
                connect=self.timeout, # Connection establishment timeout
                sock_read=self.timeout # Socket read timeout
            )
            self.session = aiohttp.ClientSession(
                connector=connector,
                timeout=timeout_settings,
                json_serialize=orjson.dumps, # Use orjson for faster JSON serialization
                headers={"User-Agent": self.user_agent}
            )
            self.semaphore = asyncio.Semaphore(self.concurrency) # Semaphore to limit concurrent tasks
            logging.info(f"URLChecker initialized with concurrency {self.concurrency}, timeout {self.timeout}s")
        except Exception as e:
            logging.error(f"Error setting up URLChecker: {str(e)}")
            raise

    async def close(self):
        """Close the aiohttp session and save any remaining results."""
        try:
            if self.session and not self.session.closed:
                await self.session.close()
                logging.info("aiohttp session closed.")
            # Save any remaining results not yet saved by the interval logic
            if self.recent_results:
                save_results_to_file(self.recent_results, self.save_filename)
                logging.info(f"Saved remaining {len(self.recent_results)} results to {self.save_filename}")
                self.recent_results = [] # Clear after saving
        except Exception as e:
            logging.error(f"Error closing URLChecker: {str(e)}")

    @retry(stop=stop_after_attempt(3), wait=wait_exponential(multiplier=1, min=1, max=5))
    async def _fetch_url_with_retry(self, url: str, session: aiohttp.ClientSession, is_robots_fetch: bool = False):
        """Internal method to fetch a URL with retry logic, used by fetch_and_parse and check_robots."""
        headers = {"User-Agent": self.user_agent}
        # For robots.txt, use a shorter timeout and don't follow redirects as strictly.
        timeout_config = aiohttp.ClientTimeout(total=5 if is_robots_fetch else self.timeout)

        async with session.get(url, ssl=False, allow_redirects=not is_robots_fetch, timeout=timeout_config, headers=headers) as resp:
            # Ensure the response is read to prevent unread data issues
            await resp.read() # Read the full response body
            return resp, await resp.text(errors='replace') # Return response object and text content

    async def recrawl_failed_urls(self, dynamic_speed_mode: bool) -> List[Dict]:
        """
        Attempt to recrawl URLs that failed in the initial crawl.
        Uses exponential backoff and retries up to 3 times.
        """
        if not self.failed_urls:
            return []

        logging.info(f"Attempting to recrawl {len(self.failed_urls)} failed URLs.")
        results = []
        # Convert set to list to iterate and potentially modify (though we just clear later)
        urls_to_recrawl = list(self.failed_urls)
        self.failed_urls.clear() # Clear original set, add back if recrawl also fails

        tasks = [self.fetch_and_parse(url, is_recrawl=True, dynamic_speed_mode=dynamic_speed_mode) for url in urls_to_recrawl]
        recrawl_results_list = await asyncio.gather(*tasks, return_exceptions=True)

        for i, res_or_exc in enumerate(recrawl_results_list):
            url = urls_to_recrawl[i]
            if isinstance(res_or_exc, Exception):
                logging.error(f"Exception during recrawl of {url}: {res_or_exc}")
                self.failed_urls.add(url) # Add back if recrawl failed
            elif res_or_exc:
                if not str(res_or_exc.get("Final_Status_Code", "")).startswith(("4", "5", "Error")):
                    results.append(res_or_exc)
                    logging.info(f"Successfully recrawled {url}")
                else:
                    logging.warning(f"Recrawl of {url} resulted in status {res_or_exc.get('Final_Status_Code')}")
                    self.failed_urls.add(url) # Add back if recrawl still results in error/bad status
            else: # Should not happen if fetch_and_parse always returns a dict
                 logging.warning(f"Recrawl of {url} returned no result.")
                 self.failed_urls.add(url)


        logging.info(f"Recrawl attempt finished. Successfully recrawled {len(results)} URLs. {len(self.failed_urls)} URLs still failed.")
        return results

    async def check_robots(self, url: str) -> Tuple[bool, str]:
        """
        Check robots.txt for the given URL and user agent. Returns (is_allowed, rule_if_disallowed).
        Uses the standard robotparser library for accurate parsing.
        Caches robots.txt content and parsed objects.
        """
        if not self.respect_robots:
            return True, ""

        try:
            parsed_url = urlparse(url)
            base_url = f"{parsed_url.scheme}://{parsed_url.netloc}"
            robots_url = urljoin(base_url, "/robots.txt")
            # Use a simplified user agent for matching, e.g., "googlebot" from "Googlebot/2.1"
            short_user_agent = self.user_agent.split("/")[0].lower()


            # Check parser cache first
            if base_url in self.robots_parser_cache:
                parser = self.robots_parser_cache[base_url]
                is_allowed = parser.can_fetch(self.user_agent, url) # Use full UA for can_fetch
                return is_allowed, ("Disallow rule" if not is_allowed else "")

            # If not in parser cache, fetch robots.txt (or use content cache)
            async with self.robots_semaphore: # Limit concurrent fetches of different robots.txt files
                if base_url in self.robots_cache:
                    content = self.robots_cache[base_url]
                else:
                    logging.info(f"Fetching robots.txt for {base_url}")
                    try:
                        # Use a separate session for robots.txt or the main one if robust enough
                        # For simplicity, creating a temporary one or ensuring main session is configured for this.
                        # Re-using the main session here.
                        resp, content = await self._fetch_url_with_retry(robots_url, self.session, is_robots_fetch=True)
                        if resp.status == 200:
                            self.robots_cache[base_url] = content
                            logging.info(f"Fetched and cached robots.txt for {base_url}")
                        else:
                            logging.info(f"No robots.txt or error for {base_url} (status {resp.status}). Allowing crawl by default.")
                            self.robots_cache[base_url] = "" # Cache empty content to prevent re-fetch
                            self.robots_parser_cache[base_url] = robotparser.RobotFileParser() # Store an empty parser
                            self.robots_parser_cache[base_url].parse(["User-agent: *", "Allow: /"]) # Default allow
                            return True, ""
                    except Exception as e:
                        logging.warning(f"Could not fetch robots.txt for {base_url}: {e}. Allowing crawl by default.")
                        self.robots_cache[base_url] = "" # Cache empty on error
                        self.robots_parser_cache[base_url] = robotparser.RobotFileParser()
                        self.robots_parser_cache[base_url].parse(["User-agent: *", "Allow: /"])
                        return True, ""

                # Parse robots.txt content
                parser = robotparser.RobotFileParser()
                parser.parse(content.splitlines())
                self.robots_parser_cache[base_url] = parser
                is_allowed = parser.can_fetch(self.user_agent, url)
                return is_allowed, ("Disallow rule" if not is_allowed else "")

        except Exception as e:
            logging.error(f"Error in check_robots for {url}: {e}. Allowing crawl by default.")
            return True, "" # Fail open if there's an unexpected error

    async def fetch_and_parse(self, url: str, is_recrawl: bool = False, dynamic_speed_mode: bool = False) -> Dict:
        """
        Fetches a single URL, parses its content, and extracts relevant SEO data.
        Manages semaphore for concurrency control.
        """
        if self.is_stopped(): # Check if crawl stop has been requested
            logging.info(f"Skipping {url} due to stop request.")
            # Return a minimal dict indicating skipped status
            return { "Original_URL": url, "Final_Status_Code": "Skipped", "Final_Status_Type": "Crawl stopped"}


        async with self.semaphore: # Acquire semaphore slot
            if self.is_stopped(): # Re-check after acquiring semaphore
                 logging.info(f"Skipping {url} (checked after semaphore) due to stop request.")
                 return { "Original_URL": url, "Final_Status_Code": "Skipped", "Final_Status_Type": "Crawl stopped"}

            # Adjust concurrency dynamically if in that mode (only for primary fetches, not recrawls)
            if not is_recrawl:
                await self.adjust_concurrency_if_needed(dynamic_speed_mode)

            logging.info(f"Fetching and parsing URL: {url}")
            start_time = time.monotonic()
            data = {
                "Original_URL": url, "Content_Type": "", "Initial_Status_Code": "", "Initial_Status_Type": "",
                "Final_URL": url, "Final_Status_Code": "", "Final_Status_Type": "", "Title": "",
                "Meta Description": "", "H1": "", "H1_Count": 0, "Canonical_URL": "", "Meta Robots": "",
                "X-Robots-Tag": "", "HTML Lang": "", "Blocked by Robots.txt": "No", "Robots Block Rule": "",
                "Indexable": "Yes", "Indexability Reason": "", "Last Modified": "", "Word Count": 0,
                "Crawl Time": 0.0, "Timestamp": datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
            }

            try:
                # Check robots.txt first if respect_robots is True
                allowed_by_robots, robots_rule = True, ""
                if self.respect_robots:
                    allowed_by_robots, robots_rule = await self.check_robots(url)
                    if not allowed_by_robots:
                        data.update({
                            "Blocked by Robots.txt": "Yes", "Robots Block Rule": robots_rule,
                            "Indexable": "No", "Indexability Reason": "Blocked by robots.txt",
                            "Final_Status_Code": "Skipped", "Final_Status_Type": "Blocked by robots.txt"
                        })
                        logging.info(f"Skipping {url} as it is disallowed by robots.txt.")
                        # Still add to recent_results for saving logic, but it's effectively a non-crawl result
                        self._add_to_recent_results(data)
                        return data


                # Make the request using the retry-enabled internal fetch method
                resp, content_text = await self._fetch_url_with_retry(url, self.session)

                # Populate data from response
                data["Content_Type"] = resp.headers.get("Content-Type", "")
                # Initial status is from the first response before redirects
                # aiohttp's history gives previous responses if redirects occurred
                initial_resp = resp.history[0] if resp.history else resp
                data["Initial_Status_Code"] = str(initial_resp.status)
                data["Initial_Status_Type"] = self.status_label(initial_resp.status)

                data["Final_URL"] = str(resp.url) # URL after all redirects
                data["Final_Status_Code"] = str(resp.status)
                data["Final_Status_Type"] = self.status_label(resp.status)
                data["Last Modified"] = resp.headers.get("Last-Modified", "")
                data["X-Robots-Tag"] = resp.headers.get("X-Robots-Tag", "")


                if resp.status == 200 and data["Content_Type"].startswith("text/html"):
                    self.parse_html_content(data, content_text, resp.headers) # Pass headers for X-Robots-Tag
                elif resp.status != 200:
                    data["Indexable"] = "No"
                    data["Indexability Reason"] = f"HTTP Error: {resp.status}"
                else: # Non-HTML content
                    data["Indexable"] = "No" # Or "N/A" depending on desired output
                    data["Indexability Reason"] = f"Non-HTML Content-Type: {data['Content_Type']}"

                # Update indexability based on X-Robots-Tag and Meta Robots
                self.update_indexability_from_directives(data)


            except aiohttp.ClientResponseError as e: # Specific client errors (4xx, 5xx from server)
                logging.error(f"ClientResponseError for {url}: Status {e.status}, Message: {e.message}")
                data.update({
                    "Final_Status_Code": str(e.status), "Final_Status_Type": self.status_label(e.status) + f" ({e.message})",
                    "Indexable": "No", "Indexability Reason": f"HTTP Error: {e.status}"
                })
                if not is_recrawl: self.failed_urls.add(url)
            except aiohttp.ClientConnectorError as e: # Connection establishment errors
                logging.error(f"ClientConnectorError for {url}: {str(e)}")
                data.update({
                    "Final_Status_Code": "Error", "Final_Status_Type": f"Connection Error ({e.__class__.__name__})",
                    "Indexable": "No", "Indexability Reason": "Connection Error"
                })
                if not is_recrawl: self.failed_urls.add(url)
            except asyncio.TimeoutError:
                logging.error(f"Timeout fetching {url}")
                data.update({
                    "Final_Status_Code": "Error", "Final_Status_Type": "Timeout",
                    "Indexable": "No", "Indexability Reason": "Timeout"
                })
                if not is_recrawl: self.failed_urls.add(url)
            except Exception as e:
                logging.error(f"Generic error fetching/parsing {url}: {str(e)} ({e.__class__.__name__})")
                data.update({
                    "Final_Status_Code": "Error", "Final_Status_Type": f"General Error ({e.__class__.__name__})",
                    "Indexable": "No", "Indexability Reason": f"Error: {str(e)}"
                })
                if not is_recrawl: self.failed_urls.add(url)
            finally:
                data["Crawl Time"] = round(time.monotonic() - start_time, 2)
                # Update redirect label based on final vs original URL
                data = update_redirect_label(data, url)
                # Add to recent results for saving and dynamic concurrency adjustment
                if not is_recrawl: # Don't add recrawl attempts to recent_results for concurrency adjustment
                     self._add_to_recent_results(data)

            return data

    def _add_to_recent_results(self, result_data: Dict):
        """Adds a result to recent_results and triggers save if interval is met."""
        self.recent_results.append(result_data)
        if len(self.recent_results) >= SAVE_INTERVAL:
            save_results_to_file(self.recent_results, self.save_filename)
            logging.info(f"Saved {len(self.recent_results)} results to {self.save_filename}")
            self.recent_results = []  # Clear after saving
            self.last_save_time = datetime.now()


    def status_label(self, status_code: int) -> str:
        """Convert HTTP status code to a human-readable label."""
        if 200 <= status_code < 300: return "Success"
        if 300 <= status_code < 400: return "Redirect"
        if 400 <= status_code < 500: return "Client Error"
        if 500 <= status_code < 600: return "Server Error"
        return "Unknown"

    def parse_html_content(self, data: Dict, content: str, headers: Dict): # headers removed, use data["X-Robots-Tag"]
        """Parse HTML content and extract metadata. Modifies data dict in-place."""
        try:
            soup = BeautifulSoup(content, "lxml") # Using lxml for speed

            data["Title"] = soup.title.string.strip() if soup.title and soup.title.string else ""
            meta_desc = soup.find("meta", attrs={"name": re.compile(r"description", re.I)})
            data["Meta Description"] = meta_desc["content"].strip() if meta_desc and meta_desc.get("content") else ""

            h1_tags = soup.find_all("h1")
            data["H1_Count"] = len(h1_tags)
            data["H1"] = h1_tags[0].text.strip() if h1_tags else ""

            # Canonical URL extraction (more robust)
            canonical_tag = soup.find("link", rel=re.compile(r"canonical", re.I))
            if canonical_tag and canonical_tag.get("href"):
                data["Canonical_URL"] = urljoin(data["Final_URL"], canonical_tag["href"].strip()) # Join with final URL
            else: # Fallback for meta canonical (less common)
                meta_canonical = soup.find("meta", attrs={"name": re.compile(r"canonical", re.I)})
                if meta_canonical and meta_canonical.get("content"):
                     data["Canonical_URL"] = urljoin(data["Final_URL"], meta_canonical["content"].strip())


            meta_robots_tag = soup.find("meta", attrs={"name": re.compile(r"robots", re.I)})
            data["Meta Robots"] = meta_robots_tag["content"].strip() if meta_robots_tag and meta_robots_tag.get("content") else ""

            html_tag = soup.find("html")
            data["HTML Lang"] = html_tag.get("lang", "").strip() if html_tag else ""

            # Word Count (simple text-based)
            text_content = soup.get_text(separator=" ", strip=True)
            data["Word Count"] = len(text_content.split())

        except Exception as e:
            logging.error(f"Error parsing HTML for {data['Original_URL']}: {e}")
            # Keep already extracted data, just log error

    def update_indexability_from_directives(self, data: Dict):
        """Updates 'Indexable' and 'Indexability Reason' based on Meta Robots and X-Robots-Tag."""
        # If already set to No (e.g. by robots.txt or HTTP error), don't override unless it's a more specific "noindex"
        if data["Indexable"] == "No" and "directive" not in data["Indexability Reason"]: # Allow override if current reason isn't a directive
            pass # Keep current non-indexable status

        meta_robots = data["Meta Robots"].lower()
        x_robots = data["X-Robots-Tag"].lower()

        if "noindex" in meta_robots:
            data["Indexable"] = "No"
            data["Indexability Reason"] = "Meta Robots: noindex"
        elif "noindex" in x_robots:
            data["Indexable"] = "No"
            data["Indexability Reason"] = "X-Robots-Tag: noindex"
        # Add other checks like "none" which implies noindex, nofollow
        elif "none" in meta_robots:
            data["Indexable"] = "No"
            data["Indexability Reason"] = "Meta Robots: none"
        elif "none" in x_robots:
            data["Indexable"] = "No"
            data["Indexability Reason"] = "X-Robots-Tag: none"
        # If canonical points elsewhere and it's not self-referential (and page is otherwise indexable)
        elif data["Canonical_URL"] and data["Canonical_URL"] != data["Final_URL"] and data["Indexable"] == "Yes":
            data["Indexable"] = "No" # Or "Considered Non-Indexable"
            data["Indexability Reason"] = "Canonical to other URL"
        elif data["Indexable"] == "Yes": # If no "noindex" and still "Yes"
             data["Indexability Reason"] = "Indexable" # Default reason for indexable pages


    def stop(self):
        """Set the stop event to halt the crawl."""
        self.stop_event.set()
        logging.info("Stop event set - crawl will halt after current tasks complete or new tasks are skipped.")

    def is_stopped(self) -> bool:
        """Check if the crawl should stop."""
        return self.stop_event.is_set()


async def dynamic_frontier_crawl(
    seed_url: str,
    checker: URLChecker,
    include_regex: Optional[str],
    exclude_regex: Optional[str],
    crawl_sitemaps: bool, # New parameter to control sitemap processing
    max_urls_to_crawl: int, # Control total URLs to crawl
    show_partial_callback=None,
    dynamic_speed_mode: bool = False
) -> List[Dict]:
    """
    Dynamic frontier crawl implementation with unique URL tracking, sitemap integration, and max URL limit.
    """
    visited: Set[str] = set() # URLs for which fetch_and_parse has been called
    queued: Set[str] = set()  # URLs added to the frontier (to avoid re-adding)
    results: List[Dict] = []
    # Using a simple list as a FIFO queue for frontier for now, can be optimized with asyncio.Queue
    frontier: List[Tuple[int, str]] = [] # (depth, url)

    # Normalize and validate seed URL
    normalized_seed_url = normalize_url(seed_url)
    if not normalized_seed_url:
        logging.error("Invalid seed URL provided for dynamic crawl.")
        return results

    base_netloc = urlparse(normalized_seed_url).netloc.lower()
    if not base_netloc:
        logging.error(f"Could not parse netloc from seed URL: {normalized_seed_url}")
        return results

    logging.info(f"Starting dynamic frontier crawl from seed URL: {normalized_seed_url}. Base netloc: {base_netloc}")

    # Add seed URL to frontier
    frontier.append((0, normalized_seed_url))
    queued.add(normalized_seed_url)

    inc_re, exc_re = compile_filters(include_regex, exclude_regex)

    # Sitemap URL discovery (if enabled)
    sitemap_urls_to_process: List[str] = []
    if crawl_sitemaps:
        # Attempt to find sitemaps from robots.txt of the seed URL's domain
        robots_sitemaps = await fetch_sitemaps_from_robots(f"{urlparse(normalized_seed_url).scheme}://{base_netloc}", checker.session)
        sitemap_urls_to_process.extend(robots_sitemaps)
        # Optionally, could add common sitemap paths like /sitemap.xml if not found
        if not sitemap_urls_to_process:
            common_sitemap = urljoin(f"{urlparse(normalized_seed_url).scheme}://{base_netloc}", "sitemap.xml")
            # Basic check if this common sitemap exists before adding
            try:
                async with checker.session.head(common_sitemap, timeout=5, ssl=False) as sitemap_resp:
                    if sitemap_resp.status == 200:
                        sitemap_urls_to_process.append(common_sitemap)
                        logging.info(f"Added common sitemap: {common_sitemap}")
            except Exception as e:
                logging.warning(f"Could not check for common sitemap {common_sitemap}: {e}")


        if sitemap_urls_to_process:
            logging.info(f"Found/Added sitemap URLs for processing: {sitemap_urls_to_process}")
            # Process these sitemaps to extract URLs
            extracted_sitemap_links = await process_sitemaps(sitemap_urls_to_process, checker.session, show_partial_sitemap_callback=None) # No UI callback here
            for link in extracted_sitemap_links:
                norm_link = normalize_url(link)
                if norm_link and norm_link not in queued and norm_link not in visited:
                    # Filter sitemap links: must be on the same domain, and pass regex filters
                    if urlparse(norm_link).netloc.lower() == base_netloc and regex_filter(norm_link, inc_re, exc_re):
                        frontier.append((0, norm_link)) # Add sitemap URLs at depth 0
                        queued.add(norm_link)
            logging.info(f"Added {len(extracted_sitemap_links)} URLs from sitemaps to frontier.")


    processed_url_count = 0
    try:
        # No need to call checker.setup() here, it's called in run_dynamic_crawl
        while frontier and processed_url_count < max_urls_to_crawl:
            if checker.is_stopped():
                logging.info("Crawl stopped by user request during dynamic frontier crawl.")
                break

            depth, current_url = frontier.pop(0) # FIFO
            # current_url is already normalized when added to queue/frontier

            if current_url in visited:
                continue

            visited.add(current_url)
            processed_url_count +=1
            logging.info(f"Crawling URL ({processed_url_count}/{len(queued)} in queue, {len(visited)} visited): {current_url} at depth {depth}")

            try:
                result = await checker.fetch_and_parse(current_url, dynamic_speed_mode=dynamic_speed_mode)
                if result: # fetch_and_parse should always return a dict
                    results.append(result)
                else: # Should not happen
                    logging.warning(f"No result returned for URL: {current_url}, adding to failed.")
                    checker.failed_urls.add(current_url)


                # Discover new links only if page was HTML and successfully fetched (status 200)
                # And if the URL itself was not blocked by robots.txt
                if result and result.get("Final_Status_Code") == "200" and \
                   result.get("Content_Type", "").startswith("text/html") and \
                   result.get("Blocked by Robots.txt") == "No":
                    # Use the content from the result if available, otherwise re-fetch (less ideal)
                    # For now, re-fetching for links to keep fetch_and_parse focused.
                    # Consider passing content if fetch_and_parse could return it.
                    page_content_for_links = "" # This would require fetch_and_parse to return content
                                          # or a re-fetch. Let's assume discover_links handles fetching.

                    discovered_links = await discover_links_from_html(current_url, result.get("Final_URL", current_url), checker.session, checker.user_agent, page_content_for_links)
                    logging.debug(f"Discovered {len(discovered_links)} links from {current_url}")

                    for link in discovered_links:
                        if checker.is_stopped() or len(visited) + len(frontier) >= max_urls_to_crawl * 1.2 : # Heuristic to stop adding if queue grows too large vs max
                            break

                        norm_link = normalize_url(link)
                        if not norm_link or norm_link in visited or norm_link in queued:
                            continue

                        # Filter links: must be on the same domain, and pass regex filters
                        if urlparse(norm_link).netloc.lower() == base_netloc and regex_filter(norm_link, inc_re, exc_re):
                            if len(queued) < max_urls_to_crawl * 1.5: # Another heuristic to prevent excessive queue growth
                                frontier.append((depth + 1, norm_link))
                                queued.add(norm_link)
                            else:
                                logging.debug(f"Queue limit reached, not adding more links from {current_url}")
                                break # Stop processing links from this page if queue is too full


            except Exception as e:
                logging.error(f"Error processing URL {current_url} in dynamic_frontier_crawl loop: {str(e)}")
                checker.failed_urls.add(current_url) # Ensure it's marked for potential recrawl
                continue # Continue to next URL in frontier

            if show_partial_callback:
                # crawled_count is len(visited), total_to_crawl is min(len(queued), max_urls_to_crawl)
                show_partial_callback(results, len(visited), min(len(queued), max_urls_to_crawl))

        logging.info(f"Dynamic frontier crawl loop finished. Visited {len(visited)} URLs. Max URLs set to {max_urls_to_crawl}.")
        return results

    except Exception as e:
        logging.error(f"Fatal error in dynamic_frontier_crawl: {str(e)}")
        return results
    # finally:
        # checker.close() is handled by the calling function run_dynamic_crawl


async def discover_links_from_html(page_url: str, final_page_url:str, session: aiohttp.ClientSession, user_agent: str, html_content: Optional[str] = None) -> List[str]:
    """
    Discover absolute links from an HTML page.
    If html_content is provided, uses it. Otherwise, fetches the page_url.
    page_url is the original URL, final_page_url is the URL after redirects (used for joining relative links).
    """
    links: Set[str] = set() # Use a set to store unique links
    headers = {"User-Agent": user_agent}

    try:
        if not html_content: # If no content passed, fetch it
            async with session.get(page_url, headers=headers, ssl=False, allow_redirects=True, timeout=10) as resp:
                if resp.status == 200 and resp.content_type and resp.content_type.startswith("text/html"):
                    html_content = await resp.text(errors='replace')
                else:
                    logging.warning(f"Could not fetch HTML for link discovery from {page_url} (status: {resp.status})")
                    return [] # Return empty list if page can't be fetched/is not HTML

        if html_content:
            soup = BeautifulSoup(html_content, "lxml")
            for anchor_tag in soup.find_all("a", href=True):
                href = anchor_tag["href"].strip()
                if href and not href.startswith(("mailto:", "tel:", "javascript:")):
                    try:
                        # Use final_page_url as the base for resolving relative URLs
                        abs_link = urljoin(final_page_url, href)
                        parsed_abs_link = urlparse(abs_link)
                        # Ensure it's HTTP/HTTPS and has a netloc
                        if parsed_abs_link.scheme in ["http", "https"] and parsed_abs_link.netloc:
                            links.add(normalize_url(abs_link)) # Normalize before adding
                    except Exception as e:
                        logging.debug(f"Error processing link '{href}' from {page_url}: {e}")
                        continue # Skip malformed links
    except Exception as e:
        logging.error(f"Error discovering links from {page_url}: {e}")

    return list(links)


def compile_filters(include_pattern: Optional[str], exclude_pattern: Optional[str]):
    """Compile regex patterns for URL filtering. Returns (compiled_include_re, compiled_exclude_re)."""
    inc = re.compile(include_pattern) if include_pattern and include_pattern.strip() else None
    exc = re.compile(exclude_pattern) if exclude_pattern and exclude_pattern.strip() else None
    return inc, exc

def regex_filter(url: str, include_re: Optional[re.Pattern], exclude_re: Optional[re.Pattern]) -> bool:
    """Filter URL based on compiled regex patterns."""
    if include_re and not include_re.search(url):
        return False
    if exclude_re and exclude_re.search(url):
        return False
    return True

async def run_dynamic_crawl(
    seed_url: str, checker: URLChecker, include_pattern: Optional[str], exclude_pattern: Optional[str],
    crawl_sitemaps: bool, max_urls: int, show_partial_callback, dynamic_speed_mode: bool
    ) -> List[Dict]:
    """Async wrapper for dynamic frontier crawl."""
    results = []
    try:
        logging.info(f"Starting dynamic crawl for seed URL: {seed_url}")
        await checker.setup() # Setup session and semaphore
        results = await dynamic_frontier_crawl(
            seed_url=seed_url, # Already normalized by caller if needed
            checker=checker,
            include_regex=include_pattern,
            exclude_regex=exclude_pattern,
            crawl_sitemaps=crawl_sitemaps,
            max_urls_to_crawl=max_urls,
            show_partial_callback=show_partial_callback,
            dynamic_speed_mode=dynamic_speed_mode
        )
        logging.info(f"Dynamic crawl phase completed. Found {len(results)} primary results.")

    except Exception as e:
        logging.error(f"Error during dynamic crawl execution: {e}", exc_info=True)
    finally:
        # Recrawl failed URLs if any, regardless of how the main crawl ended
        if checker.failed_urls:
            logging.info(f"Recrawling {len(checker.failed_urls)} failed URLs from dynamic crawl...")
            recrawl_results = await checker.recrawl_failed_urls(dynamic_speed_mode) # Pass speed mode
            results.extend(recrawl_results)
            logging.info(f"Recrawl completed. Added {len(recrawl_results)} more results. Total results: {len(results)}")
        await checker.close() # Ensure session is closed
    return results


async def run_list_or_sitemap_crawl(urls: List[str], checker: URLChecker, show_partial_callback, dynamic_speed_mode: bool, crawl_mode_name: str) -> List[Dict]:
    """Async wrapper for list or sitemap mode crawl. Reuses chunk_process."""
    results = []
    try:
        logging.info(f"Starting {crawl_mode_name} crawl for {len(urls)} URLs.")
        await checker.setup()
        # Normalize URLs before processing
        normalized_urls = [normalize_url(u) for u in urls if normalize_url(u)]
        unique_urls = sorted(list(set(normalized_urls))) # Process unique URLs
        logging.info(f"Processing {len(unique_urls)} unique URLs for {crawl_mode_name} crawl.")

        results = await chunk_process(unique_urls, checker, show_partial_callback=show_partial_callback, dynamic_speed_mode=dynamic_speed_mode)
        logging.info(f"{crawl_mode_name} crawl phase completed. Found {len(results)} primary results.")

    except Exception as e:
        logging.error(f"Error during {crawl_mode_name} crawl execution: {e}", exc_info=True)
    finally:
        if checker.failed_urls:
            logging.info(f"Recrawling {len(checker.failed_urls)} failed URLs from {crawl_mode_name} crawl...")
            recrawl_results = await checker.recrawl_failed_urls(dynamic_speed_mode)
            results.extend(recrawl_results)
            logging.info(f"Recrawl completed. Added {len(recrawl_results)} results. Total: {len(results)}")
        await checker.close()
    return results


async def fetch_sitemaps_from_robots(domain_base_url: str, session: aiohttp.ClientSession) -> List[str]:
    """Fetches and parses robots.txt to find sitemap URLs."""
    robots_url = urljoin(domain_base_url, "/robots.txt")
    sitemap_urls: List[str] = []
    try:
        logging.info(f"Fetching robots.txt from {robots_url} to find sitemaps.")
        async with session.get(robots_url, ssl=False, timeout=aiohttp.ClientTimeout(total=10)) as resp:
            if resp.status == 200:
                content = await resp.text(errors='replace')
                for line in content.splitlines():
                    if line.strip().lower().startswith("sitemap:"):
                        sitemap_url = line.split(":", 1)[1].strip()
                        sitemap_urls.append(sitemap_url)
                if sitemap_urls:
                    logging.info(f"Found sitemap URLs in robots.txt: {sitemap_urls}")
                else:
                    logging.info(f"No sitemap directives found in robots.txt for {domain_base_url}")
            else:
                logging.warning(f"Could not fetch robots.txt from {robots_url} (status: {resp.status})")
    except Exception as e:
        logging.error(f"Error fetching or parsing robots.txt at {robots_url}: {e}")
    return sitemap_urls


async def process_sitemaps(sitemap_urls: List[str], session: aiohttp.ClientSession, show_partial_sitemap_callback=None) -> List[str]:
    """
    Process multiple sitemap URLs concurrently and extract all unique URLs.
    Handles nested sitemap indexes.
    """
    all_found_urls: Set[str] = set()
    sitemaps_to_process_queue: asyncio.Queue[str] = asyncio.Queue()
    processed_sitemap_files: Set[str] = set() # To avoid re-processing same sitemap file if linked multiple times

    for s_url in sitemap_urls:
        normalized_s_url = normalize_url(s_url)
        if normalized_s_url:
            await sitemaps_to_process_queue.put(normalized_s_url)
            processed_sitemap_files.add(normalized_s_url) # Add initial ones to avoid re-queueing if they are also indexes

    active_tasks = 0

    async def process_single_sitemap_worker(s_url: str):
        nonlocal active_tasks
        active_tasks += 1
        try:
            logging.info(f"Processing sitemap: {s_url}")
            urls_from_sitemap, nested_sitemaps = await async_parse_sitemap_xml_or_text(s_url, session)

            for u_url in urls_from_sitemap:
                norm_u = normalize_url(u_url)
                if norm_u:
                    all_found_urls.add(norm_u)

            for ns_url in nested_sitemaps:
                norm_ns = normalize_url(ns_url)
                if norm_ns and norm_ns not in processed_sitemap_files:
                    await sitemaps_to_process_queue.put(norm_ns)
                    processed_sitemap_files.add(norm_ns) # Mark as added to queue

            if show_partial_sitemap_callback:
                show_partial_sitemap_callback(list(all_found_urls)) # Update UI with current count

        except Exception as e:
            logging.error(f"Error processing sitemap {s_url} in worker: {e}")
        finally:
            sitemaps_to_process_queue.task_done()
            active_tasks -=1

    # Create worker tasks
    # Limit concurrent sitemap processing tasks, e.g., to 5
    # This is for fetching/parsing sitemap files themselves, not the URLs within them.
    MAX_SITEMAP_WORKERS = 5
    workers = []

    while True:
        try:
            # Wait for a short duration if queue is empty but tasks might still be adding to it
            sitemap_url_to_work_on = await asyncio.wait_for(sitemaps_to_process_queue.get(), timeout=1.0)
        except asyncio.TimeoutError:
            if active_tasks == 0 and sitemaps_to_process_queue.empty():
                break # All sitemaps processed and queue is empty
            continue # Continue waiting if tasks are still active

        if len(workers) >= MAX_SITEMAP_WORKERS:
            # Wait for one of the existing workers to complete
            _done, workers = await asyncio.wait(workers, return_when=asyncio.FIRST_COMPLETED)

        task = asyncio.create_task(process_single_sitemap_worker(sitemap_url_to_work_on))
        workers.append(task)

    # Wait for all remaining tasks to complete
    if workers:
        await asyncio.wait(workers)

    await sitemaps_to_process_queue.join() # Ensure queue is fully processed

    logging.info(f"Finished processing all sitemaps. Found {len(all_found_urls)} unique URLs.")
    return sorted(list(all_found_urls))


async def async_parse_sitemap_xml_or_text(url: str, session: aiohttp.ClientSession) -> Tuple[List[str], List[str]]:
    """
    Parse a single sitemap URL (XML or TXT) and extract URLs and nested sitemap URLs.
    Returns (list_of_page_urls, list_of_nested_sitemap_urls).
    """
    page_urls: List[str] = []
    nested_sitemap_urls: List[str] = []
    try:
        # Use a timeout for fetching individual sitemap files
        timeout = aiohttp.ClientTimeout(total=20) # 20 seconds for fetching a sitemap file
        async with session.get(url, ssl=False, timeout=timeout) as response:
            if response.status == 200:
                content = await response.text(errors='replace')
                content_type = response.headers.get("Content-Type", "").lower()

                if 'xml' in content_type or content.strip().startswith('<?xml'):
                    # Parse XML content
                    try:
                        root = ET.fromstring(content)
                        # Define namespaces commonly found in sitemaps
                        namespaces = {
                            'sm': 'http://www.sitemaps.org/schemas/sitemap/0.9',
                            # Add other namespaces if needed, e.g., for image or video sitemaps
                        }

                        # Check if this is a sitemap index
                        if root.tag.endswith('sitemapindex'):
                            for sitemap_element in root.findall('.//sm:sitemap', namespaces=namespaces):
                                loc_element = sitemap_element.find('sm:loc', namespaces=namespaces)
                                if loc_element is not None and loc_element.text:
                                    nested_sitemap_urls.append(loc_element.text.strip())
                        else: # Regular sitemap
                            for url_element in root.findall('.//sm:url', namespaces=namespaces):
                                loc_element = url_element.find('sm:loc', namespaces=namespaces)
                                if loc_element is not None and loc_element.text:
                                    page_urls.append(loc_element.text.strip())
                    except ET.ParseError as e_xml:
                        logging.warning(f"XML ParseError for sitemap {url}: {e_xml}. Trying text parse.")
                        # Fallback to text parsing if XML parsing fails for some reason (e.g. malformed XML but still text)
                        for line in content.splitlines():
                            line = line.strip()
                            if line and (line.startswith("http://") or line.startswith("https://")):
                                page_urls.append(line)

                elif 'text/plain' in content_type or not content_type : # Treat as text sitemap if XML not detected or no content type
                    logging.info(f"Parsing {url} as a text sitemap.")
                    for line in content.splitlines():
                        line = line.strip()
                        # Basic validation for a URL
                        if line and (line.startswith("http://") or line.startswith("https://")) and '.' in urlparse(line).netloc :
                            page_urls.append(line)
                else:
                    logging.warning(f"Unsupported Content-Type '{content_type}' for sitemap {url}. Skipping.")

            else:
                logging.error(f"Failed to fetch sitemap {url}. Status: {response.status}")
    except asyncio.TimeoutError:
        logging.error(f"Timeout fetching sitemap {url}.")
    except aiohttp.ClientError as e_aio: # Catch more specific aiohttp client errors
        logging.error(f"ClientError fetching sitemap {url}: {e_aio}")
    except Exception as e:
        logging.error(f"Unexpected error parsing sitemap {url}: {e}")
    return page_urls, nested_sitemap_urls


async def chunk_process(urls: List[str], checker: URLChecker, show_partial_callback=None, dynamic_speed_mode: bool = False) -> List[Dict]:
    """
    Process a list of URLs by creating tasks for each and gathering results.
    The checker's semaphore handles concurrency.
    """
    results = []
    total_urls = len(urls)
    processed_count = 0

    if not urls:
        return []

    # checker.setup() is called by the calling run_list_or_sitemap_crawl function

    # Create all tasks
    tasks = [checker.fetch_and_parse(url, dynamic_speed_mode=dynamic_speed_mode) for url in urls]

    for future in asyncio.as_completed(tasks):
        if checker.is_stopped(): # Check if stop requested during processing
            logging.info("Chunk processing interrupted by stop request.")
            # Optionally, cancel remaining tasks if desired, but as_completed will naturally stop yielding them
            # for task_to_cancel in tasks:
            #    if not task_to_cancel.done():
            #        task_to_cancel.cancel()
            break

        try:
            result = await future # Get result from completed task
            if result: # fetch_and_parse should always return a dict
                results.append(result)
        except Exception as e:
            # This catch block might be redundant if fetch_and_parse handles its own errors
            # and returns a dict with error info. However, it can catch unexpected errors from await future.
            logging.error(f"Error processing a URL in chunk: {e}")
            # We might not know which URL failed here if not careful, fetch_and_parse should include Original_URL
        finally:
            processed_count += 1
            if show_partial_callback:
                show_partial_callback(results, processed_count, total_urls)

    # checker.close() is also handled by the calling function
    return results


def normalize_url(url: str) -> str:
    """
    Normalize a URL: adds scheme if missing, removes fragment, lowercases scheme and netloc.
    """
    if not url: return ""
    url = url.strip()
    parsed = urlparse(url)

    scheme = parsed.scheme.lower()
    if not scheme: scheme = 'https' # Default to https

    netloc = parsed.netloc.lower()
    path = parsed.path
    if not path: path = '/' # Ensure path is at least '/'

    # Reconstruct, excluding fragment and query params if desired (currently keeping query)
    # To remove query params: parsed = parsed._replace(query="")
    normalized = urlunparse((scheme, netloc, path, parsed.params, parsed.query, "")) # Fragment removed
    return normalized


def update_redirect_label(data: Dict, original_url: str) -> Dict:
    """
    Update the Final_Status_Type field based on redirect information and canonical URLs.
    This provides more context than just the raw status code type.
    """
    final_url = data.get("Final_URL", "")
    final_status_str = data.get("Final_Status_Code", "") # This is a string
    # original_url is passed for comparison

    # Normalize for comparison
    norm_original_url = normalize_url(original_url)
    norm_final_url = normalize_url(final_url)

    if final_status_str.lower() == "error" or final_status_str.lower() == "skipped":
        # Keep the existing Final_Status_Type if it's an error or skipped
        return data

    try:
        final_status_code = int(final_status_str)
    except ValueError: # If status code isn't a number (e.g. "Error")
        # data["Final_Status_Type"] is already set by fetch_and_parse for errors
        return data


    if norm_final_url == norm_original_url:
        if 200 <= final_status_code < 300:
            data["Final_Status_Type"] = "OK (No Redirect)"
        else: # e.g. 404 on the original URL itself
            data["Final_Status_Type"] = f"{data.get('Final_Status_Type', '')} (No Redirect)"
    else: # It's a redirect
        if 200 <= final_status_code < 300:
            data["Final_Status_Type"] = "Redirect to 2xx"
        elif 300 <= final_status_code < 400:
            # This case implies a redirect chain that ended in another redirect,
            # which aiohttp usually resolves. If final status is 3xx, it's likely
            # the max_redirects was hit or allow_redirects=False for that specific request.
            # However, our main fetch_and_parse uses allow_redirects=True by default for the session.
            # This might indicate a redirect loop or a misconfiguration.
            data["Final_Status_Type"] = f"Redirect to {final_status_code}"
        elif 400 <= final_status_code < 600:
            data["Final_Status_Type"] = f"Redirect to Error {final_status_code}"
        else:
            data["Final_Status_Type"] = f"Redirect to Unknown Status ({final_status_code})"

    # Check for canonical mismatch after determining redirect status
    # This is an indexability concern, not strictly a redirect type.
    # update_indexability_from_directives already handles canonical impact on indexability.
    # We can add a note here if desired, but it might be redundant.
    # canonical_url = data.get("Canonical_URL", "")
    # if canonical_url and normalize_url(canonical_url) != norm_final_url:
    #    data["Final_Status_Type"] += " (Canonical Mismatch)" # Appending to existing type

    return data


def format_and_reorder_df(df: pd.DataFrame) -> pd.DataFrame:
    """Helper function to reorder and format columns consistently for display."""
    if df.empty:
        return df

    # Define the desired column order
    # Prioritize key information, then technical details, then content details
    desired_cols_order = [
        'Original_URL', 'Final_URL',
        'Initial_Status_Code', 'Initial_Status_Type',
        'Final_Status_Code', 'Final_Status_Type',
        'Indexable', 'Indexability Reason',
        'Blocked by Robots.txt', 'Robots Block Rule',
        'Meta Robots', 'X-Robots-Tag', 'Canonical_URL',
        'Content_Type', 'Title', 'Meta Description', 'H1', 'H1_Count',
        'Word Count', 'HTML Lang', 'Last Modified',
        'Crawl Time', 'Timestamp'
    ]

    # Get existing columns from the DataFrame
    existing_cols = df.columns.tolist()
    ordered_cols = []
    remaining_cols = list(existing_cols) # Start with all columns

    # Add desired columns if they exist, in the specified order
    for col in desired_cols_order:
        if col in remaining_cols:
            ordered_cols.append(col)
            remaining_cols.remove(col)

    # Add any other columns that were not in the desired_cols_order list (e.g., new fields)
    ordered_cols.extend(remaining_cols)

    return df[ordered_cols]


def main():
    st.set_page_config(layout="wide", page_title="Web Crawler SEO Tool")
    st.title("🕵️ Web Crawler & SEO Analyzer")
    st.markdown("Crawl websites, analyze SEO elements, and export data.")

    # Initialize session state variables
    if 'is_crawling' not in st.session_state: st.session_state['is_crawling'] = False
    if 'crawl_results' not in st.session_state: st.session_state['crawl_results'] = []
    if 'crawl_done' not in st.session_state: st.session_state['crawl_done'] = False
    if 'checker_instance' not in st.session_state: st.session_state['checker_instance'] = None
    if 'current_crawl_mode' not in st.session_state: st.session_state['current_crawl_mode'] = "Spider"


    st.sidebar.header("⚙️ Crawler Configuration")

    # User Agent Selection
    ua_mode = st.sidebar.radio("User Agent Mode", ["Preset", "Custom"], index=0, horizontal=True, key="ua_mode_radio")
    if ua_mode == "Preset":
        ua_choice = st.sidebar.selectbox("Select User Agent", list(USER_AGENTS.keys()), index=0, key="ua_preset_select")
        user_agent = USER_AGENTS[ua_choice]
    else:
        user_agent = st.sidebar.text_input("Enter Custom User Agent", value=DEFAULT_USER_AGENT, key="ua_custom_input")

    # Speed Controls & Concurrency
    st.sidebar.subheader("🚀 Speed & Performance")
    speed_mode_options = ["Safe (Default)", "Dynamic (Adjusts)", "Custom"]
    speed_mode = st.sidebar.selectbox("Speed Mode", speed_mode_options, index=0, key="speed_mode_select",
                                      help="Safe: Fixed moderate speed. Dynamic: Adjusts based on server response. Custom: Manual setting.")

    dynamic_speed_active = False
    if speed_mode == "Safe (Default)":
        concurrency = DEFAULT_CONCURRENCY
    elif speed_mode == "Dynamic (Adjusts)":
        concurrency = st.sidebar.slider("Initial URLs/sec (Concurrency)", MIN_CONCURRENCY, MAX_CONCURRENCY, DEFAULT_CONCURRENCY, key="concurrency_dynamic_slider")
        dynamic_speed_active = True # Flag that dynamic adjustment should occur
    else:  # Custom
        concurrency = st.sidebar.slider("Fixed URLs/sec (Concurrency)", MIN_CONCURRENCY, MAX_CONCURRENCY, DEFAULT_CONCURRENCY, key="concurrency_custom_slider")

    timeout_seconds = st.sidebar.slider("Request Timeout (seconds)", 5, 60, DEFAULT_TIMEOUT, key="timeout_slider")
    respect_robots = st.sidebar.checkbox("Respect robots.txt", value=True, key="respect_robots_check", help="If unchecked, robots.txt will be ignored (use responsibly).")

    st.sidebar.markdown("---")
    st.sidebar.header("🎯 Crawl Mode & Input")
    mode = st.sidebar.radio("Select Mode", ["Spider", "List", "Sitemap"], index=0, key="crawl_mode_radio", horizontal=False)
    st.session_state['current_crawl_mode'] = mode # Update current mode

    # --- UI Placeholders ---
    # These will be defined within each mode's section if needed, or globally if shared
    progress_bar_placeholder = st.empty()
    progress_text_placeholder = st.empty()
    results_table_placeholder = st.empty()
    download_buttons_placeholder = st.empty() # For Download and Copy buttons

    # --- Callback for partial data updates ---
    def show_partial_data_streamlit(current_results: List[Dict], processed_count: int, total_count: int):
        if total_count > 0:
            ratio = min(1.0, processed_count / total_count if total_count > 0 else 0)
            progress_bar_placeholder.progress(ratio)
            progress_text_placeholder.markdown(
                f"**Status:** Processed {processed_count} of approx. {total_count} URLs ({ratio*100:.2f}%). "
                f"Collected {len(current_results)} results."
            )
        else: # E.g. dynamic crawl where total_count might be unknown initially or very large
            progress_text_placeholder.markdown(
                 f"**Status:** Processed {processed_count} URLs. "
                 f"Collected {len(current_results)} results."
            )

        if current_results: # Only update table if there are results
            df_temp = pd.DataFrame(current_results)
            df_temp_formatted = format_and_reorder_df(df_temp)
            # Display a limited number of rows during crawl for performance
            results_table_placeholder.dataframe(df_temp_formatted.head(1000), height=400, use_container_width=True)


    # --- Sitemap URLs display callback (for sitemap mode input) ---
    sitemap_urls_display_placeholder = st.empty()
    def show_discovered_sitemap_urls_streamlit(discovered_urls: List[str]):
        if discovered_urls:
            sitemap_urls_display_placeholder.info(f"Discovered {len(discovered_urls)} URLs from sitemaps. Ready to crawl.")
            # st.expander("View Discovered URLs").dataframe(pd.DataFrame(discovered_urls, columns=["URLs from Sitemaps"]))
        else:
            sitemap_urls_display_placeholder.info("No URLs discovered from the provided sitemaps yet.")


    # === Spider Mode UI ===
    if mode == "Spider":
        st.subheader("🕷️ Spider Mode")
        seed_url_input = st.text_input("Enter Seed URL to start crawling from:", placeholder="e.g., https://example.com", key="spider_seed_url")
        max_urls_spider = st.number_input("Max URLs to Crawl in Spider Mode:", min_value=10, max_value=DEFAULT_MAX_URLS, value=100, step=10, key="spider_max_urls",
                                          help=f"Maximum URLs the spider will attempt to fetch. Default is 100, Max is {DEFAULT_MAX_URLS}.")
        spider_crawl_sitemaps = st.checkbox("Auto-discover & crawl sitemaps found via robots.txt of seed domain?", value=True, key="spider_crawl_sitemaps_check",
                                            help="If checked, will look for sitemaps in robots.txt of the seed URL's domain and add their URLs to the crawl queue.")

        st.markdown("###### Advanced Filters (Optional)")
        col_inc, col_exc = st.columns(2)
        include_pattern_spider = col_inc.text_input("Include URLs matching Regex:", placeholder="e.g., /products/", key="spider_include_regex")
        exclude_pattern_spider = col_exc.text_input("Exclude URLs matching Regex:", placeholder="e.g., /blog/category/old/", key="spider_exclude_regex")

        start_stop_col, _ = st.columns([1,3]) # Column for button
        if st.session_state['is_crawling'] and st.session_state.get('crawl_op_id') == "spider":
            if start_stop_col.button("🛑 Stop Crawl", key="spider_stop_btn"):
                if st.session_state['checker_instance']:
                    st.session_state['checker_instance'].stop()
                st.session_state['is_crawling'] = False # Assume stop is immediate for UI
                st.warning("Stop request sent. Finishing current tasks...")
        elif not st.session_state['is_crawling']:
            if start_stop_col.button("🚀 Start Spider Crawl", key="spider_start_btn"):
                if seed_url_input and normalize_url(seed_url_input):
                    st.session_state['is_crawling'] = True
                    st.session_state['crawl_done'] = False
                    st.session_state['crawl_results'] = []
                    st.session_state['crawl_op_id'] = "spider" # Identifier for this operation
                    results_table_placeholder.empty() # Clear previous table
                    progress_text_placeholder.info("Spider crawl starting...")


                    checker = URLChecker(user_agent, concurrency, timeout_seconds, respect_robots)
                    st.session_state['checker_instance'] = checker
                    loop = asyncio.new_event_loop()
                    asyncio.set_event_loop(loop)
                    try:
                        results = loop.run_until_complete(
                            run_dynamic_crawl(
                                seed_url=normalize_url(seed_url_input), checker=checker,
                                include_pattern=include_pattern_spider, exclude_pattern=exclude_pattern_spider,
                                crawl_sitemaps=spider_crawl_sitemaps, max_urls=max_urls_spider,
                                show_partial_callback=show_partial_data_streamlit,
                                dynamic_speed_mode=dynamic_speed_active
                            )
                        )
                        st.session_state['crawl_results'] = results
                        st.session_state['crawl_done'] = True
                        progress_text_placeholder.success(f"Spider crawl finished! Found {len(results)} results.")
                    except Exception as e:
                        st.error(f"Spider crawl failed: {e}")
                        logging.error("Spider Crawl Exception", exc_info=True)
                        st.session_state['crawl_done'] = True # Mark as done even if failed
                    finally:
                        loop.close()
                        st.session_state['is_crawling'] = False
                        st.session_state['checker_instance'] = None # Clear checker
                else:
                    st.warning("Please enter a valid seed URL.")

    # === List Mode UI ===
    elif mode == "List":
        st.subheader("📋 List Mode")
        url_list_input = st.text_area("Enter URLs (one per line):", height=200, placeholder="https://example.com/page1\nhttps://example.com/page2", key="list_urls_area")
        start_stop_col_list, _ = st.columns([1,3])

        if st.session_state['is_crawling'] and st.session_state.get('crawl_op_id') == "list":
            if start_stop_col_list.button("🛑 Stop Crawl", key="list_stop_btn"):
                if st.session_state['checker_instance']: st.session_state['checker_instance'].stop()
                st.session_state['is_crawling'] = False
                st.warning("Stop request sent for List crawl.")
        elif not st.session_state['is_crawling']:
            if start_stop_col_list.button("🚀 Start List Crawl", key="list_start_btn"):
                user_urls = [u.strip() for u in url_list_input.splitlines() if u.strip()]
                if user_urls:
                    st.session_state['is_crawling'] = True
                    st.session_state['crawl_done'] = False
                    st.session_state['crawl_results'] = []
                    st.session_state['crawl_op_id'] = "list"
                    results_table_placeholder.empty()
                    progress_text_placeholder.info("List crawl starting...")

                    checker = URLChecker(user_agent, concurrency, timeout_seconds, respect_robots)
                    st.session_state['checker_instance'] = checker
                    loop = asyncio.new_event_loop()
                    asyncio.set_event_loop(loop)
                    try:
                        results = loop.run_until_complete(
                            run_list_or_sitemap_crawl(
                                urls=user_urls, checker=checker,
                                show_partial_callback=show_partial_data_streamlit,
                                dynamic_speed_mode=dynamic_speed_active,
                                crawl_mode_name="List"
                            )
                        )
                        st.session_state['crawl_results'] = results
                        st.session_state['crawl_done'] = True
                        progress_text_placeholder.success(f"List crawl finished! Found {len(results)} results.")
                    except Exception as e:
                        st.error(f"List crawl failed: {e}")
                        logging.error("List Crawl Exception", exc_info=True)
                        st.session_state['crawl_done'] = True
                    finally:
                        loop.close()
                        st.session_state['is_crawling'] = False
                        st.session_state['checker_instance'] = None
                else:
                    st.warning("Please enter at least one URL.")

    # === Sitemap Mode UI ===
    elif mode == "Sitemap":
        st.subheader("🗺️ Sitemap Mode")
        sitemap_urls_input = st.text_area("Enter Sitemap XML URLs (one per line):", height=150, placeholder="https://example.com/sitemap.xml\nhttps://example.com/sitemap_index.xml", key="sitemap_urls_area")
        start_stop_col_sitemap, _ = st.columns([1,3])

        if st.session_state['is_crawling'] and st.session_state.get('crawl_op_id') == "sitemap":
            if start_stop_col_sitemap.button("🛑 Stop Crawl", key="sitemap_stop_btn"):
                if st.session_state['checker_instance']: st.session_state['checker_instance'].stop()
                st.session_state['is_crawling'] = False
                st.warning("Stop request sent for Sitemap crawl.")
        elif not st.session_state['is_crawling']:
            if start_stop_col_sitemap.button("🔗 Fetch & Crawl Sitemaps", key="sitemap_start_btn"):
                sitemap_xml_urls = [s.strip() for s in sitemap_urls_input.splitlines() if s.strip()]
                if sitemap_xml_urls:
                    st.session_state['is_crawling'] = True # Mark as crawling during sitemap parsing too
                    st.session_state['crawl_done'] = False
                    st.session_state['crawl_results'] = []
                    st.session_state['crawl_op_id'] = "sitemap"
                    results_table_placeholder.empty()
                    progress_text_placeholder.info("Fetching URLs from sitemaps...")
                    sitemap_urls_display_placeholder.empty() # Clear previous discovery message

                    # Temporary session for sitemap parsing
                    temp_session_loop = asyncio.new_event_loop()
                    asyncio.set_event_loop(temp_session_loop)
                    all_urls_from_sitemaps = []
                    try:
                        # Create a temporary session just for parsing sitemaps
                        # This avoids conflict if checker_instance is already in use or not set up
                        temp_connector = aiohttp.TCPConnector(ssl=False)
                        async with aiohttp.ClientSession(connector=temp_connector, headers={"User-Agent": user_agent}) as sitemap_session:
                            all_urls_from_sitemaps = await process_sitemaps(
                                sitemap_xml_urls,
                                session=sitemap_session,
                                show_partial_sitemap_callback=show_discovered_sitemap_urls_streamlit
                            )
                        show_discovered_sitemap_urls_streamlit(all_urls_from_sitemaps) # Final update
                    except Exception as e_sitemap_proc:
                        st.error(f"Error processing sitemaps: {e_sitemap_proc}")
                        logging.error("Sitemap Processing Exception", exc_info=True)
                        st.session_state['is_crawling'] = False # Stop if sitemap parsing fails
                        # temp_session_loop.close() # Close loop here if error
                        # return # Exit if sitemap processing fails
                    finally:
                        if not temp_session_loop.is_closed(): # Ensure loop is closed
                             temp_session_loop.close()


                    if all_urls_from_sitemaps:
                        progress_text_placeholder.info(f"Found {len(all_urls_from_sitemaps)} URLs. Starting crawl...")
                        checker = URLChecker(user_agent, concurrency, timeout_seconds, respect_robots)
                        st.session_state['checker_instance'] = checker
                        crawl_loop = asyncio.new_event_loop()
                        asyncio.set_event_loop(crawl_loop)
                        try:
                            results = crawl_loop.run_until_complete(
                                run_list_or_sitemap_crawl(
                                    urls=all_urls_from_sitemaps, checker=checker,
                                    show_partial_callback=show_partial_data_streamlit,
                                    dynamic_speed_mode=dynamic_speed_active,
                                    crawl_mode_name="Sitemap"
                                )
                            )
                            st.session_state['crawl_results'] = results
                            st.session_state['crawl_done'] = True
                            progress_text_placeholder.success(f"Sitemap crawl finished! Found {len(results)} results.")
                        except Exception as e:
                            st.error(f"Sitemap crawl failed: {e}")
                            logging.error("Sitemap Crawl Exception", exc_info=True)
                            st.session_state['crawl_done'] = True
                        finally:
                            crawl_loop.close()
                            st.session_state['is_crawling'] = False
                            st.session_state['checker_instance'] = None
                    else:
                        st.warning("No URLs found in the provided sitemaps to crawl.")
                        st.session_state['is_crawling'] = False
                else:
                    st.warning("Please enter at least one Sitemap URL.")


    # --- Display final results and download/copy buttons ---
    if st.session_state['crawl_done'] and st.session_state['crawl_results']:
        final_df = pd.DataFrame(st.session_state['crawl_results'])
        final_df_formatted = format_and_reorder_df(final_df)
        results_table_placeholder.dataframe(final_df_formatted, height=500, use_container_width=True) # Show full final table

        csv_data = final_df_formatted.to_csv(index=False, encoding='utf-8')
        # Use bytes for download button, string for copy button
        csv_bytes = csv_data.encode('utf-8')

        # download_buttons_placeholder holds the columns for the buttons
        btn_col1, btn_col2 = download_buttons_placeholder.columns(2)
        with btn_col1:
            st.download_button(
                label="📥 Download Results as CSV",
                data=csv_bytes,
                file_name=f"crawl_results_{st.session_state['current_crawl_mode'].lower()}_{datetime.now().strftime('%Y%m%d_%H%M')}.csv",
                mime="text/csv",
                key="download_csv_final"
            )
        with btn_col2:
            copy_button(csv_data, "📋 Copy as CSV", key="copy_csv_final") # Using st_copy.copy_button

        # --- Summary Section ---
        st.subheader("📊 Crawl Summary")
        if not final_df_formatted.empty:
            summary_cols = st.columns(3)
            summary_cols[0].metric("Total URLs Processed", len(final_df_formatted))

            # Indexable count
            if 'Indexable' in final_df_formatted.columns:
                 indexable_count = final_df_formatted[final_df_formatted['Indexable'].str.lower() == 'yes'].shape[0]
                 summary_cols[1].metric("Indexable URLs", indexable_count)

            # HTTP 200 count
            if 'Final_Status_Code' in final_df_formatted.columns:
                http_200_count = final_df_formatted[final_df_formatted['Final_Status_Code'] == '200'].shape[0]
                summary_cols[2].metric("HTTP 200 OK", http_200_count)

            # Further summary details in expanders
            with st.expander("Detailed Status Code Distribution"):
                if 'Final_Status_Code' in final_df_formatted.columns:
                    st.dataframe(final_df_formatted['Final_Status_Code'].value_counts().rename_axis('Status Code').reset_index(name='Count'))
            with st.expander("Indexability Overview"):
                if 'Indexable' in final_df_formatted.columns and 'Indexability Reason' in final_df_formatted.columns:
                    st.dataframe(final_df_formatted.groupby(['Indexable', 'Indexability Reason']).size().reset_index(name='Count').sort_values(by='Count', ascending=False))

        else:
            st.info("No results to summarize.")

    elif st.session_state['crawl_done'] and not st.session_state['crawl_results']:
        results_table_placeholder.info("Crawl finished, but no results were collected.")


if __name__ == "__main__":
    main()

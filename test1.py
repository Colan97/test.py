import streamlit as st
import pandas as pd
import re
import asyncio
import aiohttp
import orjson
import nest_asyncio
import logging
from typing import List, Dict, Set, Optional, Tuple
from urllib.parse import urlparse, urljoin, urlunparse
from bs4 import BeautifulSoup
from datetime import datetime
from tenacity import retry, stop_after_attempt, wait_exponential
import xml.etree.ElementTree as ET
import os
from pathlib import Path
from st_copy import copy_button
import time
from urllib import robotparser
import platform
from rich.console import Console
from rich.progress import Progress, SpinnerColumn, TextColumn
from rich.table import Table
from rich.panel import Panel
from rich.logging import RichHandler
from dataclasses import dataclass
import hashlib
import ssl
import certifi

# Apply nest_asyncio to allow nested event loops
nest_asyncio.apply()

# Set up event loop policy for Windows
if platform.system() == "Windows":
    asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())

# Constants
DEFAULT_TIMEOUT = 30
DEFAULT_MAX_URLS = 1000
SAVE_INTERVAL = 100
MAX_RETRIES = 3
INITIAL_BACKOFF = 1
MAX_BACKOFF = 60
DEFAULT_USER_AGENT = "custom_adidas_seo_x3423/1.0"
ERROR_THRESHOLD = 0.15
MIN_CONCURRENCY = 5
MAX_CONCURRENCY = 100
DEFAULT_CONCURRENCY = 20
RETRY_DELAYS = [1, 2, 4]

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format="%(message)s",
    datefmt="[%X]",
    handlers=[RichHandler(rich_tracebacks=True)]
)
logger = logging.getLogger("rich")
console = Console()

# User Agents
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
    with open(filename, 'w', encoding='utf-8') as f:
        json.dump(results, f, ensure_ascii=False, indent=2)

def load_results_from_file(filename: str) -> List[Dict]:
    """Load results from a JSON file."""
    if os.path.exists(filename):
        with open(filename, 'r', encoding='utf-8') as f:
            return json.load(f)
    return []

def calculate_error_rate(results: List[Dict]) -> float:
    """Calculate the error rate from recent results."""
    if not results:
        return 0.0
    error_count = sum(1 for r in results if str(r.get("Final_Status_Code", "")).startswith(("4", "5")))
    return error_count / len(results)

def adjust_concurrency(current_concurrency: int, error_rate: float) -> int:
    """Dynamically adjust concurrency based on error rate."""
    if error_rate > ERROR_THRESHOLD:
        return max(MIN_CONCURRENCY, current_concurrency - 2)
    elif error_rate < ERROR_THRESHOLD / 2:
        return min(MAX_CONCURRENCY, current_concurrency + 1)
    return current_concurrency

class URLChecker:
    def __init__(self, user_agent: str, concurrency: int, timeout: int, respect_robots: bool):
        self.user_agent = user_agent
        self.concurrency = concurrency
        self.timeout = timeout
        self.respect_robots = respect_robots
        self.robots_cache = {}
        self.robots_parser_cache = {}
        self.robots_rules_cache = {}  # New cache for storing rules
        self.session = None
        self.semaphore = None
        self.failed_urls = set()
        self.recent_results = []
        self.last_save_time = datetime.now()
        self.save_filename = f"crawl_results_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        self.robots_semaphore = asyncio.Semaphore(10)
        self.stop_event = asyncio.Event()
        self.last_adjustment_time = datetime.now()
        self.adjustment_interval = 10

    async def adjust_concurrency_if_needed(self):
        now = datetime.now()
        if (now - self.last_adjustment_time).total_seconds() >= self.adjustment_interval:
            error_rate = calculate_error_rate(self.recent_results[-100:] if self.recent_results else [])
            new_concurrency = adjust_concurrency(self.concurrency, error_rate)
            if new_concurrency != self.concurrency:
                logging.info(f"Adjusting concurrency from {self.concurrency} to {new_concurrency} (error rate: {error_rate:.2%})")
                self.concurrency = new_concurrency
                self.semaphore = asyncio.Semaphore(self.concurrency)
            self.last_adjustment_time = now

    async def setup(self):
        try:
            connector = aiohttp.TCPConnector(limit_per_host=100, ssl=False)
            timeout_settings = aiohttp.ClientTimeout(total=None, connect=self.timeout, sock_read=self.timeout)
            self.session = aiohttp.ClientSession(connector=connector, timeout=timeout_settings,
                                                headers={"User-Agent": self.user_agent})
            self.semaphore = asyncio.Semaphore(self.concurrency)
            logging.info(f"URLChecker initialized with concurrency {self.concurrency}")
        except Exception as e:
            logging.error(f"Error setting up URLChecker: {str(e)}")
            raise

    async def close(self):
        try:
            if self.session:
                await self.session.close()
            if self.recent_results:
                save_results_to_file(self.recent_results, self.save_filename)
                logging.info(f"Saved {len(self.recent_results)} results to {self.save_filename}")
        except Exception as e:
            logging.error(f"Error closing URLChecker: {str(e)}")

    async def recrawl_failed_urls(self) -> List[Dict]:
        if not self.failed_urls:
            return []
        results = []
        for url in self.failed_urls:
            for attempt, delay in enumerate(RETRY_DELAYS, 1):
                try:
                    result = await self.fetch_and_parse(url)
                    if result and str(result.get("Final_Status_Code", "")).startswith("2"):
                        results.append(result)
                        break
                    await asyncio.sleep(delay)
                except Exception as e:
                    logging.error(f"Error recrawling {url}: {e}")
        self.failed_urls.clear()
        return results

    async def check_robots(self, url: str) -> Tuple[bool, str]:
        parsed = urlparse(url)
        base_url = f"{parsed.scheme}://{parsed.netloc}"
        user_agent = self.user_agent.split("/")[0].lower()

        if base_url in self.robots_parser_cache:
            parser = self.robots_parser_cache[base_url]
            allowed = parser.can_fetch(user_agent, url)
            if not allowed:
                for pattern, rule in self.robots_rules_cache.get(base_url, {}).items():
                    if re.match(pattern.replace('*', '.*'), url):
                        return False, rule
                return False, "Disallow rule found"
            return True, ""

        async with self.robots_semaphore:
            if base_url in self.robots_cache:
                content = self.robots_cache[base_url]
            else:
                try:
                    async with aiohttp.ClientSession() as session:
                        async with session.get(f"{base_url}/robots.txt", ssl=False, timeout=5) as resp:
                            if resp.status == 200:
                                content = await resp.text()
                                self.robots_cache[base_url] = content
                            else:
                                return True, ""
                except Exception as e:
                    logging.warning(f"Could not fetch robots.txt: {e}")
                    return True, ""

            parser = robotparser.RobotFileParser()
            parser.parse(content.splitlines())
            self.robots_parser_cache[base_url] = parser

            rules = {}
            for line in content.splitlines():
                if line.lower().startswith('disallow:'):
                    pattern = line[9:].strip()
                    if pattern:
                        rules[pattern] = line.strip()
            self.robots_rules_cache[base_url] = rules

            allowed = parser.can_fetch(user_agent, url)
            if not allowed:
                for pattern, rule in rules.items():
                    if re.match(pattern.replace('*', '.*'), url):
                        return False, rule
                return False, "Disallow rule found"
            return True, ""

    async def fetch_and_parse(self, url: str) -> Dict:
        async with self.semaphore:
            await self.adjust_concurrency_if_needed()
            data = {
                "Original_URL": url,
                "Content_Type": "",
                "Initial_Status_Code": "",
                "Initial_Status_Type": "",
                "Final_URL": "",
                "Final_Status_Code": "",
                "Final_Status_Type": "",
                "Title": "",
                "Meta Description": "",
                "H1": "",
                "H1_Count": 0,
                "Canonical_URL": "",
                "Meta Robots": "",
                "X-Robots-Tag": "",
                "HTML Lang": "",
                "Blocked by Robots.txt": "No",
                "Robots Block Rule": "",
                "Indexable": "Yes",
                "Indexability Reason": "",
                "Last Modified": "",
                "Word Count": 0,
                "Crawl Time": 0,
                "Timestamp": datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
            }

            try:
                robots_task = asyncio.create_task(self.check_robots(url))
                start = time.time()

                for attempt in range(MAX_RETRIES):
                    try:
                        async with self.session.get(url, ssl=False, allow_redirects=True) as resp:
                            data["Content_Type"] = resp.headers.get("Content-Type", "")
                            data["Initial_Status_Code"] = str(resp.status)
                            data["Initial_Status_Type"] = self.status_label(resp.status)
                            data["Final_URL"] = str(resp.url)
                            data["Final_Status_Code"] = str(resp.status)
                            data["Final_Status_Type"] = self.status_label(resp.status)
                            data["Last Modified"] = resp.headers.get("Last-Modified", "")

                            if resp.status == 200 and resp.content_type.startswith("text/html"):
                                content = await resp.text(errors='replace')
                                result = self.parse_html_content(data, content, resp.headers, resp.status, True)
                                allowed, blocking_rule = await robots_task
                                if not allowed:
                                    result["Blocked by Robots.txt"] = "Yes"
                                    result["Robots Block Rule"] = blocking_rule
                                    result["Indexable"] = "No"
                                    result["Indexability Reason"] = f"Blocked by robots.txt: {blocking_rule}"
                                    if self.respect_robots:
                                        return result
                                result = update_redirect_label(result, url)
                                self.recent_results.append(result)
                                if len(self.recent_results) >= SAVE_INTERVAL:
                                    save_results_to_file(self.recent_results, self.save_filename)
                                    self.recent_results = []
                                return result
                            else:
                                data = update_redirect_label(data, url)
                                return data
                    except Exception as e:
                        if attempt == MAX_RETRIES - 1:
                            data["Indexability Reason"] = f"Error: {str(e)}"
                            data["Indexable"] = "No"
                            self.failed_urls.add(url)
                        await asyncio.sleep(min(INITIAL_BACKOFF * (2 ** attempt), MAX_BACKOFF))
                return data
            except Exception as e:
                logging.error(f"Error fetching {url}: {str(e)}")
                data["Indexability Reason"] = f"Error: {str(e)}"
                data["Indexable"] = "No"
                self.failed_urls.add(url)
                return data

    def status_label(self, status_code: int) -> str:
        if 200 <= status_code < 300:
            return "Success"
        elif 300 <= status_code < 400:
            return "Redirect"
        elif 400 <= status_code < 500:
            return "Client Error"
        elif 500 <= status_code < 600:
            return "Server Error"
        else:
            return "Unknown"

    def parse_html_content(self, data: Dict, content: str, headers: Dict, status_code: int, is_final: bool) -> Dict:
        try:
            soup = BeautifulSoup(content, "lxml")
            title_tag = soup.find("title")
            data["Title"] = title_tag.text.strip() if title_tag else ""

            meta_desc = soup.find("meta", attrs={"name": "description"})
            data["Meta Description"] = meta_desc["content"].strip() if meta_desc and "content" in meta_desc.attrs else ""

            h1_tags = soup.find_all("h1")
            data["H1_Count"] = len(h1_tags)
            data["H1"] = h1_tags[0].text.strip() if h1_tags else ""

            canonical_link = soup.find("link", attrs={"rel": "canonical"})
            if canonical_link and "href" in canonical_link.attrs:
                canonical = urljoin(data["Original_URL"], canonical_link["href"])
                parsed = urlparse(canonical)._replace(fragment="")
                data["Canonical_URL"] = urlunparse(parsed)

            meta_robots = soup.find("meta", attrs={"name": "robots"})
            data["Meta Robots"] = meta_robots["content"] if meta_robots and "content" in meta_robots.attrs else ""
            data["X-Robots-Tag"] = headers.get("X-Robots-Tag", "")

            if "noindex" in data["Meta Robots"].lower() or "noindex" in data["X-Robots-Tag"].lower():
                data["Indexable"] = "No"
                data["Indexability Reason"] = "Noindex directive"

            text = soup.get_text()
            data["Word Count"] = len(text.split())
            return data
        except Exception as e:
            logging.error(f"Error parsing HTML: {e}")
            return data

    def stop(self):
        self.stop_event.set()
        logging.info("Stop event set - crawl will halt after current tasks complete")

    def is_stopped(self) -> bool:
        return self.stop_event.is_set()


async def dynamic_frontier_crawl(seed_url: str, checker: URLChecker, include_regex: Optional[str],
                                 exclude_regex: Optional[str], show_partial_callback=None) -> List[Dict]:
    visited: Set[str] = set()
    queued: Set[str] = set()
    results = []
    frontier = asyncio.PriorityQueue()
    seed_url = normalize_url(seed_url)
    if not seed_url:
        return results
    base_netloc = urlparse(seed_url).netloc.lower()
    if not base_netloc:
        return results

    inc, exc = compile_filters(include_regex, exclude_regex)
    await frontier.put((0, seed_url))
    queued.add(seed_url)

    try:
        await checker.setup()
        while not frontier.empty() and len(visited) < DEFAULT_MAX_URLS:
            if checker.is_stopped():
                break
            depth, url = await frontier.get()
            norm_url = normalize_url(url)
            if not norm_url or norm_url in visited:
                continue
            visited.add(norm_url)
            result = await checker.fetch_and_parse(norm_url)
            if result:
                results.append(result)

            discovered_links = await discover_links(norm_url, checker.session, checker.user_agent)
            for link in discovered_links:
                norm_link = normalize_url(link)
                if not norm_link or norm_link in visited or norm_link in queued:
                    continue
                parsed_link = urlparse(norm_link)
                if parsed_link.netloc.lower() != base_netloc:
                    continue
                if not regex_filter(norm_link, inc, exc):
                    continue
                await frontier.put((depth + 1, norm_link))
                queued.add(norm_link)

            crawled_count = len(visited)
            total_unique = len(queued)
            if show_partial_callback:
                show_partial_callback(results, crawled_count, total_unique)
        return results
    finally:
        await checker.close()


async def discover_links(url: str, session: aiohttp.ClientSession, user_agent: str) -> List[str]:
    out = []
    headers = {"User-Agent": user_agent}
    try:
        async with session.get(url, headers=headers, ssl=False, allow_redirects=True) as resp:
            if resp.status == 200 and resp.content_type and resp.content_type.startswith("text/html"):
                content = await resp.text(errors='replace')
                soup = BeautifulSoup(content, "lxml")
                for a in soup.find_all("a", href=True):
                    abs_link = urljoin(url, a["href"])
                    if abs_link.startswith(('http://', 'https://')):
                        out.append(abs_link)
    except Exception as e:
        logging.error(f"Error discovering links from {url}: {e}")
    return list(set(out))


def compile_filters(include_pattern: str, exclude_pattern: str):
    inc = re.compile(include_pattern) if include_pattern else None
    exc = re.compile(exclude_pattern) if exclude_pattern else None
    return inc, exc


def regex_filter(url: str, inc, exc) -> bool:
    if inc and not inc.search(url):
        return False
    if exc and exc.search(url):
        return False
    return True


def normalize_url(url: str) -> str:
    if not url:
        return ""
    url = url.strip()
    if not url.startswith(('http://', 'https://')):
        url = 'https://' + url
    parsed = urlparse(url)._replace(fragment="")
    return urlunparse(parsed)


def update_redirect_label(data: Dict, original_url: str) -> Dict:
    final_url = data.get("Final_URL", "")
    final_status = data.get("Final_Status_Code", "")
    canonical_url = data.get("Canonical_URL", "")
    try:
        final_code = int(final_status)
    except:
        final_code = None

    if canonical_url and canonical_url != final_url:
        data["Indexability Reason"] = "Canonical URL mismatch"
        data["Indexable"] = "No"

    if final_url == original_url:
        data["Final_Status_Type"] = "No Redirect"
    else:
        if final_code == 200:
            data["Final_Status_Type"] = "Redirecting to Live Page"
        elif final_code in (301, 302):
            data["Final_Status_Type"] = "Temporary/Permanent Redirect"
        elif final_code == 404:
            data["Final_Status_Type"] = "Redirecting to Not Found Page"
        elif final_code == 500:
            data["Final_Status_Type"] = "Redirecting to Server Error Page"
        else:
            data["Final_Status_Type"] = f"Status {final_status}"
    return data


def format_and_reorder_df(df):
    rename_map = {
        'Is_Blocked_by_Robots': 'Blocked by Robots.txt',
        'Is_Indexable': 'Indexable',
        'Indexability_Reason': 'Indexability Reason'
    }
    df = df.rename(columns=rename_map)
    main_cols = [
        'Original_URL', 'Content_Type', 'Initial_Status_Code', 'Initial_Status_Type',
        'Indexable', 'Indexability Reason', 'Blocked by Robots.txt', 'Robots Block Rule',
        'Final_URL', 'Final_Status_Code', 'Final_Status_Type', 'Meta Robots', 'X-Robots-Tag',
        'Canonical_URL', 'H1', 'Title', 'Meta Description', 'Word Count', 'Crawl Time',
        'Last Modified', 'HTML Lang', 'Timestamp'
    ]
    other_cols = [col for col in df.columns if col not in main_cols]
    ordered_cols = [col for col in main_cols if col in df.columns] + other_cols
    return df[ordered_cols]


def display_distribution(column_name: str, title: str, df: pd.DataFrame):
    if column_name in df.columns:
        counts = df[column_name].value_counts(dropna=False).reset_index()
        counts.columns = [column_name, "Count"]
        st.write(f"**{title}**")
        st.table(counts)


def show_summary(df: pd.DataFrame):
    st.subheader("Summary")
    if df.empty:
        st.write("No data available for summary.")
        return
    display_distribution("Initial_Status_Code", "Initial Status Code Distribution", df)
    display_distribution("Final_Status_Code", "Final Status Code Distribution", df)
    display_distribution("Blocked by Robots.txt", "Blocked by Robots.txt?", df)
    display_distribution("Indexable", "Indexable?", df)
    display_distribution("Indexability Reason", "Indexability Reasons", df)


async def run_dynamic_crawl(seed_url: str, checker: URLChecker, include_regex: str, exclude_regex: str,
                           show_partial_callback) -> List[Dict]:
    results = await dynamic_frontier_crawl(
        seed_url=seed_url.strip(),
        checker=checker,
        include_regex=include_regex,
        exclude_regex=exclude_regex,
        show_partial_callback=show_partial_callback
    )
    if checker.failed_urls:
        results += await checker.recrawl_failed_urls()
    await checker.close()
    return results


def main():
    st.set_page_config(layout="wide")
    st.title("Web Crawler")
    st.sidebar.header("Configuration")

    ua_mode = st.sidebar.radio("User Agent Mode", ["Preset", "Custom"], horizontal=True)
    if ua_mode == "Preset":
        ua_choice = st.sidebar.selectbox("User Agent", list(USER_AGENTS.keys()))
        user_agent = USER_AGENTS[ua_choice]
    else:
        user_agent = st.sidebar.text_input("Custom User Agent", value=DEFAULT_USER_AGENT)

    speed_mode = st.sidebar.radio("Speed Mode", ["Safe", "Dynamic", "Custom"], horizontal=True)
    if speed_mode == "Safe":
        concurrency = DEFAULT_CONCURRENCY
    elif speed_mode == "Dynamic":
        concurrency = st.sidebar.slider("Initial Urls/s", MIN_CONCURRENCY, MAX_CONCURRENCY, DEFAULT_CONCURRENCY)
    else:
        concurrency = st.sidebar.slider("Urls/s", MIN_CONCURRENCY, MAX_CONCURRENCY, DEFAULT_CONCURRENCY)

    respect_robots = st.sidebar.checkbox("Respect robots.txt", value=True)
    mode = st.radio("Select Mode", ["Spider", "List", "Sitemap"], horizontal=True)
    st.write("----")

    if 'is_crawling' not in st.session_state:
        st.session_state['is_crawling'] = False
    if 'crawl_done' not in st.session_state:
        st.session_state['crawl_done'] = False
    if 'checker' not in st.session_state:
        st.session_state['checker'] = None
    if 'crawl_results' not in st.session_state:
        st.session_state['crawl_results'] = []

    if mode == "Spider":
        st.subheader("Spider Mode")
        seed_url = st.text_input("Seed URL", placeholder="Enter a single URL")
        include_sitemaps = st.checkbox("Include Sitemaps")
        sitemap_urls = []
        if include_sitemaps:
            sitemaps_text = st.text_area("Sitemap URLs (one per line)", "")
            if sitemaps_text.strip():
                raw_sitemaps = [s.strip() for s in sitemaps_text.splitlines() if s.strip()]
                with st.expander("Discovered Sitemap URLs", expanded=True):
                    table_ph = st.empty()
                    def show_partial(urls):
                        table_ph.dataframe(pd.DataFrame(urls, columns=["Discovered URLs"]), height=500, use_container_width=True)
                    loop = asyncio.new_event_loop()
                    sitemap_urls = loop.run_until_complete(process_sitemaps(raw_sitemaps, show_partial))
                    st.write(f"Collected {len(sitemap_urls)} URLs from sitemaps.")

        with st.expander("Advanced Filters (Optional)"):
            include_pattern = st.text_input("Include Regex", "")
            exclude_pattern = st.text_input("Exclude Regex", "")

        crawl_btn_label = "Stop Crawl" if st.session_state['is_crawling'] else "Start Crawl"
        crawl_btn = st.button(crawl_btn_label)
        progress_bar = st.progress(0.0)
        progress_ph = st.empty()
        table_ph = st.empty()
        download_ph = st.empty()

        def show_partial_data(res_list, crawled_count, discovered_count):
            ratio = crawled_count / discovered_count if discovered_count > 0 else 0
            progress_bar.progress(ratio)
            remain = discovered_count - crawled_count
            pct = ratio * 100
            progress_ph.write(f"Completed {crawled_count} of {discovered_count} ({pct:.2f}%) → {remain} Remaining")
            df_temp = pd.DataFrame(res_list)
            df_temp = format_and_reorder_df(df_temp)
            table_ph.dataframe(df_temp, height=500, use_container_width=True)

        if crawl_btn:
            if not st.session_state['is_crawling']:
                if not seed_url.strip():
                    st.warning("No seed URL provided.")
                    return
                st.session_state.update({
                    'is_crawling': True,
                    'crawl_results': [],
                    'crawl_done': False
                })
                checker = URLChecker(user_agent, concurrency, DEFAULT_TIMEOUT, respect_robots)
                st.session_state['checker'] = checker
                loop = asyncio.new_event_loop()
                asyncio.set_event_loop(loop)
                try:
                    results = loop.run_until_complete(
                        run_dynamic_crawl(
                            seed_url=normalize_url(seed_url),
                            checker=checker,
                            include_regex=include_pattern,
                            exclude_regex=exclude_pattern,
                            show_partial_callback=show_partial_data
                        )
                    )
                    st.session_state['crawl_results'] = results
                    st.session_state['crawl_done'] = True
                finally:
                    loop.close()
                st.session_state['is_crawling'] = False
            else:
                if st.session_state['checker']:
                    st.session_state['checker'].stop()
                    st.info("Stopping crawl after current tasks complete...")

        if st.session_state['crawl_done'] and st.session_state['crawl_results']:
            df_final = pd.DataFrame(st.session_state['crawl_results'])
            df_final = format_and_reorder_df(df_final)
            table_ph.dataframe(df_final, height=500, use_container_width=True)
            csv_data = df_final.to_csv(index=False)
            col1, col2 = st.columns(2)
            with col1:
                download_ph.download_button(label="Download CSV", data=csv_data, file_name="crawl_results.csv",
                                          mime="text/csv")
            with col2:
                copy_button(text=csv_data)

    elif mode == "List":
        st.subheader("List Mode")
        list_input = st.text_area("Enter URLs (one per line)")
        if st.button("Start Crawl"):
            urls = [u.strip() for u in list_input.splitlines() if u.strip()]
            if not urls:
                st.warning("No URLs provided.")
                return
            progress_bar = st.progress(0.0)
            progress_ph = st.empty()
            table_ph = st.empty()
            def show_partial_data(res_list, done_count, total_count):
                progress_bar.progress(done_count / total_count if total_count else 1.0)
                progress_ph.write(f"Completed {done_count} of {total_count}")
                df_temp = pd.DataFrame(res_list)
                df_temp = format_and_reorder_df(df_temp)
                table_ph.dataframe(df_temp, height=500, use_container_width=True)
            checker = URLChecker(user_agent, concurrency, DEFAULT_TIMEOUT, respect_robots)
            loop = asyncio.new_event_loop()
            asyncio.set_event_loop(loop)
            results = loop.run_until_complete(run_list_crawl(urls, checker, show_partial_data))
            loop.close()
            if results:
                df = pd.DataFrame(results)
                df = format_and_reorder_df(df)
                st.dataframe(df, use_container_width=True)
                csv_data = df.to_csv(index=False)
                col1, col2 = st.columns(2)
                with col1:
                    st.download_button("Download CSV", csv_data, "crawl_results.csv", "text/csv")
                with col2:
                    copy_button(text=csv_data)
                show_summary(df)

    elif mode == "Sitemap":
        st.subheader("Sitemap Mode")
        sitemap_text = st.text_area("Sitemap URLs (one per line)", "")
        if st.button("Fetch & Crawl Sitemaps"):
            lines = [x.strip() for x in sitemap_text.splitlines() if x.strip()]
            if not lines:
                st.warning("No sitemap URLs provided.")
                return
            with st.expander("Discovered Sitemap URLs", expanded=True):
                table_ph = st.empty()
                def show_partial(urls):
                    table_ph.dataframe(pd.DataFrame(urls, columns=["Discovered URLs"]),
                                       height=500, use_container_width=True)
                loop = asyncio.new_event_loop()
                sitemap_urls = loop.run_until_complete(process_sitemaps(lines, show_partial))
                loop.close()
                if not sitemap_urls:
                    st.warning("No URLs found in these sitemaps.")
                    return
            progress_bar = st.progress(0.0)
            progress_ph = st.empty()
            table_ph = st.empty()
            def show_partial_data(res_list, done_count, total_count):
                progress_bar.progress(done_count / total_count if total_count else 1.0)
                progress_ph.write(f"Completed {done_count} of {total_count}")
                df_temp = pd.DataFrame(res_list)
                df_temp = format_and_reorder_df(df_temp)
                table_ph.dataframe(df_temp, height=500, use_container_width=True)
            checker = URLChecker(user_agent, concurrency, DEFAULT_TIMEOUT, respect_robots)
            loop = asyncio.new_event_loop()
            results = loop.run_until_complete(
                run_sitemap_crawl(sitemap_urls, checker, show_partial_data))
            loop.close()
            if results:
                df = pd.DataFrame(results)
                df = format_and_reorder_df(df)
                st.dataframe(df, use_container_width=True)
                csv_data = df.to_csv(index=False)
                col1, col2 = st.columns(2)
                with col1:
                    st.download_button("Download CSV", csv_data, "crawl_results.csv", "text/csv")
                with col2:
                    copy_button(text=csv_data)
                show_summary(df)


@retry(stop=stop_after_attempt(3), wait=wait_exponential(multiplier=1, max=60))
async def process_sitemaps(sitemap_urls: List[str], show_partial_callback=None) -> List[str]:
    tasks = [async_parse_sitemap(url) for url in sitemap_urls]
    all_urls = []
    for future in asyncio.as_completed(tasks):
        urls = await future
        all_urls.extend(urls)
        if show_partial_callback:
            show_partial_callback(all_urls)
    return all_urls


async def async_parse_sitemap(url: str) -> List[str]:
    try:
        async with aiohttp.ClientSession() as session:
            async with session.get(url, ssl=False, timeout=10) as response:
                if response.status == 200:
                    content = await response.text()
                    if '<?xml' in content:
                        root = ET.fromstring(content)
                        if root.tag.endswith('sitemapindex'):
                            sitemap_urls = [s.text.strip() for s in root.findall('.//{*}sitemap/{*}loc')]
                            tasks = [async_parse_sitemap(u) for u in sitemap_urls]
                            nested = await asyncio.gather(*tasks)
                            return sum(nested, [])
                        else:
                            return [u.text.strip() for u in root.findall('.//{*}url/{*}loc')]
                    return [line.strip() for line in content.splitlines() if line.strip() and not line.startswith('#')]
    except Exception as e:
        logging.error(f"Error parsing sitemap {url}: {e}")
    return []


async def chunk_process(urls: List[str], checker: URLChecker, show_partial_callback=None) -> List[Dict]:
    results = []
    total = len(urls)
    try:
        await checker.setup()
        tasks = [checker.fetch_and_parse(url) for url in urls]
        for future in asyncio.as_completed(tasks):
            result = await future
            results.append(result)
            if show_partial_callback:
                show_partial_callback(results, len(results), total)
    finally:
        await checker.close()
    return results


async def run_list_crawl(urls: List[str], checker: URLChecker, show_partial_callback) -> List[Dict]:
    results = await chunk_process(urls, checker, show_partial_callback)
    if checker.failed_urls:
        results += await checker.recrawl_failed_urls()
    await checker.close()
    return results


async def run_sitemap_crawl(urls: List[str], checker: URLChecker, show_partial_callback) -> List[Dict]:
    results = await chunk_process(urls, checker, show_partial_callback)
    if checker.failed_urls:
        results += await checker.recrawl_failed_urls()
    await checker.close()
    return results


if __name__ == "__main__":
    main()

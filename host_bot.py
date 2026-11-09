# -*- coding: utf-8 -*-
"""
ᴛᴇʟᴇɢʀᴀᴍ ꜰɪʟᴇ ʜᴏꜱᴛ ʙᴏᴛ
Host & run Python (.py) / JS (.js) scripts or .zip projects from Telegram.

Install:  pip install "python-telegram-bot>=20" psutil
Run:      BOT_TOKEN=123:ABC OWNER_ID=123456 python host_bot.py
(Node.js must be installed on the host if you want to run .js files.)
"""
import asyncio
import hashlib
import html
import json
import logging
import os
import re
import ipaddress
import math
import shutil
import signal
import socket
import subprocess
import sys
import time
import zipfile
from pathlib import Path

from telegram import (
    InlineKeyboardButton as IB,
    InlineKeyboardMarkup as IM,
    ReplyKeyboardMarkup,
    ReplyKeyboardRemove,
    Update,
)
from telegram.constants import ParseMode
from telegram.error import RetryAfter
from telegram.ext import (
    Application,
    ApplicationHandlerStop,
    CallbackQueryHandler,
    ChatMemberHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

# ───────────────────────── CONFIG ─────────────────────────
BOT_TOKEN = os.getenv("BOT_TOKEN", "PASTE_TOKEN_HERE")  # set BOT_TOKEN as an environment variable, never in the file
OWNER_ID = int(os.getenv("OWNER_ID", "8803261206"))
OWNER_USERNAME = os.getenv("OWNER_USERNAME", "notCoder2006")  # without @
UPDATES_CHANNEL = os.getenv("UPDATES_CHANNEL", "https://t.me/+-Bf3mKcG58xiMDY0")
def _env(name, default):
    try:
        return int(os.getenv(name, str(default)))
    except ValueError:
        return default


# ── capacity / load settings (all can be overridden with environment variables) ──
MAX_FILES = _env("MAX_FILES", 100)                 # files per normal user (owner = unlimited)
MAX_FILE_MB = 20                                   # Telegram bot download limit is 20 MB
STORAGE_MB = _env("STORAGE_MB", 500)               # disk space per normal user (0 = unlimited)
ZIP_MAX_MB = _env("ZIP_MAX_MB", 200)               # max unpacked size of one zip (zip-bomb guard)
ZIP_MAX_FILES = _env("ZIP_MAX_FILES", 5000)
MAX_RUNNING_TOTAL = _env("MAX_RUNNING_TOTAL", 300) # hosted processes running at once (owner exempt)
MAX_RUNNING_PER_USER = _env("MAX_RUNNING_PER_USER", 15)
MEM_LIMIT_MB = _env("MEM_LIMIT_MB", 512)           # RAM per hosted process (needs psutil, 0 = off)
MEM_EMERGENCY_PCT = _env("MEM_EMERGENCY_PCT", 95)  # whole-machine RAM %: stop the biggest user process
LOG_MAX_MB = _env("LOG_MAX_MB", 5)                 # a running file's output.log is cut when bigger
RUN_NICE = _env("RUN_NICE", 10)                    # hosted scripts get lower CPU priority than the bot
RUN_NOFILE = _env("RUN_NOFILE", 2048)              # max open files per hosted process
RUN_FSIZE_MB = _env("RUN_FSIZE_MB", 500)           # max size of any single file a hosted script writes
INSTALL_PARALLEL = _env("INSTALL_PARALLEL", 3)     # pip/npm installs running at the same time
AUTO_APPROVE = False      # True = skip owner review

# Website hosting (.php / .html). Each site gets its own port and an https link.
PUBLIC_HOST = os.getenv("PUBLIC_HOST", "")   # server IP/domain used in links (auto-detected if empty)
WEB_PORT_MIN = int(os.getenv("WEB_PORT_MIN", "20000"))
WEB_PORT_MAX = int(os.getenv("WEB_PORT_MAX", "20999"))
TLS_CERT = os.getenv("TLS_CERT", "")         # optional: your own trusted certificate
TLS_KEY = os.getenv("TLS_KEY", "")

# Force-join: users must be in this group before they can use the bot.
# FORCE_JOIN_CHAT_ID = numeric id of the group (looks like -1001234567890).
# The bot must be an ADMIN in that group so it can check membership.
# Leave it 0 and the banner still shows, but the bot can't check that the user
# really joined (Verify just unlocks). Set the id to make the lock real.
# The owner (OWNER_ID) never sees the banner.
FORCE_JOIN_CHAT_ID = int(os.getenv("FORCE_JOIN_CHAT_ID", "-1004383089614"))
FORCE_JOIN_LINK = os.getenv("FORCE_JOIN_LINK", "https://t.me/+-Bf3mKcG58xiMDY0")
GC_NAME = "𝗡ᴏᴛ 𝗖ᴏᴅᴇʀ 𝗚𝗖 ☼"
# ───────────────────────────────────────────────────────────

BASE = Path(__file__).resolve().parent
USERS_DIR = BASE / "user_files"
DB_PATH = BASE / "host_db.json"
USERS_DIR.mkdir(exist_ok=True)
WEB_DIR = BASE / "web_runtime"
WEB_DIR.mkdir(exist_ok=True)
START_TIME = time.time()

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger("hostbot")

# ───────────────────── small-caps font ─────────────────────
_SC = dict(zip("abcdefghijklmnopqrstuvwxyz", "ᴀʙcᴅᴇꜰɢʜɪᴊᴋʟᴍɴoᴘǫʀꜱᴛᴜᴠᴡxʏᴢ"))
_SKIP = re.compile(r"(<code>.*?</code>|<pre>.*?</pre>|<[^>]+>)", re.S)


def sc(text: str) -> str:
    """Convert static text to small caps (HTML tags / <code> are left alone)."""
    out = []
    for part in _SKIP.split(text):
        if part and _SKIP.fullmatch(part):
            out.append(part)
        else:
            out.append("".join("Đ" if c == "D" else _SC.get(c.lower(), c) for c in part))
    return "".join(out)


def esc(x) -> str:
    return html.escape(str(x))


# bot name in the stylized font: ཌɴoᴛ coᴅᴇʀ 〆ʜoꜱᴛɪɴɢ ʙoᴛ
BRAND = "ཌ" + sc("Not Coder") + " 〆" + sc("Hosting Bot")


# ───────────────────────── database ────────────────────────
DB = {"users": {}, "files": {}, "banned": [], "verified": [], "admins": [], "groups": {}}
if DB_PATH.exists():
    try:
        DB.update(json.loads(DB_PATH.read_text()))
    except Exception:
        log.exception("could not load db")


_DIRTY = {"v": False}


def _write_db(data):
    tmp = DB_PATH.with_suffix(".tmp")
    tmp.write_text(data)
    tmp.replace(DB_PATH)


def save():
    """Cheap: just marks the DB dirty. db_flusher() writes it (batched, off the event loop)."""
    _DIRTY["v"] = True


def save_now():
    """Immediate blocking write (used on shutdown)."""
    _DIRTY["v"] = False
    _write_db(json.dumps(DB, separators=(",", ":")))


async def db_flusher():
    while True:
        await asyncio.sleep(2)
        if _DIRTY["v"]:
            _DIRTY["v"] = False
            data = json.dumps(DB, separators=(",", ":"))  # snapshot on the loop thread (safe)
            try:
                await asyncio.to_thread(_write_db, data)
            except Exception:
                _DIRTY["v"] = True
                log.exception("db write failed")


def resolve_target(tok):
    """Chat ID or @username (of someone who has used this bot) -> int id, else None."""
    tok = (tok or "").strip()
    if re.fullmatch(r"-?\d{5,15}", tok):
        return int(tok)
    name = tok.lstrip("@").lower()
    if re.fullmatch(r"[a-z]\w{3,31}", name):
        for u, r in DB["users"].items():
            if (r.get("username") or "").lower() == name:
                return int(u)
    return None


def dir_size_mb(path: Path) -> float:
    total = 0
    stack = [str(path)]
    while stack:
        try:
            with os.scandir(stack.pop()) as it:
                for e in it:
                    try:
                        if e.is_dir(follow_symlinks=False):
                            stack.append(e.path)
                        else:
                            total += e.stat(follow_symlinks=False).st_size
                    except OSError:
                        pass
        except OSError:
            pass
    return total / (1024 * 1024)


def user_files(uid):
    return [(fid, r) for fid, r in DB["files"].items() if r["uid"] == uid]


def is_owner(uid):
    return uid == OWNER_ID


# ───────────────────── website hosting (.php / .html) ─────────────────────
WEB = {"host": PUBLIC_HOST, "cert": "", "key": "", "self_signed": False}
WEB_LAUNCHER = WEB_DIR / "site_server.py"
WEB_ROUTER = WEB_DIR / "router.php"
RUNNER = WEB_DIR / "runner.py"
RUNNER_SRC = r"""
import os, sys
try:
    import resource
except ImportError:
    resource = None
INF = getattr(resource, "RLIM_INFINITY", -1)


def cap(which, soft, hard_too=False):
    try:
        _s, h = resource.getrlimit(which)
        v = soft if h == INF else min(soft, h)
        resource.setrlimit(which, (v, v if hard_too else h))
    except Exception:
        pass


try:
    os.nice(int(os.environ.get("RUN_NICE", "10")))
except Exception:
    pass
if resource:
    cap(resource.RLIMIT_NOFILE, int(os.environ.get("RUN_NOFILE", "2048")))
    cap(resource.RLIMIT_FSIZE, int(os.environ.get("RUN_FSIZE_MB", "500")) * 1048576, True)
    cap(resource.RLIMIT_CORE, 0, True)
os.execvp(sys.argv[1], sys.argv[1:])
"""
URL_DIR = WEB_DIR / "urls"
URL_DIR.mkdir(exist_ok=True)


def tunnel_path():
    """cloudflared gives every site a public, trusted https link without opening any ports."""
    if os.getenv("WEB_TUNNEL", "auto").lower() in ("off", "0", "no"):
        return ""
    return shutil.which("cloudflared") or ""

# Runs as a normal hosted process (so Start/Stop/Restart/Logs/Ban all work). Stdlib only.
SITE_SERVER_SRC = r"""
import asyncio, os, shutil, socket, ssl, subprocess, sys, tempfile, threading
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer

ROOT = os.getcwd()
PORT = int(os.environ["SITE_PORT"])
KIND = os.environ.get("SITE_KIND", "html")
CERT, KEY = os.environ.get("TLS_CERT", ""), os.environ.get("TLS_KEY", "")
ROUTER = os.environ.get("SITE_ROUTER", "")
TUNNEL = os.environ.get("SITE_TUNNEL", "")       # path to cloudflared (public https, no port forwarding)
URL_FILE = os.environ.get("SITE_URL_FILE", "")
BIND = "127.0.0.1" if TUNNEL else "0.0.0.0"      # behind a tunnel only localhost needs to listen

ctx = None
if not TUNNEL and CERT and KEY and os.path.exists(CERT) and os.path.exists(KEY):
    ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
    ctx.load_cert_chain(CERT, KEY)
print("site root:", ROOT, "| port:", PORT, "| kind:", KIND, "| https:", bool(ctx), "| tunnel:", bool(TUNNEL), flush=True)


def start_tunnel():
    import re
    if not TUNNEL:
        return
    if URL_FILE and os.path.exists(URL_FILE):
        os.remove(URL_FILE)
    p = subprocess.Popen([TUNNEL, "tunnel", "--no-autoupdate", "--url", "http://127.0.0.1:%d" % PORT],
                         stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)

    def reader():
        for line in p.stderr:  # keep draining so the pipe never fills
            m = re.search(r"https://[a-z0-9-]+\.trycloudflare\.com", line)
            if m and URL_FILE:
                with open(URL_FILE, "w") as f:
                    f.write(m.group(0))
                print("tunnel url:", m.group(0), flush=True)
        print("tunnel exited", flush=True)
        os._exit(1)

    threading.Thread(target=reader, daemon=True).start()


def hidden(path):
    return any(seg.startswith(".") for seg in path.split("?")[0].split("/") if seg)


class Handler(SimpleHTTPRequestHandler):
    def __init__(self, *a, **k):
        super().__init__(*a, directory=ROOT, **k)

    def send_head(self):
        if hidden(self.path):
            self.send_error(404)
            return None
        return super().send_head()

    def list_directory(self, path):
        self.send_error(403, "Directory listing disabled")
        return None

    def log_message(self, *a):
        pass


class Server(ThreadingHTTPServer):
    daemon_threads = True
    request_queue_size = 64

    def process_request_thread(self, request, client_address):
        if ctx:  # TLS handshake in the worker thread so a slow client can't block accept()
            try:
                request.settimeout(10)
                request = ctx.wrap_socket(request, server_side=True)
                request.settimeout(30)
            except Exception:
                self.shutdown_request(request)
                return
        super().process_request_thread(request, client_address)


def run_html():
    srv = Server((BIND, PORT), Handler)
    start_tunnel()
    srv.serve_forever()


def free_port():
    s = socket.socket()
    s.bind(("127.0.0.1", 0))
    p = s.getsockname()[1]
    s.close()
    return p


async def pipe(r, w):
    try:
        while True:
            d = await r.read(65536)
            if not d:
                break
            w.write(d)
            await w.drain()
    except Exception:
        pass
    finally:
        try:
            w.close()
        except Exception:
            pass


async def proxy(inner):
    async def handle(r, w):
        try:
            br, bw = await asyncio.open_connection("127.0.0.1", inner)
        except Exception:
            w.close()
            return
        await asyncio.gather(pipe(r, bw), pipe(br, w))

    kw = {"ssl": ctx, "ssl_handshake_timeout": 10} if ctx else {}
    srv = await asyncio.start_server(handle, BIND, PORT, **kw)
    async with srv:
        await srv.serve_forever()


def run_php():
    php = shutil.which("php")
    if not php:
        print("PHP is not installed on this host (Termux: pkg install php)", flush=True)
        sys.exit(1)
    inner = free_port()
    allowed = os.pathsep.join([ROOT, tempfile.gettempdir()] + ([os.path.dirname(ROUTER)] if ROUTER else []))
    cmd = [php, "-S", "127.0.0.1:%d" % inner, "-t", ROOT,
           "-d", "disable_functions=exec,passthru,shell_exec,system,proc_open,popen,pcntl_exec,mail",
           "-d", "open_basedir=" + allowed]
    if ROUTER:
        cmd.append(ROUTER)
    env = dict(os.environ, PHP_CLI_SERVER_WORKERS="4")
    p = subprocess.Popen(cmd, env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    def watch():
        p.wait()
        print("php backend exited with code", p.returncode, flush=True)
        os._exit(1)

    threading.Thread(target=watch, daemon=True).start()
    for _ in range(50):  # wait until php accepts connections
        try:
            socket.create_connection(("127.0.0.1", inner), 0.2).close()
            break
        except OSError:
            import time
            time.sleep(0.1)
    start_tunnel()
    asyncio.run(proxy(inner))


run_php() if KIND == "php" else run_html()
"""

ROUTER_SRC = """<?php
// blocks dotfiles (.env, .git ...) then lets the built-in server handle the request normally
$p = parse_url($_SERVER["REQUEST_URI"], PHP_URL_PATH);
foreach (explode("/", (string)$p) as $seg) {
    if ($seg !== "" && $seg[0] === ".") { http_response_code(404); exit; }
}
return false;
"""


def _detect_ip():
    import urllib.request
    for u in ("https://api.ipify.org", "https://ifconfig.me/ip"):
        try:
            return urllib.request.urlopen(u, timeout=4).read().decode().strip()
        except Exception:
            pass
    return ""


def _make_cert(host, cert, key):
    ossl = shutil.which("openssl")
    if not ossl or not host:
        return False
    try:
        ipaddress.ip_address(host)
        san = "IP:" + host
    except ValueError:
        san = "DNS:" + host
    try:
        r = subprocess.run(
            [ossl, "req", "-x509", "-newkey", "rsa:2048", "-nodes", "-keyout", str(key), "-out", str(cert),
             "-days", "825", "-subj", "/CN=" + host, "-addext", "subjectAltName=" + san],
            capture_output=True, timeout=90)
        return r.returncode == 0
    except Exception:
        return False


async def setup_web():
    """Write the site launcher, find the public IP, prepare the HTTPS certificate."""
    RUNNER.write_text(RUNNER_SRC)
    WEB_LAUNCHER.write_text(SITE_SERVER_SRC)
    WEB_ROUTER.write_text(ROUTER_SRC)
    if not WEB["host"]:
        WEB["host"] = await asyncio.to_thread(_detect_ip)
    if TLS_CERT and TLS_KEY and Path(TLS_CERT).exists() and Path(TLS_KEY).exists():
        WEB["cert"], WEB["key"], WEB["self_signed"] = TLS_CERT, TLS_KEY, False
        return
    cert, key = WEB_DIR / "web_cert.pem", WEB_DIR / "web_key.pem"
    if WEB["host"] and (not cert.exists() or not key.exists() or DB.get("web_host") != WEB["host"]):
        if await asyncio.to_thread(_make_cert, WEB["host"], cert, key):
            DB["web_host"] = WEB["host"]
            save()
    if cert.exists() and key.exists():
        WEB["cert"], WEB["key"], WEB["self_signed"] = str(cert), str(key), True
    else:
        log.warning("no HTTPS certificate (openssl missing or host unknown): sites will use plain http")


def alloc_port():
    used = {r.get("port") for r in DB["files"].values() if r.get("port")}
    for port in range(WEB_PORT_MIN, WEB_PORT_MAX + 1):
        if port in used:
            continue
        with socket.socket() as sk:
            try:
                sk.bind(("0.0.0.0", port))
            except OSError:
                continue
        return port
    return None


def tunnel_url(rec):
    f = URL_DIR / f"{rec['fid']}.txt"
    try:
        if is_running(rec["fid"]) and f.exists():
            return f.read_text().strip()
    except Exception:
        pass
    return ""


async def wait_tunnel_url(rec, secs=25):
    if not tunnel_path():
        return
    for _ in range(int(secs * 2)):
        if tunnel_url(rec):
            return
        await asyncio.sleep(0.5)


def site_url(rec):
    u = tunnel_url(rec)
    if u:
        return u
    scheme = "https" if WEB["cert"] else "http"
    return f"{scheme}://{WEB['host'] or 'YOUR_SERVER_IP'}:{rec['port']}"


def site_note(rec):
    t = sc("🌐 Your site is live:\n") + f"<code>{esc(site_url(rec))}</code>"
    if tunnel_url(rec):
        t += "\n" + sc("🔒 Secure https via Cloudflare. This link changes if the site restarts.")
    elif tunnel_path():
        t += "\n" + sc("⏳ The secure tunnel is still starting. Open Check Files in a few seconds for the link.")
    elif not tunnel_url(rec):
        t += "\n" + sc("⚠️ This direct link only opens if port ") + str(rec["port"]) + sc(
            " is reachable from the internet (not behind mobile data or a router).")
    if tunnel_url(rec) or tunnel_path():
        return quote(t)
    if WEB["cert"] and WEB["self_signed"]:
        t += "\n" + sc("🔒 HTTPS uses a self-signed certificate: if the browser warns, tap Advanced → Continue.")
    elif not WEB["cert"]:
        t += "\n" + sc("⚠️ HTTPS is not available on this host, so the link is plain http.")
    return quote(t)


def find_site_index(d: Path, root_only):
    for name in ("index.php", "index.html", "index.htm"):
        if (d / name).is_file():
            return name
    if root_only:
        return None
    hits = [p for p in d.rglob("*") if p.is_file() and p.name in ("index.php", "index.html", "index.htm")]
    hits.sort(key=lambda p: (len(p.relative_to(d).parts), p.name))
    return str(hits[0].relative_to(d)) if hits else None


# ───────────────────── process manager ─────────────────────
PROCS = {}  # fid -> Popen


def proj_dir(rec) -> Path:
    return USERS_DIR / str(rec["uid"]) / rec["fid"]


def is_running(fid) -> bool:
    p = PROCS.get(fid)
    return p is not None and p.poll() is None


def start_proc(fid):
    rec = DB["files"][fid]
    if is_running(fid):
        return False, "already running"
    main = proj_dir(rec) / rec["main"]
    if not main.exists():
        return False, "main file missing"
    if not is_owner(rec["uid"]):
        live = [f for f in PROCS if is_running(f)]
        if len(live) >= MAX_RUNNING_TOTAL:
            return False, "the server is at full capacity right now, please try again later"
        mine = sum(1 for f in live if DB["files"].get(f, {}).get("uid") == rec["uid"])
        if mine >= MAX_RUNNING_PER_USER:
            return False, f"you can run at most {MAX_RUNNING_PER_USER} files at the same time, stop one first"
    udir = USERS_DIR / str(rec["uid"])
    env = os.environ.copy()
    env.pop("BOT_TOKEN", None)  # never leak the host token to hosted scripts
    env["PYTHONPATH"] = str(udir / "libs") + os.pathsep + env.get("PYTHONPATH", "")
    env["NODE_PATH"] = str(udir / "node_modules")
    env["PYTHONUNBUFFERED"] = "1"
    if rec["type"] == "web":
        if rec.get("web") == "php" and not shutil.which("php"):
            return False, "PHP is not installed on this host. Owner: run `pkg install php` (Termux) or `apt install php-cli`."
        if not WEB_LAUNCHER.exists():
            return False, "web server is not ready yet, try again in a few seconds"
        env.update(SITE_PORT=str(rec["port"]), SITE_KIND=rec.get("web", "html"), TLS_CERT=WEB["cert"],
                   TLS_KEY=WEB["key"], SITE_ROUTER=str(WEB_ROUTER), SITE_TUNNEL=tunnel_path(),
                   SITE_URL_FILE=str(URL_DIR / f"{rec['fid']}.txt"))
        cmd = [sys.executable, "-u", str(WEB_LAUNCHER)]
    else:
        cmd = [sys.executable, "-u", main.name] if rec["type"] == "py" else ["node", main.name]
    logf = main.parent / "output.log"
    if RUNNER.exists():  # lower priority + file/size limits, then exec the real command
        env.update(RUN_NICE=str(RUN_NICE), RUN_NOFILE=str(RUN_NOFILE), RUN_FSIZE_MB=str(RUN_FSIZE_MB))
        cmd = [sys.executable, str(RUNNER)] + cmd
    fd = None
    try:
        # fresh log per start; O_APPEND so the monitor can truncate a huge log safely
        fd = os.open(logf, os.O_WRONLY | os.O_CREAT | os.O_TRUNC | os.O_APPEND, 0o644)
        PROCS[fid] = subprocess.Popen(
            cmd, cwd=main.parent, env=env, stdout=fd, stderr=subprocess.STDOUT,
            stdin=subprocess.DEVNULL, start_new_session=True,
        )
    except Exception as e:
        return False, str(e)
    finally:
        if fd is not None:
            os.close(fd)  # the child has its own copy; leaving this open leaked one fd per start
    rec["status"] = "running"
    save()
    return True, "ok"


def _force_kill(p):
    if p.poll() is None:
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except Exception:
            pass


def stop_proc(fid, mark=True):
    p = PROCS.pop(fid, None)
    if p and p.poll() is None:
        try:
            os.killpg(p.pid, signal.SIGTERM)
        except Exception:
            pass
        try:  # don't block the bot: force-kill later if it ignores SIGTERM
            asyncio.get_running_loop().call_later(5, _force_kill, p)
        except RuntimeError:
            try:
                p.wait(timeout=5)
            except Exception:
                _force_kill(p)
    if mark and fid in DB["files"] and DB["files"][fid]["status"] == "running":
        DB["files"][fid]["status"] = "stopped"
        save()


async def run_cmd(cmd, cwd=None, timeout=300):
    p = await asyncio.create_subprocess_exec(
        *cmd, cwd=cwd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.STDOUT
    )
    try:
        out, _ = await asyncio.wait_for(p.communicate(), timeout)
    except asyncio.TimeoutError:
        p.kill()
        return 1, "timeout"
    return p.returncode, out.decode(errors="ignore")


# ───────────────────────── keyboards ───────────────────────
BG = set()
LAUNCHING = set()


def spawn(coro):
    t = asyncio.create_task(coro)
    BG.add(t)
    t.add_done_callback(BG.discard)
    return t


# pip package names that differ from the import name
PKG_MAP = {
    "cv2": "opencv-python", "PIL": "Pillow", "bs4": "beautifulsoup4", "yaml": "pyyaml",
    "dotenv": "python-dotenv", "telegram": "python-telegram-bot", "telebot": "pyTelegramBotAPI",
    "sklearn": "scikit-learn", "Crypto": "pycryptodome", "dateutil": "python-dateutil",
    "jwt": "PyJWT", "serial": "pyserial", "discord": "discord.py", "docx": "python-docx",
    "pptx": "python-pptx", "skimage": "scikit-image", "googleapiclient": "google-api-python-client",
    "flask_cors": "flask-cors", "git": "GitPython", "magic": "python-magic", "attr": "attrs",
}
# names that are almost always the user's OWN files: never auto-install these from PyPI
LOCAL_NAMES = {
    "config", "utils", "helpers", "keys", "settings", "database", "db", "bot", "main", "app",
    "constants", "functions", "handlers", "models", "core", "data", "secrets", "credentials",
}


def log_tail(rec, n=3000):
    lp = (proj_dir(rec) / rec["main"]).parent / "output.log"
    if not lp.exists():
        return ""
    return lp.read_bytes()[-n:].decode(errors="ignore")


def missing_pkg(rec, tail):
    if rec["type"] == "py":
        m = re.search(r"No module named '([A-Za-z0-9_\-]+)", tail)
        if not m or m.group(1) in LOCAL_NAMES:
            return None
        pkg = PKG_MAP.get(m.group(1), m.group(1))
    else:
        m = re.search(r"Cannot find module '([^'./][^']*)'", tail)
        if not m:
            return None
        pkg = m.group(1)
    return pkg if PKG_RE.match(pkg) else None


# Termux/Android: Python 3.13+ reports sys.platform == "android", so many PyPI source builds
# (psutil, numpy, pillow, cryptography ...) refuse to compile. Termux ships patched builds
# as "python-<name>" packages, so we fall back to those.
ON_ANDROID = (sys.platform == "android" or hasattr(sys, "getandroidapilevel")
              or "com.termux" in os.environ.get("PREFIX", ""))
TERMUX_NAMES = {"pyyaml": "python-yaml", "pillow": "python-pillow", "opencv-python": "opencv-python",
                "scikit-learn": "python-scikit-learn", "beautifulsoup4": "python-beautifulsoup4"}


def _base_name(spec):
    return re.split(r"[<>=!~\[;@ ]", spec)[0].lower().replace("_", "-")


INSTALL_SEM = asyncio.Semaphore(INSTALL_PARALLEL)


async def pip_install(udir, pkgs):
    async with INSTALL_SEM:
        return await _pip_install(udir, pkgs)


async def _pip_install(udir, pkgs):
    """pip install into the user's libs dir; on Android falls back to Termux's own packages."""
    (udir / "libs").mkdir(parents=True, exist_ok=True)
    code, out = await run_cmd(
        [sys.executable, "-m", "pip", "install", "--target", str(udir / "libs"), *pkgs], timeout=600)
    if code == 0 or not ON_ANDROID:
        return code, out
    pkg_bin = shutil.which("pkg")
    if not pkg_bin:
        return code, out + "\n[hint] Android detected but `pkg` not found. Run in Termux: pkg install python-<module>"
    names = [TERMUX_NAMES.get(_base_name(p), "python-" + _base_name(p)) for p in pkgs]
    c2, o2 = await run_cmd(["env", "DEBIAN_FRONTEND=noninteractive", pkg_bin, "install", "-y", *names],
                           timeout=900)
    if c2 == 0:
        return 0, ("pip has no build for Android, installed from the Termux repo instead:\n"
                   + " ".join(names) + "\n" + o2[-500:])
    return code, (out[-600:] + "\n--- termux pkg ---\n" + o2[-600:]
                  + "\n[hint] If the package has no Termux build, install it manually in Termux.")


async def install_requirements(req, udir):
    code, _ = await run_cmd([sys.executable, "-m", "pip", "install", "-r", str(req),
                             "--target", str(udir / "libs")], timeout=600)
    if code == 0 or not ON_ANDROID:
        return
    for line in req.read_text(errors="ignore").splitlines():
        line = line.split("#")[0].strip()
        if line and not line.startswith("-") and PKG_RE.match(line.replace(" ", "")):
            await pip_install(udir, [line.replace(" ", "")])


async def pkg_install(uid, mgr, pkgs):
    udir = USERS_DIR / str(uid)
    udir.mkdir(exist_ok=True)
    if mgr == "py":
        return await pip_install(udir, pkgs)
    async with INSTALL_SEM:
        return await run_cmd(["npm", "install", "--prefix", str(udir), *pkgs])


# ─────────────── install progress dialogue (same style for Manual Install and auto-install) ───────────────
def progress_bar(pct):
    n = max(0, min(10, pct * 10 // 100))
    return "▬" * n + "▭" * (10 - n) + f" {pct}%"


def _card_tail(names):
    return (f"\n\n◈ {sc('Module')} ➤ <code>{esc(names)}</code>"
            f"\n◈ {sc('Owner')} ➤ @{esc(OWNER_USERNAME)}")


def install_card(suffix, pct, names):
    step, label = (1, "Preparing") if pct < 20 else (2, "Downloading") if pct < 70 else (3, "Installing")
    return quote(sc(f"STEP {step}: {label} {suffix}...") + "\n\n" + progress_bar(pct) + _card_tail(names))


def parse_installed(out):
    m = re.search(r"Successfully installed (.+)", out)
    if m:
        return ", ".join(m.group(1).split()[:8])
    m = re.search(r"added (\d+) packages?", out)
    if m:
        return f"{m.group(1)} package(s)"
    m = re.search(r"installed from the Termux repo instead:\n(.+)", out)
    return m.group(1).strip() if m else ""


def done_card(names, out):
    got = parse_installed(out)
    return (quote(sc("✅ Module successfully installed") + "\n\n" + progress_bar(100)
                  + _card_tail(names)
                  + (f"\n◈ {sc('Installed')} ➤ <code>{esc(got)}</code>" if got else "")
                  + f"\n◈ {sc('Saved in')} ➤ " + sc("your private space"))
            + "\n" + sc("Already running file? Restart it so it can use the module."))


def fail_card(names, out):
    return (quote(sc("❌ Install failed") + _card_tail(names))
            + f"\n<pre>{esc((out or 'no output')[-1200:])}</pre>")


async def safe_edit(msg, text):
    if msg is None:
        return
    try:
        await msg.edit_text(text, parse_mode=H)
    except Exception:
        pass  # "not modified", flood wait, or the user deleted the message: never break the install


async def install_with_ui(bot, chat_id, uid, mgr, pkgs, suffix="Module", msg=None):
    """Installs while an animated progress card runs. The percentage is an estimate
    (pip/npm don't report real progress) that creeps up until the install finishes."""
    names = " ".join(pkgs)
    card = install_card(suffix, 5, names)
    if msg is None:
        try:
            msg = await bot.send_message(chat_id, card, parse_mode=H)
        except Exception:
            msg = None
    task = asyncio.ensure_future(pkg_install(uid, mgr, pkgs))
    t0, last = time.time(), 5
    while not task.done():
        await asyncio.wait({task}, timeout=2)
        if task.done():
            break
        pct = min(95, 5 + int(90 * (1 - math.exp(-(time.time() - t0) / 10))))
        if pct != last:
            last = pct
            await safe_edit(msg, install_card(suffix, pct, names))
    try:
        code, out = task.result()
    except Exception as e:
        code, out = 1, str(e)
    await safe_edit(msg, done_card(names, out) if code == 0 else fail_card(names, out))
    return code, out


async def launch(bot, fid, tries=3):
    """Start a file, check it survives the first seconds, auto-install missing modules."""
    rec = DB["files"][fid]
    if is_running(fid):
        return True, "running"
    LAUNCHING.add(fid)
    tail = ""
    try:
        for attempt in range(tries + 1):
            ok, msg = start_proc(fid)
            if not ok:
                rec["status"] = "stopped"
                save()
                return False, msg
            await asyncio.sleep(5)
            p = PROCS.get(fid)
            if p is None or p.poll() is None:
                return True, "running"
            tail = log_tail(rec)
            pkg = missing_pkg(rec, tail) if attempt < tries else None
            if not pkg:
                break
            code, out = await install_with_ui(bot, rec["uid"], rec["uid"], rec["type"], [pkg], "Missing module")
            if code != 0:
                tail = f"Could not install {pkg}:\n{out}"
                break
        PROCS.pop(fid, None)
        rec["status"] = "stopped"
        save()
        return False, tail or "process exited immediately with no output"
    finally:
        LAUNCHING.discard(fid)


def crash_text(info):
    return (sc("❌ Your file crashed on startup.\n\n📜 Error log:\n") + f"<pre>{esc(info[-1500:])}</pre>\n"
            + sc("Fix the error and upload again. Missing a module? Use Manual Install."))


async def launch_and_report(bot, fid, chat_id):
    if fid not in DB["files"]:
        return
    ok, info = await launch(bot, fid)
    if not ok:
        await bot.send_message(chat_id, crash_text(info), parse_mode=H)


def scan_load():
    """Runs in a thread. Cuts oversized logs and finds processes that use too much RAM.
    Returns (offenders [(fid, mb, reason)], system_ram_percent)."""
    try:
        import psutil
    except ImportError:
        psutil = None
    over, usage = [], {}
    for fid, p in list(PROCS.items()):
        rec = DB["files"].get(fid)
        if not rec or p.poll() is not None:
            continue
        try:  # keep logs small
            logf = (proj_dir(rec) / rec["main"]).parent / "output.log"
            if logf.exists() and logf.stat().st_size > LOG_MAX_MB * 1024 * 1024:
                os.truncate(logf, 0)
        except Exception:
            pass
        if not psutil:
            continue
        try:
            root = psutil.Process(p.pid)
            rss = root.memory_info().rss
            for c in root.children(recursive=True):
                try:
                    rss += c.memory_info().rss
                except Exception:
                    pass
            mb = rss // (1024 * 1024)
            usage[fid] = mb
            if MEM_LIMIT_MB and mb > MEM_LIMIT_MB and not is_owner(rec["uid"]):
                over.append((fid, mb, "memory limit"))
        except Exception:
            pass
    pct = 0
    if psutil:
        try:
            pct = psutil.virtual_memory().percent
            if MEM_EMERGENCY_PCT and pct >= MEM_EMERGENCY_PCT and not over:
                cand = [(mb, f) for f, mb in usage.items() if not is_owner(DB["files"][f]["uid"])]
                if cand:
                    mb, f = max(cand)
                    over.append((f, mb, "server memory almost full"))
        except Exception:
            pass
    return over, pct


async def monitor(app):
    """Tell users when a running file dies, and keep the machine healthy under load."""
    while True:
        await asyncio.sleep(20)
        for fid, rec in list(DB["files"].items()):
            if rec["status"] == "running" and fid not in LAUNCHING and not is_running(fid):
                rec["status"] = "stopped"
                save()
                try:
                    await app.bot.send_message(
                        rec["uid"],
                        sc("⚠️ Your file ") + f"<code>{esc(rec['name'])}</code>"
                        + sc(" stopped running.\n\n📜 Last output:\n")
                        + f"<pre>{esc(log_tail(rec)[-1500:] or 'no output')}</pre>", parse_mode=H)
                except Exception:
                    pass
        try:
            over, pct = await asyncio.to_thread(scan_load)
        except Exception:
            log.exception("scan_load failed")
            continue
        for fid, mb, why in over:
            rec = DB["files"].get(fid)
            if not rec:
                continue
            stop_proc(fid)
            try:
                await app.bot.send_message(
                    rec["uid"],
                    sc("⛔ Your file ") + f"<code>{esc(rec['name'])}</code>"
                    + sc(f" was stopped: {why} ({mb} MB used"
                         + (f", limit {MEM_LIMIT_MB} MB" if why == "memory limit" else "") + "). "
                         "Reduce its memory use and start it again."), parse_mode=H)
                if why != "memory limit":
                    await app.bot.send_message(
                        OWNER_ID, sc(f"⚠️ Server RAM at {pct}%: stopped ") + f"<code>{esc(rec['name'])}</code>"
                        + sc(f" of user {rec['uid']} ({mb} MB)."), parse_mode=H)
            except Exception:
                pass


L = {
    "updates": sc("📢 Updates Channel"),
    "upload": sc("📤 Upload File"),
    "check": sc("📂 Check Files"),
    "speed": sc("⚡ Bot Speed"),
    "stats": sc("📊 Statistics"),
    "contact": sc("📞 Contact Owner"),
    "manual": sc("📦 Manual Install"),
    "help": sc("🆘 Help"),
}
MAIN_KB = ReplyKeyboardMarkup(
    [
        [L["updates"]],
        [L["upload"], L["check"]],
        [L["speed"], L["stats"]],
        [L["contact"]],
        [L["manual"], L["help"]],
    ],
    resize_keyboard=True,
)
H = ParseMode.HTML
L.update({
    "broadcast": sc("📣 Broadcast"),
    "admin": sc("👮 Admin"),
    "ban": sc("🚫 Ban User"),
    "users": sc("👥 View Users"),
    "group": sc("🔗 Group"),
})


def main_kb(uid):
    """Main menu. Owner sees all panel buttons, admins see Ban User + View Users."""
    rows = [
        [L["updates"]],
        [L["upload"], L["check"]],
        [L["speed"], L["stats"]],
        [L["contact"]],
        [L["manual"], L["help"]],
    ]
    if is_owner(uid):
        rows += [[L["broadcast"], L["admin"]], [L["ban"], L["users"]], [L["group"]]]
    elif uid in DB["admins"]:
        rows += [[L["ban"], L["users"]], [L["group"]]]
    return ReplyKeyboardMarkup(rows, resize_keyboard=True)


_FULL_SC = str.maketrans("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ",
                         "ᴀʙᴄᴅᴇꜰɢʜɪᴊᴋʟᴍɴᴏᴘǫʀꜱᴛᴜᴠᴡxʏᴢᴀʙᴄᴅᴇꜰɢʜɪᴊᴋʟᴍɴᴏᴘǫʀꜱᴛᴜᴠᴡxʏᴢ")


def sc_full(text: str) -> str:
    """Complete small caps (also c -> ᴄ and o -> ᴏ), like ᴅᴀꜱʜʙᴏᴀʀᴅ."""
    return text.translate(_FULL_SC)


def banned_text():
    return ("<blockquote>" + sc_full("🚫 You have been banned for using the bot without joining the owner's GC, "
                                     "contact the owner ") + f"@{esc(OWNER_USERNAME)}"
            + sc_full(" to resolve the problem.") + "</blockquote>")


BAN_NOTIFIED = {}


async def notify_banned(bot, uid, force=False):
    """Tell a banned user why (at most once per 10 min unless forced)."""
    if not force and BAN_NOTIFIED.get(uid, 0) > time.time():
        return
    BAN_NOTIFIED[uid] = time.time() + 600
    try:
        await bot.send_message(uid, banned_text(), parse_mode=H, reply_markup=ReplyKeyboardRemove())
    except Exception:
        pass


async def guard(update: Update) -> bool:
    u = update.effective_user
    if u.id in DB["banned"]:
        await notify_banned(update.get_bot(), u.id)
        return False
    rec = DB["users"].setdefault(str(u.id), {"joined": int(time.time())})
    if rec.get("username", "?") != u.username or rec.get("name") != u.full_name:
        rec["username"] = u.username
        rec["name"] = u.full_name
        save()
    if not await is_member(update.get_bot(), u.id):
        chat = update.effective_chat
        if chat and chat.type in ("group", "supergroup"):
            note_attempt(u.id, chat)
            if time.time() - GROUP_BANNER.get(u.id, 0) < 60:
                return False  # already told them a moment ago, don't spam the group
            GROUP_BANNER[u.id] = time.time()
        await send_join_banner(update)
        return False
    return True


GROUP_BANNER = {}


def note_attempt(uid, chat):
    """Log people who use the bot in a group without having joined the owner's GC."""
    a = DB.setdefault("attempts", {}).setdefault(str(uid), {"n": 0})
    a["n"] += 1
    a["chat"] = chat.title or ""
    a["last"] = int(time.time())
    save()


MEMBER_OK = {}  # uid -> time until which a positive membership check is trusted


async def is_member(bot, uid) -> bool:
    if is_owner(uid):
        return True
    if MEMBER_OK.get(uid, 0) > time.time():
        return True
    ok = await _is_member(bot, uid)
    if ok:
        MEMBER_OK[uid] = time.time() + 120
    else:
        MEMBER_OK.pop(uid, None)
    return ok


async def _is_member(bot, uid) -> bool:
    if is_owner(uid):
        return True
    if not FORCE_JOIN_CHAT_ID:
        # no group id set: banner is shown, but joining can't be checked,
        # so a user passes after tapping Verify (set FORCE_JOIN_CHAT_ID to enforce)
        return uid in DB["verified"]
    try:
        m = await bot.get_chat_member(FORCE_JOIN_CHAT_ID, uid)
    except Exception as e:
        log.warning("membership check failed: %s", e)
        if not _FLAGS["gc_err"]:
            _FLAGS["gc_err"] = True  # tell the owner once, not on every click
            try:
                await bot.send_message(
                    OWNER_ID,
                    f"⚠️ Join check failed: {e}\n\nMake sure the bot is ADMIN in the group and "
                    f"FORCE_JOIN_CHAT_ID is correct. Send /checkgc to test.")
            except Exception:
                pass
        return False
    if m.status in ("member", "administrator", "creator"):
        return True
    return m.status == "restricted" and bool(getattr(m, "is_member", False))


def join_banner():
    text = (
        f"<b>{BRAND}</b>\n\n"
        + sc("🔒 Access locked!\n\nJoin first ")
        + f"<b>{GC_NAME}</b>"
        + sc(" to unlock the bot.\n\n👇 Tap Join Group, then tap Verify.")
    )
    kb = IM([
        [IB(sc("🚀 Join Group"), url=FORCE_JOIN_LINK)],
        [IB(sc("✅ Verify"), callback_data="verify")],
    ])
    return text, kb


async def send_join_banner(update: Update):
    text, kb = join_banner()
    await update.effective_message.reply_text(text, parse_mode=H, reply_markup=kb)


# ───────────────────────── handlers ────────────────────────
def welcome_text(u):
    n = len(user_files(u.id))
    limit = "∞" if is_owner(u.id) else MAX_FILES
    text = (
        f"<b>{BRAND}</b>\n\n"
        + sc("👋 Welcome, ") + f"<b>{esc(u.full_name)}</b>!\n\n"
        + sc("🆔 ID: ") + f"<code>{u.id}</code>\n"
        + sc("📁 Files Uploaded: ") + f"<code>{n} / {limit}</code>\n\n"
        + sc("🤖 Host & run Python (.py) or JS (.js) scripts.\n"
             "🌐 Host websites: .php or .html pages with an https link.\n"
             "Upload single files or .zip archives.\n"
             "📦 Manual module installation available\n\n"
             "👇 Use buttons or type commands.")
    )
    return text


async def start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    if not await guard(update):
        return
    await update.message.reply_text(
        welcome_text(update.effective_user), parse_mode=H,
        reply_markup=main_kb(update.effective_user.id))


async def upload_prompt(update, ctx):
    await update.message.reply_text(
        sc("📤 Send your Python (.py), JS (.js), PHP (.php), HTML (.html), or ZIP (.zip) file."), parse_mode=H
    )


async def doc_handler(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    if not await guard(update):
        return
    u = update.effective_user
    doc = update.message.document
    name = os.path.basename(doc.file_name or "file")
    ext = name.rsplit(".", 1)[-1].lower() if "." in name else ""
    if ext not in ("py", "js", "zip", "php", "html", "htm"):
        return await update.message.reply_text(
            sc("❌ Only .py, .js, .php, .html and .zip files are supported."), parse_mode=H)
    if STORAGE_MB and not is_owner(u.id):
        used = await asyncio.to_thread(dir_size_mb, USERS_DIR / str(u.id))
        if used >= STORAGE_MB:
            return await update.message.reply_text(
                sc(f"❌ Your storage is full ({int(used)}/{STORAGE_MB} MB). Delete a file in Check Files first."),
                parse_mode=H)
    if doc.file_size and doc.file_size > MAX_FILE_MB * 1024 * 1024:
        return await update.message.reply_text(
            sc(f"❌ File too large (max {MAX_FILE_MB} MB)."), parse_mode=H)
    if not is_owner(u.id) and len(user_files(u.id)) >= MAX_FILES:
        return await update.message.reply_text(
            sc("❌ File limit reached. Delete a file first."), parse_mode=H)

    fid = hashlib.sha1(f"{u.id}{name}{time.time()}".encode()).hexdigest()[:8]
    rec = {"fid": fid, "uid": u.id, "name": name, "type": "js" if ext == "js" else "py",
           "main": name, "status": "pending", "tg_file": doc.file_id}
    if ext in ("php", "html", "htm"):  # a single page becomes the site's index
        rec.update(type="web", web="php" if ext == "php" else "html",
                   main="index.php" if ext == "php" else "index.html", port=alloc_port())
        if not rec["port"]:
            return await update.message.reply_text(sc("❌ No free web ports on this host."), parse_mode=H)
        if rec["web"] == "php" and not shutil.which("php"):
            return await update.message.reply_text(
                sc("❌ PHP is not installed on this host, so .php sites can't run yet. Contact the owner."),
                parse_mode=H)
    d = proj_dir(rec)
    d.mkdir(parents=True, exist_ok=True)

    await update.message.reply_text(
        sc("✅ Downloaded ") + f"<code>{esc(name)}</code>" + sc(". Processing..."), parse_mode=H)
    tgf = await ctx.bot.get_file(doc.file_id)
    dest = d / (rec["main"] if rec["type"] == "web" else name)
    await tgf.download_to_drive(dest)

    if ext == "zip":
        try:
            main = await asyncio.to_thread(extract_zip, dest, d)
        except Exception as e:
            await asyncio.to_thread(shutil.rmtree, d, True)
            return await update.message.reply_text(
                sc("❌ Bad zip: ") + f"<code>{esc(e)}</code>", parse_mode=H)
        # a root-level index.html/index.php means it's a website; nested ones only if there's no bot code
        site = find_site_index(d, True) or (None if main else find_site_index(d, False))
        if site:
            rec.update(type="web", web="php" if site.endswith(".php") else "html", main=site, port=alloc_port())
            if not rec["port"]:
                await asyncio.to_thread(shutil.rmtree, d, True)
                return await update.message.reply_text(sc("❌ No free web ports on this host."), parse_mode=H)
            if rec["web"] == "php" and not shutil.which("php"):
                await asyncio.to_thread(shutil.rmtree, d, True)
                return await update.message.reply_text(
                    sc("❌ PHP is not installed on this host, so .php sites can't run yet. Contact the owner."),
                    parse_mode=H)
        elif not main:
            await asyncio.to_thread(shutil.rmtree, d, True)
            return await update.message.reply_text(
                sc("❌ No .py/.js entry file or index.html/index.php found in zip."), parse_mode=H)
        else:
            rec["main"] = main
            rec["type"] = "js" if main.endswith(".js") else "py"
            req = (d / main).parent / "requirements.txt"
            if req.exists() and rec["type"] == "py":
                udir = USERS_DIR / str(u.id)
                (udir / "libs").mkdir(parents=True, exist_ok=True)
                spawn(install_requirements(req, udir))

    DB["files"][fid] = rec
    save()

    if is_owner(u.id) or AUTO_APPROVE:
        return await approve_file(ctx, fid)

    await update.message.reply_text(
        sc("⏳ File under security review. You will be notified upon approval."), parse_mode=H)
    kb = IM([[IB(sc("✅ Approve"), callback_data=f"ap:{fid}"),
              IB(sc("❌ Reject"), callback_data=f"rj:{fid}")]])
    cap = (sc("🔔 New file for review\n👤 User: ") + f"<a href='tg://user?id={u.id}'>{esc(u.full_name)}</a> "
           f"(<code>{u.id}</code>)\n" + sc("📄 File: ") + f"<code>{esc(name)}</code>\n"
           + sc("🎯 Entry: ") + f"<code>{esc(rec['main'])}</code>")
    try:
        await ctx.bot.send_document(OWNER_ID, doc.file_id, caption=cap, parse_mode=H, reply_markup=kb)
    except Exception:
        log.exception("owner notify failed")


def extract_zip(zpath: Path, d: Path):
    root = d.resolve()
    with zipfile.ZipFile(zpath) as z:
        infos = z.infolist()
        if len(infos) > ZIP_MAX_FILES or sum(m.file_size for m in infos) > ZIP_MAX_MB * 1024 * 1024:
            raise ValueError(f"zip too big (max {ZIP_MAX_MB} MB unpacked, {ZIP_MAX_FILES} files)")
        for m in z.infolist():
            target = (d / m.filename).resolve()
            if not str(target).startswith(str(root)):
                raise ValueError("unsafe path in zip")
        z.extractall(d)
    zpath.unlink(missing_ok=True)
    files = [p for p in d.rglob("*") if p.is_file() and p.suffix in (".py", ".js")]
    if not files:
        return None
    pref = ["main.py", "bot.py", "app.py", "run.py", "index.js", "main.js", "bot.js", "app.js"]
    files.sort(key=lambda p: (len(p.relative_to(d).parts), p.name))
    for want in pref:
        for p in files:
            if p.name == want:
                return str(p.relative_to(d))
    return str(files[0].relative_to(d))


async def approve_file(ctx, fid):
    rec = DB["files"][fid]
    ok, info = await launch(ctx.bot, fid)
    name = f"<code>{esc(rec['name'])}</code>"
    if ok:
        text = sc("✅ Your file ") + name + sc(" has been approved and started.")
        if rec["type"] == "web":
            await wait_tunnel_url(rec)
            text += "\n\n" + site_note(rec)
    else:
        text = (sc("✅ Your file ") + name + sc(" was approved, but it crashed on startup.\n\n📜 Error log:\n")
                + f"<pre>{esc(info[-1500:])}</pre>\n"
                + sc("Fix the error and upload again. Missing a module? Use Manual Install."))
    await ctx.bot.send_message(rec["uid"], text, parse_mode=H)
    if not ok and not is_owner(rec["uid"]):
        try:
            await ctx.bot.send_message(
                OWNER_ID, sc("⚠️ File ") + name + sc(" from user ") + f"<code>{rec['uid']}</code>"
                + sc(" crashed on startup.\n\n") + f"<pre>{esc(info[-1000:])}</pre>", parse_mode=H)
        except Exception:
            pass


async def check_files(update, ctx):
    if not await guard(update):
        return
    uid = update.effective_user.id
    await update.message.reply_text(**files_view(uid))


def files_view(uid):
    fl = user_files(uid)
    if not fl:
        return dict(text=sc("📂 You have no files yet. Tap Upload File."), parse_mode=H)
    rows = []
    for fid, r in fl:
        ico = "🟢" if is_running(fid) else ("🟡" if r["status"] == "pending" else "🔴")
        rows.append([IB(f"{ico} {r['name']}", callback_data=f"f:{fid}")])
    rows.append([IB(sc("⬅️ Back"), callback_data="home")])
    return dict(text=sc("📂 Your files — tap one to manage:\n🟢 running  🔴 stopped  🟡 pending"),
                parse_mode=H, reply_markup=IM(rows))


def file_menu(fid):
    r = DB["files"][fid]
    state = sc("Running") if is_running(fid) else sc(r["status"].capitalize())
    text = (sc("📄 File: ") + f"<code>{esc(r['name'])}</code>\n"
            + sc("🎯 Entry: ") + f"<code>{esc(r['main'])}</code>\n"
            + sc("📡 Status: ") + f"<b>{state}</b>")
    if r.get("type") == "web":
        text += "\n" + sc("🌐 Link: ") + f"<code>{esc(site_url(r))}</code>"
    kb = IM([
        [IB(sc("▶️ Start"), callback_data=f"st:{fid}"), IB(sc("⏹ Stop"), callback_data=f"sp:{fid}")],
        [IB(sc("🔄 Restart"), callback_data=f"rs:{fid}"), IB(sc("📜 Logs"), callback_data=f"lg:{fid}")],
        [IB(sc("🗑 Delete"), callback_data=f"dl:{fid}"), IB(sc("⬅️ Back"), callback_data="back")],
    ])
    return text, kb


async def callbacks(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    uid = q.from_user.id
    if uid in DB["banned"]:
        await notify_banned(ctx.bot, uid)
        return await q.answer(f"🚫 You have been banned. Contact the owner @{OWNER_USERNAME}", show_alert=True)
    action, _, fid = q.data.partition(":")

    if action == "verify":
        if not FORCE_JOIN_CHAT_ID and uid not in DB["verified"]:
            DB["verified"].append(uid)
            save()
        if await is_member(ctx.bot, uid):
            await q.answer("✅")
            try:
                await q.message.delete()
            except Exception:
                pass
            return await ctx.bot.send_message(
                q.message.chat_id, welcome_text(q.from_user), parse_mode=H,
                reply_markup=main_kb(uid))
        return await q.answer(sc("❌ Join the group first!"), show_alert=True)

    if not await is_member(ctx.bot, uid):
        return await q.answer(sc("🔒 Join the group first!"), show_alert=True)

    # owner review buttons
    if action in ("ap", "rj"):
        if not is_owner(uid):
            return await q.answer("Owner only", show_alert=True)
        rec = DB["files"].get(fid)
        if not rec:
            return await q.answer("File not found", show_alert=True)
        if action == "ap":
            await q.answer("Approved - starting...")
            try:
                await q.edit_message_caption(q.message.caption_html + "\n\n" + sc("✅ Approved"), parse_mode=H)
            except Exception:
                pass
            await approve_file(ctx, fid)
        else:
            stop_proc(fid, mark=False)
            await asyncio.to_thread(shutil.rmtree, proj_dir(rec), True)
            DB["files"].pop(fid, None)
            save()
            await ctx.bot.send_message(rec["uid"], sc("❌ Your file ") + f"<code>{esc(rec['name'])}</code>"
                                       + sc(" was rejected by the owner."), parse_mode=H)
            await q.answer("Rejected")
            await q.edit_message_caption(q.message.caption_html + "\n\n" + sc("❌ Rejected"), parse_mode=H)
        return

    if action == "home":
        await q.answer()
        return await q.edit_message_text(welcome_text(q.from_user), parse_mode=H)

    if action == "back":
        await q.answer()
        return await q.edit_message_text(**files_view(uid))

    rec = DB["files"].get(fid)
    if not rec or (rec["uid"] != uid and not is_owner(uid)):
        return await q.answer("Not found", show_alert=True)

    if action == "f":
        await q.answer()
        t, kb = file_menu(fid)
        return await q.edit_message_text(t, parse_mode=H, reply_markup=kb)

    if rec["status"] == "pending" and action in ("st", "rs"):
        return await q.answer("Waiting for owner approval", show_alert=True)

    if action == "st":
        if is_running(fid):
            await q.answer(sc("Already running"))
        else:
            await q.answer(sc("⏳ Starting..."))
            spawn(launch_and_report(ctx.bot, fid, q.message.chat_id))
    elif action == "sp":
        stop_proc(fid)
        await q.answer("Stopped")
    elif action == "rs":
        stop_proc(fid)
        await q.answer(sc("🔄 Restarting..."))
        spawn(launch_and_report(ctx.bot, fid, q.message.chat_id))
    elif action == "lg":
        lp = (proj_dir(rec) / rec["main"]).parent / "output.log"
        data = lp.read_bytes()[-3000:].decode(errors="ignore") if lp.exists() else ""
        await q.answer()
        return await ctx.bot.send_message(
            q.message.chat_id,
            sc("📜 Logs:\n") + f"<pre>{esc(data or 'no output yet')}</pre>", parse_mode=H)
    elif action == "dl":
        stop_proc(fid, mark=False)
        await asyncio.to_thread(shutil.rmtree, proj_dir(rec), True)
        DB["files"].pop(fid, None)
        save()
        await q.answer("Deleted")
        return await q.edit_message_text(**files_view(rec["uid"]))

    t, kb = file_menu(fid)
    try:
        await q.edit_message_text(t, parse_mode=H, reply_markup=kb)
    except Exception:
        pass


async def speed(update, ctx):
    t0 = time.perf_counter()
    m = await update.message.reply_text(sc("⚡ Testing..."), parse_mode=H)
    ms = (time.perf_counter() - t0) * 1000
    await m.edit_text(sc("⚡ Bot Speed\n\n🏓 Latency: ") + f"<code>{ms:.0f} ms</code>", parse_mode=H)


def fmt_uptime(s):
    s = int(s)
    d, s = divmod(s, 86400)
    h, s = divmod(s, 3600)
    m, s = divmod(s, 60)
    return f"{d}d {h}h {m}m {s}s"


async def stats(update, ctx):
    running = sum(1 for f in DB["files"] if is_running(f))
    extra = ""
    try:
        import psutil
        extra = (sc("\n🖥 CPU: ") + f"<code>{psutil.cpu_percent()}%</code>"
                 + sc("\n💾 RAM: ") + f"<code>{psutil.virtual_memory().percent}%</code>")
    except Exception:
        pass
    mine = len(user_files(update.effective_user.id))
    await update.message.reply_text(
        sc("📊 Statistics\n\n👥 Users: ") + f"<code>{len(DB['users'])}</code>"
        + sc("\n📁 Total Files: ") + f"<code>{len(DB['files'])}</code>"
        + sc("\n🟢 Running: ") + f"<code>{running}</code>"
        + sc("\n📂 Your Files: ") + f"<code>{mine}</code>"
        + sc("\n⏱ Uptime: ") + f"<code>{fmt_uptime(time.time() - START_TIME)}</code>" + extra,
        parse_mode=H)


async def contact(update, ctx):
    await update.message.reply_text(
        sc("📞 Contact the owner:"), parse_mode=H,
        reply_markup=IM([[IB(sc("👤 Owner"), url=f"https://t.me/{OWNER_USERNAME}")]]))


async def updates_ch(update, ctx):
    await update.message.reply_text(
        sc("📢 Join our updates channel:"), parse_mode=H,
        reply_markup=IM([[IB(sc("📢 Updates Channel"), url=UPDATES_CHANNEL)]]))


async def manual(update, ctx):
    ctx.user_data["await_install"] = True
    await update.message.reply_text(
        sc("📦 Manual Install\n\nSend a module name:\n")
        + "<code>requests</code>\n<code>pip aiohttp</code>\n<code>npm axios</code>\n\n"
        + sc("📍 Modules are installed in your own private space, only your files use them.\n")
        + sc("Send /cancel to abort."), parse_mode=H)


async def help_cmd(update, ctx):
    if not await guard(update):
        return
    await update.message.reply_text(
        f"<b>{BRAND}</b>\n\n" + sc("🆘 Help\n\n"
           "1️⃣ Tap Upload File and send a .py / .js / .zip\n"
           "2️⃣ Wait for owner approval\n"
           "3️⃣ Manage it in Check Files (start / stop / restart / logs / delete)\n"
           "4️⃣ Need a library? Use Manual Install\n\n"
           "📌 Zip projects: put main.py / bot.py / index.js in it. "
           "A requirements.txt is installed automatically.\n\n"
           "Commands: /start /files /help /cancel"), parse_mode=H)


async def cancel(update, ctx):
    ctx.user_data.pop("await_install", None)
    ctx.user_data.pop("await", None)
    await update.message.reply_text(sc("❎ Cancelled."), parse_mode=H)


PKG_RE = re.compile(r"^[A-Za-z0-9@][A-Za-z0-9_.@/\-]*(\[[A-Za-z0-9_,\-]+\])?([=<>~!]=?[A-Za-z0-9_.*\-]+)?$")


async def text_router(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    if not await guard(update):
        return
    t = update.message.text.strip()
    table = {L["updates"]: updates_ch, L["upload"]: upload_prompt, L["check"]: check_files,
             L["speed"]: speed, L["stats"]: stats, L["contact"]: contact,
             L["manual"]: manual, L["help"]: help_cmd,
             L["broadcast"]: broadcast_menu, L["admin"]: admin_menu,
             L["ban"]: ban_menu, L["users"]: view_users, L["group"]: group_menu}
    if t in table:
        ctx.user_data.pop("await_install", None)
        return await table[t](update, ctx)

    if ctx.user_data.get("await_install"):
        ctx.user_data.pop("await_install")
        parts = t.split()
        mgr = "pip"
        if parts[0].lower() in ("pip", "npm") and len(parts) > 1:
            mgr, parts = parts[0].lower(), parts[1:]
        pkgs = parts[:5]
        if not pkgs or not all(PKG_RE.match(p) for p in pkgs):
            return await update.message.reply_text(sc("❌ Invalid module name."), parse_mode=H)
        uid = update.effective_user.id
        udir = USERS_DIR / str(uid)
        udir.mkdir(exist_ok=True)
        msg = await update.message.reply_text(install_card("Module", 5, " ".join(pkgs)), parse_mode=H)
        await install_with_ui(ctx.bot, msg.chat_id, uid, "py" if mgr == "pip" else "npm", pkgs, "Module", msg=msg)


# ───────────────────── owner commands ──────────────────────
_FLAGS = {"gc_err": False}


async def checkgc(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Owner only: tests the force-join setup and shows what is wrong."""
    if not is_owner(update.effective_user.id):
        return
    msg = update.effective_message
    if not FORCE_JOIN_CHAT_ID:
        return await msg.reply_text("FORCE_JOIN_CHAT_ID is 0 (lock not enforced).")
    lines = [f"Configured ID: {FORCE_JOIN_CHAT_ID}"]
    try:
        chat = await ctx.bot.get_chat(FORCE_JOIN_CHAT_ID)
        lines.append(f"✅ Group found: {chat.title}")
    except Exception as e:
        lines.append(f"❌ Group not found / bot not in it: {e}")
        lines.append("→ Check the ID and add the bot to that group.")
        return await msg.reply_text("\n".join(lines))
    try:
        me = await ctx.bot.get_chat_member(FORCE_JOIN_CHAT_ID, ctx.bot.id)
        lines.append(f"Bot status: {me.status}")
        if me.status != "administrator":
            lines.append("→ Make the bot an ADMIN in the group.")
    except Exception as e:
        lines.append(f"❌ Could not read bot status: {e}")
    try:
        um = await ctx.bot.get_chat_member(FORCE_JOIN_CHAT_ID, update.effective_user.id)
        lines.append(f"Your status in the group: {um.status}")
    except Exception as e:
        lines.append(f"❌ Could not check you: {e}")
    _FLAGS["gc_err"] = False
    await msg.reply_text("\n".join(lines))


async def hostme(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Works in groups for everyone (no join lock). Remembers the group for broadcasts."""
    chat = update.effective_chat
    if chat and chat.type in ("group", "supergroup") and DB["groups"].get(str(chat.id)) != (chat.title or ""):
        DB["groups"][str(chat.id)] = chat.title or ""
        save()
    if not await guard(update):
        return
    await update.effective_message.reply_text(
        sc("Hi I am ") + BRAND
        + sc(", use me to host and run your .py, .js scripts for your telegram bots and web services"),
        parse_mode=H)


async def attempts(update, ctx):
    """Owner: people who used the bot in a group without joining the GC (still not banned)."""
    if not is_owner(update.effective_user.id):
        return
    rows = [(int(u), a) for u, a in DB.get("attempts", {}).items() if int(u) not in DB["banned"]]
    rows.sort(key=lambda x: x[1].get("last", 0), reverse=True)
    lines = []
    for i, (uid, a) in enumerate(rows[:30], 1):
        lines.append(f"{i}. {person(uid)} — <code>{uid}</code> — {a['n']}× " + esc(a.get("chat", "")))
    body = sc(f"🚨 Used the bot without joining: {len(rows)}") + "\n" + (
        "\n".join(lines) if lines else sc("Nobody yet."))
    await update.message.reply_text(
        quote(body) + "\n" + sc("Ban with the Ban User button (@username or ID)."), parse_mode=H)


async def broadcast(update, ctx):
    if not is_owner(update.effective_user.id):
        return
    text = " ".join(ctx.args)
    if not text:
        return await update.message.reply_text("Usage: /broadcast <message>")
    ok = 0
    for uid in list(DB["users"]):
        try:
            await ctx.bot.send_message(int(uid), sc(text), parse_mode=H)
            ok += 1
        except Exception:
            pass
        await asyncio.sleep(0.05)
    await update.message.reply_text(sc(f"📣 Sent to {ok} users."), parse_mode=H)


async def ban(update, ctx):
    if not is_owner(update.effective_user.id) or not ctx.args:
        return
    uid = resolve_target(ctx.args[0])
    if uid is None:
        return await update.message.reply_text(sc("❌ User not found. Use a Chat ID or a known @username."), parse_mode=H)
    if uid not in DB["banned"]:
        DB["banned"].append(uid)
    for fid, r in user_files(uid):
        stop_proc(fid)
    save()
    await notify_banned(ctx.bot, uid, force=True)
    await update.message.reply_text(sc(f"🚫 Banned {uid} and stopped their files."), parse_mode=H)


async def unban(update, ctx):
    if not is_owner(update.effective_user.id) or not ctx.args:
        return
    uid = resolve_target(ctx.args[0])
    if uid is None:
        return await update.message.reply_text(sc("❌ User not found. Use a Chat ID or a known @username."), parse_mode=H)
    if uid in DB["banned"]:
        DB["banned"].remove(uid)
        save()
    await update.message.reply_text(sc(f"✅ Unbanned {uid}."), parse_mode=H)


# ───────────────────── admin / owner panel ─────────────────────
def is_admin(uid) -> bool:
    return is_owner(uid) or uid in DB["admins"]


def all_groups():
    ids = {int(g) for g in DB["groups"]}
    if FORCE_JOIN_CHAT_ID:
        ids.add(FORCE_JOIN_CHAT_ID)
    return sorted(ids)


def quote(text):
    return f"<blockquote>{text}</blockquote>"


def uname(uid):
    r = DB["users"].get(str(uid), {})
    return ("@" + esc(r["username"])) if r.get("username") else "NULL"


def person(uid):
    """'Name @username' (either part may be missing)."""
    r = DB["users"].get(str(uid), {})
    name = esc(sc(r["name"])) if r.get("name") else sc("Unknown")
    user = ("@" + esc(r["username"])) if r.get("username") else "NULL"
    return f"{name} {user}"


async def refresh_profile(bot, uid):
    """Ask Telegram for the user's name/username and cache it.
    Works only if that user has started the bot (Telegram limitation)."""
    try:
        c = await bot.get_chat(uid)
    except Exception:
        return False
    rec = DB["users"].setdefault(str(uid), {"joined": int(time.time())})
    rec["name"] = c.full_name or c.first_name or rec.get("name")
    extra = getattr(c, "active_usernames", None) or []
    rec["username"] = c.username or (extra[0] if extra else None)
    save()
    return True


async def broadcast_menu(update, ctx):
    if not is_owner(update.effective_user.id):
        return
    ctx.user_data.pop("await", None)
    kb = IM([
        [IB(sc("👥 All Users"), callback_data="bc:all")],
        [IB(sc("🖥 Hosters Only"), callback_data="bc:host")],
        [IB(sc("❌ Cancel"), callback_data="bc:cancel")],
    ])
    await update.message.reply_text(quote(sc("📣 Broadcast Menu\nSelect type:")), parse_mode=H, reply_markup=kb)


async def admin_menu(update, ctx):
    if not is_owner(update.effective_user.id):
        return
    ctx.user_data.pop("await", None)
    kb = IM([
        [IB(sc("➕ Add Admin"), callback_data="adm:add")],
        [IB(sc("➖ Remove Admin"), callback_data="adm:rem")],
        [IB(sc("📋 Admin List"), callback_data="adm:list")],
    ])
    await update.message.reply_text(quote(sc("👮 Admin Panel\nManage admins by Chat ID:")), parse_mode=H, reply_markup=kb)


async def ban_menu(update, ctx):
    if not is_admin(update.effective_user.id):
        return
    ctx.user_data.pop("await", None)
    kb = IM([
        [IB(sc("🚫 Ban User"), callback_data="bn:ban")],
        [IB(sc("✅ Unban User"), callback_data="bn:unban")],
        [IB(sc("📋 Banned List"), callback_data="bn:list")],
    ])
    await update.message.reply_text(quote(sc("🚫 Ban Panel\nManage users by Chat ID:")), parse_mode=H, reply_markup=kb)


async def group_menu(update, ctx):
    if not is_admin(update.effective_user.id):
        return
    ctx.user_data.pop("await", None)
    kb = IM([
        [IB(sc("➕ Add Bot To Group"), url=f"https://t.me/{ctx.bot.username}?startgroup=true")],
        [IB(sc("🔗 Send Group Link"), callback_data="grp:link")],
        [IB(sc("📋 Group List"), callback_data="grp:list")],
    ])
    await update.message.reply_text(
        quote(sc("🔗 Group Panel\nAdd the bot to a group:") + f"\n⚡ @{esc(OWNER_USERNAME)}"),
        parse_mode=H, reply_markup=kb)


GC_RE = re.compile(r"(?:https?://)?(?:t|telegram)\.me/(\+[\w-]+|joinchat/[\w-]+|[A-Za-z]\w{3,})", re.I)


async def handle_group_link(ctx, txt):
    """Returns (html_text, keyboard). Bots can't join via a link, so we resolve the group,
    register it if the bot is already inside, otherwise hand over the 'add to group' button."""
    foot = f"\n⚡ @{esc(OWNER_USERNAME)}"
    add_kb = IM([[IB(sc("➕ Add Bot To Group"), url=f"https://t.me/{ctx.bot.username}?startgroup=true")]])
    target = None
    m = GC_RE.search(txt)
    if m:
        slug = m.group(1)
        if slug.startswith("+") or slug.lower().startswith("joinchat/"):
            return quote(sc("🔒 Private invite link.\nTelegram doesn't let bots join by link.\n"
                            "Tap the button, pick the group, and the bot is added.") + foot), add_kb
        target = "@" + slug
    elif re.fullmatch(r"@[A-Za-z]\w{3,}", txt):
        target = txt
    elif re.fullmatch(r"-\d{6,}", txt):
        target = int(txt)
    if target is None:
        return sc("❌ Send a group link (t.me/name), @username or chat ID, or /cancel."), None
    try:
        chat = await ctx.bot.get_chat(target)
    except Exception:
        return quote(sc("❌ Group not found.\nIf it's private, use the button below.") + foot), add_kb
    if chat.type not in ("group", "supergroup"):
        return sc("❌ That link is not a group."), None
    title = esc(chat.title or "")
    try:
        me = await ctx.bot.get_chat_member(chat.id, ctx.bot.id)
        inside = me.status in ("member", "administrator", "creator")
    except Exception:
        inside = False
    if inside:
        DB["groups"][str(chat.id)] = chat.title or ""
        save()
        return quote(sc("✅ Bot is already in this group.\nSaved for broadcasts.\n")
                     + f"{title} — <code>{chat.id}</code>" + foot), None
    return quote(sc("➕ Bot is not in this group yet.\nTap the button and pick it:\n")
                 + f"{title} — <code>{chat.id}</code>" + foot), add_kb


PER_PAGE = 15


def users_view(page):
    banned = {int(b) for b in DB["banned"]}
    items = sorted(((u, r) for u, r in DB["users"].items() if int(u) not in banned),
                   key=lambda kv: kv[1].get("joined", 0))
    total = len(items)
    pages = max(1, (total + PER_PAGE - 1) // PER_PAGE)
    page = min(max(page, 0), pages - 1)
    lines = []
    for i, (uid, _r) in enumerate(items[page * PER_PAGE:(page + 1) * PER_PAGE], page * PER_PAGE + 1):
        lines.append(f"{i}. {person(uid)} — <code>{uid}</code>")
    body = (sc(f"👥 Users: {total}") + "\n" + sc(f"Page {page + 1}/{pages}") + "\n"
            + ("\n".join(lines) if lines else sc("No users yet.")))
    text = quote(body)
    nav = []
    if page > 0:
        nav.append(IB("◀️", callback_data=f"vu:{page - 1}"))
    if page < pages - 1:
        nav.append(IB("▶️", callback_data=f"vu:{page + 1}"))
    return text, (IM([nav]) if nav else None)


async def view_users(update, ctx):
    if not is_admin(update.effective_user.id):
        return
    text, kb = users_view(0)
    await update.message.reply_text(text, parse_mode=H, reply_markup=kb)


PROMPTS = {
    ("bc", "all"): ("bc_all", "Send message to ALL users:"),
    ("bc", "host"): ("bc_host", "Send message to HOSTERS (users who uploaded files):"),
    ("grp", "link"): ("grp_link", "Send the group link (t.me/name), @username or chat ID:"),
    ("adm", "add"): ("adm_add", "Send the Chat ID of the user to make ADMIN:"),
    ("adm", "rem"): ("adm_rem", "Send the Chat ID of the admin to REMOVE:"),
    ("bn", "ban"): ("bn_ban", "Send the @username or Chat ID of the user to BAN:"),
    ("bn", "unban"): ("bn_unban", "Send the @username or Chat ID of the user to UNBAN:"),
}


async def panel_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    uid = q.from_user.id
    kind, _, arg = q.data.partition(":")
    if kind in ("bc", "adm") and not is_owner(uid):
        return await q.answer("Owner only", show_alert=True)
    if not is_admin(uid):
        return await q.answer("Admins only", show_alert=True)
    await q.answer()
    if kind == "vu":
        text, kb = users_view(int(arg))
        try:
            await q.edit_message_text(text, parse_mode=H, reply_markup=kb)
        except Exception:
            pass
        return
    if arg == "cancel":
        ctx.user_data.pop("await", None)
        return await q.edit_message_text(sc("❎ Cancelled."), parse_mode=H)
    if kind == "grp" and arg == "list":
        gl = [f"{i}. {esc(t) or '—'} — <code>{g}</code>" for i, (g, t) in enumerate(DB["groups"].items(), 1)]
        body = sc(f"🔗 Groups: {len(gl)}") + "\n" + ("\n".join(gl) if gl else sc("None."))
        return await q.edit_message_text(quote(body + f"\n⚡ @{esc(OWNER_USERNAME)}"), parse_mode=H)
    if arg == "list":
        ids = DB["admins"] if kind == "adm" else DB["banned"]
        title = "👮 Admins" if kind == "adm" else "🚫 Banned users"
        for x in ids[:20]:
            r = DB["users"].get(str(x), {})
            if not r.get("name") or not r.get("username"):
                await refresh_profile(ctx.bot, x)
        lines = [f"{i}. {person(x)} — <code>{x}</code>" for i, x in enumerate(ids, 1)]
        body = sc(f"{title}: {len(ids)}") + "\n" + ("\n".join(lines) if lines else sc("None."))
        foot = "" if kind == "adm" else f"\n⚡ @{esc(OWNER_USERNAME)}"
        return await q.edit_message_text(quote(body + foot), parse_mode=H)
    item = PROMPTS.get((kind, arg))
    if not item:
        return
    ctx.user_data["await"] = item[0]
    await q.edit_message_text(quote(sc(item[1])) + "\n" + sc("Send /cancel to abort."), parse_mode=H)


async def do_broadcast(ctx, msg, kind):
    users = [int(u) for u in DB["users"] if int(u) not in DB["banned"]]
    if kind == "host":
        hosters = {r["uid"] for r in DB["files"].values()}
        users = [u for u in users if u in hosters]
        groups = []
    else:
        groups = all_groups()
    status = await msg.reply_text(sc("📣 Broadcasting..."), parse_mode=H)
    sent = failed = 0
    for cid in users + groups:
        for _attempt in range(2):
            try:
                await ctx.bot.copy_message(cid, msg.chat_id, msg.message_id)
                sent += 1
                break
            except RetryAfter as e:
                await asyncio.sleep(e.retry_after + 1)
            except Exception:
                failed += 1
                break
        else:
            failed += 1
        await asyncio.sleep(0.05)
    result = quote(
        sc("✅ Broadcast Done!\n👥 Users: ") + str(len(users)) + sc(" | 📢 Groups: ") + str(len(groups))
        + sc("\n✅ Sent: ") + str(sent) + sc(" | ❌ Failed: ") + str(failed)
        + f"\n⚡ @{esc(OWNER_USERNAME)}")
    await status.edit_text(result, parse_mode=H)


async def apply_action(ctx, by, state, target):
    t = f"<code>{target}</code>"
    if state == "adm_add":
        if target == OWNER_ID or target in DB["admins"]:
            return t + sc(" is already an owner/admin.")
        DB["admins"].append(target)
        save()
        await refresh_profile(ctx.bot, target)
        t = f"{person(target)} — <code>{target}</code>"
        try:
            await ctx.bot.send_message(
                target, sc("👮 You are now an admin of ") + BRAND + sc(".\nYour new buttons are ready."),
                parse_mode=H, reply_markup=main_kb(target))
        except Exception:
            pass
        return quote(sc("✅ Admin added\n") + t + f"\n⚡ @{esc(OWNER_USERNAME)}")
    if state == "adm_rem":
        if target not in DB["admins"]:
            return t + sc(" is not an admin.")
        DB["admins"].remove(target)
        save()
        try:
            await ctx.bot.send_message(target, sc("You are no longer an admin."), parse_mode=H,
                                       reply_markup=main_kb(target))
        except Exception:
            pass
        return sc("✅ Admin removed: ") + t
    if state == "bn_ban":
        if target == OWNER_ID or target == by:
            return sc("❌ You can't ban the owner or yourself.")
        if target in DB["admins"]:
            if by != OWNER_ID:
                return sc("❌ Only the owner can ban an admin.")
            DB["admins"].remove(target)
        if target not in DB["banned"]:
            DB["banned"].append(target)
        for fid, _r in user_files(target):
            stop_proc(fid)
        save()
        await notify_banned(ctx.bot, target, force=True)
        return sc("🚫 Banned: ") + f"{person(target)} — {t}" + sc(" (their files were stopped)")
    if state == "bn_unban":
        if target not in DB["banned"]:
            return t + sc(" is not banned.")
        DB["banned"].remove(target)
        save()
        return sc("✅ Unbanned: ") + f"{person(target)} — {t}"
    return sc("❌ Unknown action.")


async def panel_input(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Runs before the normal handlers; only acts when a panel prompt is waiting for input."""
    state = ctx.user_data.get("await")
    if not state:
        return
    uid = update.effective_user.id
    msg = update.effective_message
    if not is_admin(uid) or (state.startswith(("bc_", "adm_")) and not is_owner(uid)):
        ctx.user_data.pop("await", None)
        return
    if msg.text and msg.text.strip() in L.values():
        ctx.user_data.pop("await", None)  # a menu button was pressed: stop waiting
        return
    if state.startswith("bc_"):
        ctx.user_data.pop("await", None)
        await do_broadcast(ctx, msg, state[3:])
        raise ApplicationHandlerStop
    txt = (msg.text or "").strip()
    if state == "grp_link":
        ctx.user_data.pop("await", None)
        text, kb = await handle_group_link(ctx, txt)
        await msg.reply_text(text, parse_mode=H, reply_markup=kb)
        raise ApplicationHandlerStop
    if state.startswith("bn_"):
        target = resolve_target(txt)
        bad = sc("❌ User not found. Send a Chat ID or the @username of someone who has used this bot, or /cancel.")
    else:
        target = int(txt) if re.fullmatch(r"-?\d{5,15}", txt) else None
        bad = sc("❌ Send a numeric Chat ID, or /cancel.")
    if target is None:
        await msg.reply_text(bad, parse_mode=H)
        raise ApplicationHandlerStop
    ctx.user_data.pop("await", None)
    await msg.reply_text(await apply_action(ctx, uid, state, target), parse_mode=H)
    raise ApplicationHandlerStop


async def track_chat(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Remember the groups the bot is in, so broadcasts can reach them."""
    cm = update.my_chat_member
    chat = cm.chat
    if chat.type not in ("group", "supergroup"):
        return
    if cm.new_chat_member.status in ("member", "administrator"):
        DB["groups"][str(chat.id)] = chat.title or ""
    else:
        DB["groups"].pop(str(chat.id), None)
    save()


# ───────────────────────── lifecycle ───────────────────────
async def restore_running():
    """Bring back running files after a restart, a few per second instead of all at once."""
    pending = [f for f, r in DB["files"].items() if r["status"] == "running"]
    LAUNCHING.update(pending)  # so the monitor doesn't call them dead while they wait their turn
    for fid in pending:
        try:
            r = DB["files"].get(fid)
            if r and r["status"] == "running" and not is_running(fid):
                ok, msg = start_proc(fid)
                if not ok:
                    r["status"] = "stopped"
                    save()
                    log.warning("restore %s failed: %s", fid, msg)
        except Exception:
            log.exception("restore failed")
        finally:
            LAUNCHING.discard(fid)
        await asyncio.sleep(0.25)


async def post_init(app):
    try:
        await setup_web()
    except Exception:
        log.exception("web setup failed")
    spawn(restore_running())
    spawn(monitor(app))
    spawn(db_flusher())
    log.info("bot ready")


async def post_shutdown(app):
    procs = list(PROCS.values())
    for fid in list(PROCS):
        stop_proc(fid, mark=False)  # status stays "running" so they auto-restore
    await asyncio.sleep(1)
    for p in procs:
        _force_kill(p)
    save_now()  # flush any pending DB changes


def main():
    if BOT_TOKEN.startswith("PASTE"):
        sys.exit("Set BOT_TOKEN first.")
    app = (Application.builder().token(BOT_TOKEN).concurrent_updates(256)
           .connection_pool_size(128).pool_timeout(30)
           .get_updates_connection_pool_size(8)
           .post_init(post_init).post_shutdown(post_shutdown).build())
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("files", check_files))
    app.add_handler(CommandHandler("help", help_cmd))
    app.add_handler(CommandHandler("cancel", cancel))
    app.add_handler(CommandHandler("hostme", hostme))
    app.add_handler(CommandHandler("checkgc", checkgc))
    app.add_handler(CommandHandler("broadcast", broadcast))
    app.add_handler(CommandHandler("attempts", attempts))
    app.add_handler(CommandHandler("ban", ban))
    app.add_handler(CommandHandler("unban", unban))
    app.add_handler(MessageHandler(filters.ChatType.PRIVATE & ~filters.COMMAND, panel_input), group=-1)
    app.add_handler(ChatMemberHandler(track_chat, ChatMemberHandler.MY_CHAT_MEMBER))
    app.add_handler(CallbackQueryHandler(panel_cb, pattern=r"^(bc|adm|bn|vu|grp):"))
    app.add_handler(CallbackQueryHandler(callbacks))
    app.add_handler(MessageHandler(filters.Document.ALL, doc_handler))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, text_router))
    # after downtime Telegram replays everything that piled up; skipping it avoids a start-up flood
    app.run_polling(allowed_updates=Update.ALL_TYPES,
                    drop_pending_updates=os.getenv("DROP_PENDING", "1") != "0")


if __name__ == "__main__":
    main()

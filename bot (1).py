#!/usr/bin/env python3
"""
BHAI3131 · Oniocokh Live OTP Telegram Bot (@Oniocokh_bot)
Standalone 24/7 Python Edition (Pure requests + Python stdlib only — zero C build deps).
Compatible with Python 3.8+ on GSM Bot Hosting, Render, Railway, Koyeb, PythonAnywhere, VPS.
"""

import concurrent.futures
import hashlib
import html
import json
import os
import queue
import random
import re
import secrets
import signal
import struct
import sys
import threading
import time
import urllib.parse
import zlib
from datetime import datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

import requests

# ==============================================================================
# CONFIGURATION
# Paste your @BotFather token below before uploading bot.py to GSM Bot Hosting,
# OR set TELEGRAM_BOT_TOKEN in your hosting environment variables.
# ==============================================================================
BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip() or "9147000064:AAHQ1khwzQGyUmJVbqgSrq6KFv8RjZX1d4Y"

ADMIN_TELEGRAM_USERNAME = "king3131bhai"
ADMIN_TELEGRAM_PHONE = "27787045561"
ADMIN_PASSWORD = os.environ.get("ADMIN_PASSWORD", "king3131").strip() or "king3131"

REQUIRED_CHANNEL_USERNAME = "@bhai3131"
REQUIRED_CHANNEL_URL = "https://t.me/bhai3131"

UPI_VPA = "9653024425-2@axl"
UPI_PAYEE_NAME = "RAJA"
QR_PAYMENT_WINDOW_SEC = 5 * 60

DEFAULT_RTDB_URLS = [
    "https://king-bihari-default-rtdb.firebaseio.com",
    "https://kaliya-413d2-default-rtdb.firebaseio.com",
    "https://sourav-4c188-default-rtdb.firebaseio.com",
    "https://new-panel1-default-rtdb.firebaseio.com",
]

STATE_FILE = os.path.join(os.getcwd(), ".bot-state.json")
BACKUP_STATE_FILE = os.path.join(os.getcwd(), ".bot-state.backup.json")

PINNED_PROTECTED_GRANTS = [
    {
        "chatId": "8732570555",
        "daysGranted": 7,
        "planName": "💎 WEEKLY PREMIUM 💎",
        "issuedAtMs": 1795084600000,
        "expiresAtMs": 1795084600000 + 7 * 86400000,
    },
    {
        "chatId": "8066758094",
        "daysGranted": 3650,
        "planName": "♾️ LIFETIME MEMBER",
        "issuedAtMs": 1795084600000,
        "expiresAtMs": 1795084600000 + 3650 * 86400000,
    },
]

# ==============================================================================
# PURE-PYTHON QR CODE PNG GENERATOR (ISO/IEC 18004 Byte Mode, EC Level M, V1-V10)
# ==============================================================================
_GF_EXP = [0] * 512
_GF_LOG = [0] * 256
_x = 1
for _i in range(255):
    _GF_EXP[_i] = _x
    _GF_LOG[_x] = _i
    _x <<= 1
    if _x & 0x100:
        _x ^= 0x11D
for _i in range(255, 512):
    _GF_EXP[_i] = _GF_EXP[_i - 255]


def _gf_mul(a, b):
    if a == 0 or b == 0:
        return 0
    return _GF_EXP[_GF_LOG[a] + _GF_LOG[b]]


def _rs_gen_poly(deg):
    poly = [1]
    for i in range(deg):
        nxt = [0] * (len(poly) + 1)
        root = _GF_EXP[i]
        for j, coef in enumerate(poly):
            nxt[j] ^= coef
            nxt[j + 1] ^= _gf_mul(coef, root)
        poly = nxt
    return poly


def _rs_remainder(data, ec_len):
    gen = _rs_gen_poly(ec_len)
    res = list(data) + [0] * ec_len
    for i in range(len(data)):
        factor = res[i]
        if factor != 0:
            for j in range(len(gen)):
                res[i + j] ^= _gf_mul(gen[j], factor)
    return res[len(data):]


# (version, total_codewords, ec_per_block, g1_blocks, g1_data, g2_blocks, g2_data, align_coords)
_QR_SPECS_M = [
    (1, 26, 10, 1, 16, 0, 0, []),
    (2, 44, 16, 1, 28, 0, 0, [6, 18]),
    (3, 70, 26, 1, 44, 0, 0, [6, 22]),
    (4, 100, 18, 2, 32, 0, 0, [6, 26]),
    (5, 134, 24, 2, 43, 0, 0, [6, 30]),
    (6, 172, 16, 4, 27, 0, 0, [6, 34]),
    (7, 196, 18, 4, 31, 0, 0, [6, 22, 38]),
    (8, 242, 22, 2, 38, 2, 39, [6, 24, 42]),
    (9, 292, 22, 3, 36, 2, 37, [6, 26, 46]),
    (10, 346, 26, 4, 43, 1, 44, [6, 28, 50]),
]


def _encode_qr_matrix(text):
    raw = text.encode("utf-8")
    spec = None
    for s in _QR_SPECS_M:
        ver, _tot, _ec, g1b, g1d, g2b, g2d, _al = s
        total_data_cw = g1b * g1d + g2b * g2d
        char_count_bits = 8 if ver <= 9 else 16
        cap_bytes = (total_data_cw * 8 - 4 - char_count_bits) // 8
        if len(raw) <= cap_bytes:
            spec = s
            break
    if spec is None:
        raise ValueError("Payload too long for QR V10-M")

    ver, _tot, ec_len, g1b, g1d, g2b, g2d, align_coords = spec
    total_data_cw = g1b * g1d + g2b * g2d
    char_count_bits = 8 if ver <= 9 else 16

    bits = []

    def push_bits(val, count):
        for k in range(count - 1, -1, -1):
            bits.append((val >> k) & 1)

    push_bits(0b0100, 4)  # Byte mode
    push_bits(len(raw), char_count_bits)
    for b in raw:
        push_bits(b, 8)
    rem_bits = total_data_cw * 8 - len(bits)
    push_bits(0, min(4, rem_bits))
    while len(bits) % 8 != 0:
        bits.append(0)
    data_cw = []
    for i in range(0, len(bits), 8):
        val = 0
        for b in bits[i:i + 8]:
            val = (val << 1) | b
        data_cw.append(val)
    pad_bytes = [0xEC, 0x11]
    idx = 0
    while len(data_cw) < total_data_cw:
        data_cw.append(pad_bytes[idx % 2])
        idx += 1

    blocks_data = []
    blocks_ec = []
    pos = 0
    for _ in range(g1b):
        blk = data_cw[pos:pos + g1d]
        pos += g1d
        blocks_data.append(blk)
        blocks_ec.append(_rs_remainder(blk, ec_len))
    for _ in range(g2b):
        blk = data_cw[pos:pos + g2d]
        pos += g2d
        blocks_data.append(blk)
        blocks_ec.append(_rs_remainder(blk, ec_len))

    final_cw = []
    max_d = max(g1d, g2d)
    for i in range(max_d):
        for blk in blocks_data:
            if i < len(blk):
                final_cw.append(blk[i])
    for i in range(ec_len):
        for blk in blocks_ec:
            final_cw.append(blk[i])

    all_bits = []
    for cw in final_cw:
        for k in range(7, -1, -1):
            all_bits.append((cw >> k) & 1)

    size = ver * 4 + 17
    modules = [[0] * size for _ in range(size)]
    is_func = [[False] * size for _ in range(size)]

    def set_func(r, c, dark):
        if 0 <= r < size and 0 <= c < size:
            modules[r][c] = 1 if dark else 0
            is_func[r][c] = True

    def draw_finder(r0, c0):
        for dr in range(-1, 8):
            for dc in range(-1, 8):
                r, c = r0 + dr, c0 + dc
                if not (0 <= r < size and 0 <= c < size):
                    continue
                if 0 <= dr <= 6 and 0 <= dc <= 6:
                    dark = (
                        dr in (0, 6)
                        or dc in (0, 6)
                        or (2 <= dr <= 4 and 2 <= dc <= 4)
                    )
                else:
                    dark = False
                set_func(r, c, dark)

    draw_finder(0, 0)
    draw_finder(0, size - 7)
    draw_finder(size - 7, 0)

    if align_coords:
        for ar in align_coords:
            for ac in align_coords:
                if (ar == 6 and ac == 6) or (ar == 6 and ac == size - 7) or (ar == size - 7 and ac == 6):
                    continue
                for dr in range(-2, 3):
                    for dc in range(-2, 3):
                        dark = max(abs(dr), abs(dc)) != 1
                        set_func(ar + dr, ac + dc, dark)

    for i in range(8, size - 8):
        dark = (i % 2 == 0)
        if not is_func[6][i]:
            set_func(6, i, dark)
        if not is_func[i][6]:
            set_func(i, 6, dark)

    # Dark module & reserve format info + version info (>=7)
    set_func(size - 8, 8, True)
    for i in range(9):
        if i != 6:
            is_func[8][i] = True
            is_func[i][8] = True
    for i in range(8):
        is_func[8][size - 1 - i] = True
    for i in range(7):
        is_func[size - 1 - i][8] = True

    if ver >= 7:
        v_bits = ver << 12
        rem = v_bits
        for _ in range(6):
            if rem & (1 << 17):
                pass
        # Compute 18-bit BCH(18,6) version info
        rem = ver << 12
        for shift in range(5, -1, -1):
            if rem & (1 << (shift + 12)):
                rem ^= 0x1F25 << shift
        v_info = (ver << 12) | rem
        for i in range(18):
            dark = bool((v_info >> i) & 1)
            r = i // 3
            c = size - 11 + (i % 3)
            set_func(r, c, dark)
            set_func(c, r, dark)

    # Place data bits
    bit_idx = 0
    up = True
    col = size - 1
    while col > 0:
        if col == 6:
            col -= 1
        row_range = range(size - 1, -1, -1) if up else range(size)
        for row in row_range:
            for dc in (0, -1):
                cc = col + dc
                if not is_func[row][cc]:
                    val = all_bits[bit_idx] if bit_idx < len(all_bits) else 0
                    modules[row][cc] = val
                    bit_idx += 1
        up = not up
        col -= 2

    def mask_cond(m_id, r, c):
        if m_id == 0:
            return (r + c) % 2 == 0
        if m_id == 1:
            return r % 2 == 0
        if m_id == 2:
            return c % 3 == 0
        if m_id == 3:
            return (r + c) % 3 == 0
        if m_id == 4:
            return (r // 2 + c // 3) % 2 == 0
        if m_id == 5:
            return ((r * c) % 2 + (r * c) % 3) == 0
        if m_id == 6:
            return (((r * c) % 2 + (r * c) % 3) % 2) == 0
        return (((r + c) % 2 + (r * c) % 3) % 2) == 0

    def apply_format(grid, m_id):
        # EC Level M = 00; ISO/IEC 18004 format bits placed MSB (bit 14) -> LSB (bit 0)
        fmt_data = (0b00 << 3) | m_id
        rem = fmt_data << 10
        for shift in range(4, -1, -1):
            if rem & (1 << (shift + 10)):
                rem ^= 0x537 << shift
        fmt = ((fmt_data << 10) | rem) ^ 0x5412
        for i in range(6):
            dark = (fmt >> (14 - i)) & 1
            grid[8][i] = dark
            grid[size - 1 - i][8] = dark
        grid[8][7] = (fmt >> 8) & 1
        grid[size - 7][8] = (fmt >> 8) & 1
        grid[8][8] = (fmt >> 7) & 1
        grid[8][size - 8] = (fmt >> 7) & 1
        grid[7][8] = (fmt >> 6) & 1
        grid[8][size - 7] = (fmt >> 6) & 1
        for i in range(9, 15):
            dark = (fmt >> (14 - i)) & 1
            grid[14 - i][8] = dark
            grid[8][size - 15 + i] = dark

    def penalty_score(grid):
        score = 0
        for r in range(size):
            run = 1
            for c in range(1, size):
                if grid[r][c] == grid[r][c - 1]:
                    run += 1
                    if run == 5:
                        score += 3
                    elif run > 5:
                        score += 1
                else:
                    run = 1
        for c in range(size):
            run = 1
            for r in range(1, size):
                if grid[r][c] == grid[r - 1][c]:
                    run += 1
                    if run == 5:
                        score += 3
                    elif run > 5:
                        score += 1
                else:
                    run = 1
        for r in range(size - 1):
            for c in range(size - 1):
                v = grid[r][c]
                if v == grid[r][c + 1] == grid[r + 1][c] == grid[r + 1][c + 1]:
                    score += 3
        dark_count = sum(sum(row) for row in grid)
        pct = (dark_count * 100) // (size * size)
        score += min(abs(pct - 50) // 5, 10) * 10
        return score

    best_grid = None
    best_score = 10**9
    for m_id in range(8):
        cand = [row[:] for row in modules]
        for r in range(size):
            for c in range(size):
                if not is_func[r][c] and mask_cond(m_id, r, c):
                    cand[r][c] ^= 1
        apply_format(cand, m_id)
        sc = penalty_score(cand)
        if sc < best_score:
            best_score = sc
            best_grid = cand
    return best_grid


def render_qr_png_bytes(text, target_width=512, border_modules=4):
    matrix = _encode_qr_matrix(text)
    mod_count = len(matrix)
    total_mods = mod_count + border_modules * 2
    scale = max(4, target_width // total_mods)
    img_size = total_mods * scale

    rows_raw = bytearray()
    white_row = bytes([255, 255, 255]) * img_size
    black_px = bytes([0, 0, 0]) * scale
    white_px = bytes([255, 255, 255]) * scale
    for mr in range(total_mods):
        r_idx = mr - border_modules
        if 0 <= r_idx < mod_count:
            line = bytearray()
            m_row = matrix[r_idx]
            for mc in range(total_mods):
                c_idx = mc - border_modules
                if 0 <= c_idx < mod_count and m_row[c_idx]:
                    line.extend(black_px)
                else:
                    line.extend(white_px)
            for _ in range(scale):
                rows_raw.append(0)
                rows_raw.extend(line)
        else:
            for _ in range(scale):
                rows_raw.append(0)
                rows_raw.extend(white_row)

    def png_chunk(chunk_type, data):
        length = struct.pack("!I", len(data))
        crc = zlib.crc32(chunk_type + data) & 0xFFFFFFFF
        return length + chunk_type + data + struct.pack("!I", crc)

    ihdr = struct.pack("!IIBBBBB", img_size, img_size, 8, 2, 0, 0, 0)  # 8-bit RGB
    idat = zlib.compress(bytes(rows_raw), 6)
    return (
        b"\x89PNG\r\n\x1a\n"
        + png_chunk(b"IHDR", ihdr)
        + png_chunk(b"IDAT", idat)
        + png_chunk(b"IEND", b"")
    )


# ==============================================================================
# RUNTIME STATE & THREAD LOCK
# ==============================================================================
state_lock = threading.RLock()
http_session = requests.Session()

bot_running = False
verified_username = None
verified_bot_name = None
last_bot_error = None
update_offset = 0
updates_processed = 0
messages_sent = 0

rtdb_urls = []
rtdb_user_modified = False
rtdb_auth_secret = ""
rtdb_last_sync_at = None
rtdb_last_error = None
rtdb_items_count = 0
rtdb_per_link_counts = []
rtdb_initial_bootstrapped = False
seen_rtdb_keys = set()
last_rtdb_sync_ms = 0

admin_chat_id = ""
default_telegram_chat_id = ""
synced_devices = []
synced_messages_by_device = {}
synced_access_grants = []
deleted_grant_chat_ids = set()
synced_payment_requests = []
used_payment_refs = set()
used_screenshot_hashes = set()
used_bank_sms_ids = set()
recent_bank_sms = []
favorite_keys = set()
removed_device_keys = set()
chat_sessions = {}

chat_queues = {}
chat_queues_lock = threading.Lock()


def now_ms():
    return int(time.time() * 1000)


def format_bot_timestamp(ts_ms=None):
    if ts_ms is None:
        dt = datetime.now()
    else:
        dt = datetime.fromtimestamp(ts_ms / 1000.0)
    return dt.strftime("%d-%m-%Y | %I:%M %p")


def escape_html(text):
    return html.escape(str(text or ""), quote=False)


def normalize_rtdb_url(raw_url):
    trimmed = str(raw_url or "").strip()
    if not trimmed:
        return ""
    with_scheme = trimmed if re.match(r"^https?://", trimmed, re.I) else f"https://{trimmed}"
    try:
        parsed = urllib.parse.urlparse(with_scheme)
        host = (parsed.hostname or "").strip().lower()
        if not re.match(r"^[a-z0-9.-]+\.(?:firebaseio\.com|firebasedatabase\.app)$", host, re.I):
            return ""
        return f"https://{host}"
    except Exception:
        return ""


def extract_rtdb_urls_from_text(text):
    found = []
    seen = set()

    def add_cand(raw):
        norm = normalize_rtdb_url(raw)
        if norm and norm not in seen:
            seen.add(norm)
            found.append(norm)

    for m in re.findall(
        r"(?:https?://)?[a-z0-9.-]+\.(?:firebaseio\.com|firebasedatabase\.app)(?:/[^\s,;'\'\"<>()]*)?",
        str(text or ""),
        re.I,
    ):
        add_cand(m)
    for tok in re.split(r"[\s,;]+", str(text or "")):
        add_cand(tok)
    return found


def is_valid_rtdb_secret(secret):
    s = str(secret or "").strip()
    if not s:
        return True
    if re.match(r"^https?://", s, re.I):
        return False
    if re.search(r"(?:firebaseio\.com|firebasedatabase\.app|firebase\.google\.com)", s, re.I):
        return False
    return True


def rtdb_url_hash(url):
    norm = normalize_rtdb_url(url) or url
    return hashlib.sha1(norm.encode("utf-8")).hexdigest()[:16]


def init_rtdb_defaults():
    global rtdb_urls, rtdb_auth_secret
    env_primary = normalize_rtdb_url(os.environ.get("FIREBASE_RTDB_URL", ""))
    env_many = [
        normalize_rtdb_url(u)
        for u in re.split(r"[\s,]+", os.environ.get("FIREBASE_RTDB_URLS", ""))
        if u.strip()
    ]
    combined = []
    for u in env_many + ([env_primary] if env_primary else []) + DEFAULT_RTDB_URLS:
        norm = normalize_rtdb_url(u)
        if norm and norm not in combined:
            combined.append(norm)
    rtdb_urls = combined
    raw_sec = os.environ.get("FIREBASE_RTDB_SECRET", "").strip()
    rtdb_auth_secret = raw_sec if is_valid_rtdb_secret(raw_sec) else ""


def is_lifetime_grant(grant):
    return (
        "LIFETIME" in str(grant.get("planName", "")).upper()
        or int(grant.get("daysGranted", 0) or 0) >= 3650
    )


def is_device_removed_by_admin(device):
    if not removed_device_keys:
        return False
    digits = re.sub(r"\D", "", device.get("phoneNumber", ""))
    dev_id = str(device.get("id", "")).upper()
    finder = str(device.get("finderCode", "")).upper()
    return (
        dev_id in removed_device_keys
        or (bool(finder) and finder in removed_device_keys)
        or (len(digits) >= 6 and digits in removed_device_keys)
    )


def save_runtime_state():
    with state_lock:
        manual_devices = [
            d
            for d in synced_devices
            if not str(d.get("id", "")).startswith("rtdb_") and not is_device_removed_by_admin(d)
        ]
        sessions_sorted = sorted(
            chat_sessions.values(),
            key=lambda s: s.get("lastSeenAtMs") or s.get("joinedAtMs") or 0,
            reverse=True,
        )[:2000]
        payload = {
            "rtdbUrls": list(dict.fromkeys(rtdb_urls)),
            "rtdbUserModified": rtdb_user_modified,
            "rtdbAuthSecret": rtdb_auth_secret if (rtdb_auth_secret and is_valid_rtdb_secret(rtdb_auth_secret)) else None,
            "adminChatId": admin_chat_id or None,
            "defaultTelegramChatId": default_telegram_chat_id or None,
            "accessGrants": synced_access_grants,
            "deletedGrantChatIds": list(deleted_grant_chat_ids),
            "paymentRequests": synced_payment_requests[:100],
            "usedPaymentRefs": list(used_payment_refs)[-500:],
            "usedScreenshotHashes": list(used_screenshot_hashes)[-500:],
            "usedBankSmsIds": list(used_bank_sms_ids)[-500:],
            "recentBankSms": recent_bank_sms[:300],
            "favoriteKeys": list(favorite_keys),
            "removedDeviceKeys": list(removed_device_keys),
            "manualDevices": manual_devices,
            "chatSessions": sessions_sorted,
        }
        raw_json = json.dumps(payload, indent=2, ensure_ascii=False)
        for path in (STATE_FILE, BACKUP_STATE_FILE):
            tmp = f"{path}.tmp"
            try:
                with open(tmp, "w", encoding="utf-8") as f:
                    f.write(raw_json)
                os.replace(tmp, path)
            except Exception as exc:
                print(f"[STATE] Save warning ({path}): {exc}", file=sys.stderr)


def ensure_pinned_member_grants():
    changed = False
    t_now = now_ms()
    for pin in PINNED_PROTECTED_GRANTS:
        cid = pin["chatId"]
        if cid in deleted_grant_chat_ids:
            continue
        is_life = pin["daysGranted"] >= 3650 or "LIFETIME" in pin["planName"].upper()
        if not is_life and t_now >= pin["expiresAtMs"]:
            continue
        existing_idx = next((i for i, g in enumerate(synced_access_grants) if g.get("chatId") == cid), -1)
        existing = synced_access_grants[existing_idx] if existing_idx >= 0 else None
        if existing and existing.get("status") == "revoked" and (existing.get("updatedAtMs") or 0) > pin["issuedAtMs"]:
            continue
        sess_user = (chat_sessions.get(cid) or {}).get("username") or "telegram_user"
        if not existing:
            synced_access_grants.append({
                "id": f"grant_{re.sub(r'[^a-zA-Z0-9_-]', '_', cid)}",
                "chatId": cid,
                "username": sess_user,
                "planName": pin["planName"],
                "daysGranted": pin["daysGranted"],
                "expiresAtMs": max(t_now + 3650 * 86400000, pin["expiresAtMs"]) if is_life else pin["expiresAtMs"],
                "status": "active",
                "updatedAtMs": pin["issuedAtMs"],
            })
            changed = True
        elif is_life and (existing.get("status") != "active" or not is_lifetime_grant(existing)):
            existing["planName"] = pin["planName"]
            existing["daysGranted"] = 3650
            existing["expiresAtMs"] = max(t_now + 3650 * 86400000, int(existing.get("expiresAtMs") or 0))
            existing["status"] = "active"
            existing["updatedAtMs"] = max(t_now, int(existing.get("updatedAtMs") or 0))
            changed = True
        elif not is_life and existing.get("status") == "active" and int(existing.get("expiresAtMs") or 0) < pin["expiresAtMs"]:
            existing["daysGranted"] = max(pin["daysGranted"], int(existing.get("daysGranted") or 7))
            existing["expiresAtMs"] = pin["expiresAtMs"]
            existing["updatedAtMs"] = max(pin["issuedAtMs"], int(existing.get("updatedAtMs") or 0))
            changed = True
    if changed:
        save_runtime_state()


def load_runtime_state():
    global rtdb_urls, rtdb_user_modified, rtdb_auth_secret
    global admin_chat_id, default_telegram_chat_id
    global synced_access_grants, synced_payment_requests, recent_bank_sms, synced_devices

    def _read_safe(path):
        try:
            if not os.path.exists(path):
                return None
            with open(path, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return None

    with state_lock:
        primary = _read_safe(STATE_FILE)
        backup = _read_safe(BACKUP_STATE_FILE)
        parsed = primary or backup
        if not parsed:
            ensure_pinned_member_grants()
            return

        if isinstance(parsed.get("rtdbUrls"), list):
            loaded_urls = []
            for u in parsed["rtdbUrls"]:
                nu = normalize_rtdb_url(str(u))
                if nu and nu not in loaded_urls:
                    loaded_urls.append(nu)
            rtdb_urls = loaded_urls
        if isinstance(parsed.get("rtdbUserModified"), bool):
            rtdb_user_modified = parsed["rtdbUserModified"]
        if isinstance(parsed.get("rtdbAuthSecret"), str):
            cand = parsed["rtdbAuthSecret"].strip()
            rtdb_auth_secret = cand if is_valid_rtdb_secret(cand) else ""
        if isinstance(parsed.get("adminChatId"), str):
            admin_chat_id = parsed["adminChatId"]
        if isinstance(parsed.get("defaultTelegramChatId"), str):
            default_telegram_chat_id = parsed["defaultTelegramChatId"]

        if isinstance(parsed.get("deletedGrantChatIds"), list):
            for cid in parsed["deletedGrantChatIds"]:
                if isinstance(cid, str) and cid.strip():
                    deleted_grant_chat_ids.add(cid.strip())

        if isinstance(parsed.get("accessGrants"), list):
            synced_access_grants = [
                {
                    **g,
                    "daysGranted": max(1, min(3650, round(float(g.get("daysGranted") or 7)))),
                    "expiresAtMs": round(float(g.get("expiresAtMs") or 0)),
                    "status": "revoked" if g.get("status") == "revoked" else "active",
                }
                for g in parsed["accessGrants"]
                if isinstance(g, dict) and g.get("chatId")
            ]

        if isinstance(parsed.get("paymentRequests"), list):
            synced_payment_requests = [
                {**p, "autoVerifyUntilMs": None}
                for p in parsed["paymentRequests"]
                if isinstance(p, dict)
            ]

        for ref in parsed.get("usedPaymentRefs") or []:
            if isinstance(ref, str) and ref.strip():
                used_payment_refs.add(ref.strip().upper())
        for h in parsed.get("usedScreenshotHashes") or []:
            if isinstance(h, str) and h.strip():
                used_screenshot_hashes.add(h.strip().lower())
        for bid in parsed.get("usedBankSmsIds") or []:
            if isinstance(bid, str) and bid.strip():
                used_bank_sms_ids.add(bid.strip())
        if isinstance(parsed.get("recentBankSms"), list):
            recent_bank_sms = [
                entry for entry in parsed["recentBankSms"]
                if isinstance(entry, dict) and entry.get("body")
                and is_genuine_bank_credit_sms(entry.get("sender", ""), entry["body"])
            ][:300]
        for fk in parsed.get("favoriteKeys") or []:
            if isinstance(fk, str) and fk.strip():
                favorite_keys.add(fk.strip().upper())
        for rk in parsed.get("removedDeviceKeys") or []:
            if isinstance(rk, str) and rk.strip():
                removed_device_keys.add(rk.strip().upper())
        if isinstance(parsed.get("manualDevices"), list):
            synced_devices = [d for d in parsed["manualDevices"] if isinstance(d, dict)]

        for s in parsed.get("chatSessions") or []:
            if isinstance(s, dict) and s.get("chatId"):
                cid = str(s["chatId"])
                chat_sessions[cid] = {
                    **s,
                    "chatId": cid,
                    "activeDeviceId": "",
                    "activeFinderCode": "",
                    "activePhoneNumber": "",
                    "activePulledByGetNumber": False,
                    "menuState": "main",
                }

        if backup and primary:
            for bg in backup.get("accessGrants") or []:
                if not isinstance(bg, dict) or not bg.get("chatId"):
                    continue
                cid = bg["chatId"]
                if cid in deleted_grant_chat_ids:
                    continue
                cur_idx = next((i for i, g in enumerate(synced_access_grants) if g["chatId"] == cid), -1)
                if cur_idx < 0:
                    synced_access_grants.append(bg)
                else:
                    cur = synced_access_grants[cur_idx]
                    if bg.get("status") == "active" and (
                        int(bg.get("expiresAtMs") or 0) > int(cur.get("expiresAtMs") or 0)
                        or (cur.get("status") == "revoked" and int(bg.get("updatedAtMs") or 0) > int(cur.get("updatedAtMs") or 0))
                    ):
                        synced_access_grants[cur_idx] = bg
            for bs in backup.get("chatSessions") or []:
                if isinstance(bs, dict) and bs.get("chatId") and str(bs["chatId"]) not in chat_sessions:
                    cid = str(bs["chatId"])
                    chat_sessions[cid] = {
                        **bs,
                        "chatId": cid,
                        "activeDeviceId": "",
                        "activeFinderCode": "",
                        "activePhoneNumber": "",
                        "activePulledByGetNumber": False,
                        "menuState": "main",
                    }

        ensure_pinned_member_grants()


# ==============================================================================
# OTP / BANK SMS / PAYMENT VALIDATION HELPERS
# ==============================================================================
def normalize_extracted_otp(raw):
    trimmed = str(raw or "").strip()
    if re.match(r"^\d{3,4}[\s-]\d{3,4}$", trimmed):
        return re.sub(r"[\s-]+", "", trimmed)
    return trimmed[:32]


def extract_otp_code(body):
    text = str(body or "").strip()
    if not text:
        return ""
    without_hash = (
        re.sub(r"(?:\s+[A-Za-z0-9+/=_-]{11})+\s*$", "", text)
        if re.match(r"^\s*<#>", text)
        else text
    )
    priority_patterns = [
        (r"(?:^|[\s<>\[#\]])(\d{3}[\s-]\d{3}|\d{4}[\s-]\d{4}|\d{4,12}|(?=[A-Z0-9]*\d)[A-Z0-9]{5,14})\s+is\s+(?:your\s+)?(?:[a-z0-9_-]+\s+){0,4}(?:instagram\s+)?(?:code|otp|pin|passcode|verification(?:\s+code)?)\b", re.I),
        (r"(?:^|[\s<>\[#\]])([A-Z]{6,12})\s+[iI][sS]\s+(?:[yY][oO][uU][rR]\s+)?(?:[a-zA-Z0-9_-]+\s+){0,4}(?:[cC][oO][dD][eE]|[oO][tT][pP]|[pP][iI][nN]|[pP][aA][sS][sS][cC][oO][dD][eE]|[vV][eE][rR][iI][fF][iI][cC][aA][tT][iI][oO][nN])\b", 0),
        (r"\b(?:use|enter)\s+(?:the\s+)?(?:code\s+)?(\d{3}[\s-]\d{3}|\d{4}[\s-]\d{4}|\d{4,12}|(?=[A-Z0-9]*\d)[A-Z0-9]{5,14})\s+to\s+(?:verify|log\s*in|sign\s*in|reset|confirm|activate|complete)\b", re.I),
        (r"\b(?:instagram|meta|facebook|whatsapp|telegram)\s*(?:verification\s*)?(?:code|otp|pin|passcode)\s*(?:is|:|-)?\s*(\d{3}[\s-]\d{3}|\d{4}[\s-]\d{4}|\d{4,12}|(?=[A-Z0-9]*\d)[A-Z0-9]{5,14})\b", re.I),
        (r"\b(?:instagram|Instagram|INSTAGRAM|meta|Meta)\s*(?:verification\s*)?(?:code|otp|CODE|OTP)\s*(?:is|:|-)?\s*([A-Z]{6,12})\b", 0),
        (r"\b(?:otp|code|pin|verification\s*code|reward\s*code|passcode|login\s*code|access\s*code)\s*(?:is|:|-)?\s*(\d{3}[\s-]\d{3}|\d{4}[\s-]\d{4}|\d{4,12}|(?=[A-Z0-9]*\d)[A-Z0-9]{4,16})\b", re.I),
    ]
    for pat, flags in priority_patterns:
        m = re.search(pat, without_hash, flags)
        if m and m.group(1):
            return normalize_extracted_otp(m.group(1))
    if re.search(r"instagram|verify|verification|\bcode\b|\botp\b|#ig\b", without_hash, re.I):
        spaced = re.search(r"\b(\d{3}[\s-]\d{3})\b", without_hash)
        if spaced:
            return normalize_extracted_otp(spaced.group(1))
    for pat in (r"\b(\d{4,10})\b", r"\b((?=[A-Z0-9]*\d)[A-Z0-9]{6,14})\b"):
        m = re.search(pat, without_hash)
        if m and m.group(1):
            return normalize_extracted_otp(m.group(1))
    return ""


def is_instagram_sms(body, sender=""):
    return bool(re.search(r"\binstagram\b|ig\.me|#ig\b", f"{sender} {body}", re.I))


def detect_sim_phone_from_text(body):
    patterns = [
        r"(?:jio|airtel|vi|vodafone|idea|bsnl|sim|mobile|phone)\s*(?:no\.?|number|num)?\s*[:\-]?\s*(?:\+?91[\s-]?)?([6-9]\d{9})\b",
        r"(?:recharge|plan|pack|data)\s+(?:for|on|your)?\s*(?:\w+\s+){0,3}(?:no\.?|number)?\s*[:\-]?\s*(?:\+?91[\s-]?)?([6-9]\d{9})\b",
    ]
    for pat in patterns:
        m = re.search(pat, body, re.I)
        if m and m.group(1):
            return m.group(1)
    return ""


def is_genuine_bank_credit_sms(sender, body):
    clean_body = str(body or "").strip()
    clean_sender = str(sender or "").strip()
    if not clean_body:
        return False
    if re.match(r"^\+?\d{10,15}$", re.sub(r"[\s-]", "", clean_sender)):
        return False
    spam_pat = (
        r"(?:https?://|bit\.ly|tinyurl|go3\.in|tpm\.zone|36kb\.xyz|\.xyz/|\.zone/|"
        r"\b(?:spin777|teen\s*patti|rummy|ludo|casino|jackpot|dream11|win\s+up\s*to|"
        r"bonus|withdraw|eligible|eligibility|apply\s+now|loan\s+can\s+be|personal\s+loan|"
        r"recharge\s+now|plan\s+expired|swiggy|jiotunes|otp\s+is|is\s+otp|is\s+your\s+otp|"
        r"registration|debited|withdrawn|failed|declined|reversed|refunded|collect\s+request)\b)"
    )
    if re.search(spam_pat, clean_body, re.I):
        return False
    if not re.search(r"\b(?:credited|received|deposited|money\s+received|paid\s+you|cr\b|credit)\b", clean_body, re.I):
        return False
    has_amount = bool(re.search(r"(?:rs\.?|inr|₹)\s*[0-9]+", clean_body, re.I))
    has_bank_ctx = bool(re.search(
        r"\b(?:a/c|acct|account|upi|utr|rrn|vpa|imps|neft|rtgs|pnb|punb|sbi|hdfc|icici|axis|kotak|bob|canara|phonepe|gpay|paytm|bhim|3544)\b",
        f"{clean_sender} {clean_body}",
        re.I,
    ))
    has_bank_hdr = bool(re.search(
        r"(?:pnb|punb|sbi|hdfc|icic|axis|kotk|bob|cnrb|ubin|indus|idfc|yesb|pytm|phonepe|upi|bank)",
        clean_sender,
        re.I,
    ))
    return has_amount and has_bank_ctx and (has_bank_hdr or bool(re.search(r"\b(?:utr|rrn|upi\s*ref)\b", clean_body, re.I)))


def record_bank_sms_candidate(sms_id, sender, body, ts_ms=None):
    clean_body = str(body or "").strip()
    if not is_genuine_bank_credit_sms(sender, clean_body):
        return
    t_ms = ts_ms or now_ms()
    for entry in recent_bank_sms:
        if entry["id"] == sms_id or (entry["body"] == clean_body and abs(entry["ts"] - t_ms) < 60000):
            return
    recent_bank_sms.insert(0, {
        "id": sms_id,
        "sender": str(sender or "BANK")[:64],
        "body": clean_body[:1000],
        "ts": t_ms,
    })
    if len(recent_bank_sms) > 300:
        del recent_bank_sms[300:]


def extract_amounts_from_text(body):
    found = []
    for m in re.finditer(r"(?:rs\.?|inr|₹)\s*([0-9]+(?:,[0-9]+)*(?:\.[0-9]{1,2})?)", body, re.I):
        try:
            found.append(float(m.group(1).replace(",", "")))
        except ValueError:
            pass
    return found


def find_matching_bank_credit_sms(utr, min_amount=25):
    clean_utr = re.sub(r"[^A-Z0-9]", "", utr, flags=re.I).upper()
    if len(clean_utr) < 10:
        return None
    candidates = list(recent_bank_sms)
    for msgs in synced_messages_by_device.values():
        for m in msgs:
            candidates.append({"id": m["id"], "sender": m["sender"], "body": m["body"], "ts": now_ms()})
    for sms in candidates:
        if sms["id"] in used_bank_sms_ids:
            continue
        if not is_genuine_bank_credit_sms(sms["sender"], sms["body"]):
            continue
        upper_body = sms["body"].upper()
        digits_only = re.sub(r"\D", "", sms["body"])
        matched = clean_utr in upper_body or (bool(re.match(r"^\d{12}$", clean_utr)) and clean_utr in digits_only)
        if not matched:
            continue
        amounts = extract_amounts_from_text(sms["body"])
        if amounts and not any(a >= min_amount for a in amounts):
            continue
        return sms
    return None


def find_unclaimed_merchant_credit_sms(min_ts_ms, min_amount=25):
    cands = sorted(
        [s for s in recent_bank_sms if s["id"] not in used_bank_sms_ids and s["ts"] >= min_ts_ms - 15000],
        key=lambda x: x["ts"],
        reverse=True,
    )
    for sms in cands:
        if not is_genuine_bank_credit_sms(sms["sender"], sms["body"]):
            continue
        is_merch = sms["id"].startswith("bank_") or bool(
            re.search(r"\b(?:3544|9653024425|raja|onc25)\b", f"{sms['sender']} {sms['body']}", re.I)
        )
        if not is_merch:
            continue
        if any(a >= min_amount for a in extract_amounts_from_text(sms["body"])):
            return sms
    return None


def extract_normalized_utr(raw_input):
    trimmed = str(raw_input or "").strip()
    m12 = re.search(r"\b(\d{12})\b", trimmed)
    if m12:
        return m12.group(1)
    mt = re.search(r"\b(T\d{18,24})\b", trimmed, re.I)
    if mt:
        return mt.group(1).upper()
    return trimmed.upper()[:64]


def has_sequential_digit_run(digits, min_run=5):
    asc = 1
    desc = 1
    for i in range(1, len(digits)):
        prev = ord(digits[i - 1])
        cur = ord(digits[i])
        if cur == prev + 1:
            asc += 1
            desc = 1
        elif cur == prev - 1:
            desc += 1
            asc = 1
        else:
            asc = 1
            desc = 1
        if asc >= min_run or desc >= min_run:
            return True
    return False


def validate_qr_utr_format(raw_utr):
    utr = extract_normalized_utr(raw_utr)
    if re.match(r"^\d{12}$", utr):
        if utr.startswith("0"):
            return False, utr, "Invalid NPCI UPI UTR prefix."
        if re.match(r"^(\d)\1{11}$", utr) or re.search(r"(\d)\1{4,}", utr):
            return False, utr, "Repeated digits detected (fake UTR pattern)."
        if len(set(utr)) < 5:
            return False, utr, "Low digit variety (fake UTR pattern)."
        if has_sequential_digit_run(utr, 5):
            return False, utr, "Sequential/dummy digits (fake UTR pattern)."
        if (
            re.match(r"^(\d{2})\1{5}$", utr)
            or re.match(r"^(\d{3})\1{3}$", utr)
            or re.match(r"^(\d{4})\1{2}$", utr)
        ):
            return False, utr, "Repeating block digits (fake UTR pattern)."
        return True, utr, ""
    if re.match(r"^T\d{18,24}$", utr):
        tail = utr[1:]
        if len(set(tail)) < 5 or re.search(r"(\d)\1{5,}", tail) or has_sequential_digit_run(tail, 6):
            return False, utr, "Fake Transaction ID pattern."
        return True, utr, ""
    return False, utr, "Invalid UTR format. Genuine UPI payment requires a 12-digit UTR number."


def validate_amazon_gift_card_format(raw_code):
    trimmed = str(raw_code or "").strip().upper()
    compact = re.sub(r"[-\s]", "", trimmed)
    if not re.match(r"^[A-Z0-9]{13,16}$", compact):
        return False, trimmed[:64], "Fake/Invalid Amazon Gift Card code format (must be 14-15 alphanumeric characters)."
    if not re.search(r"[A-Z]", compact) or not re.search(r"\d", compact):
        return False, trimmed[:64], "Fake Amazon Gift Card code (must contain both letters and numbers)."
    if len(set(compact)) < 6 or re.search(r"([A-Z0-9])\1{3,}", compact):
        return False, trimmed[:64], "Repeated/dummy gift card pattern rejected."
    if re.search(r"(?:FAKE|TEST|DEMO|FREE|GIFT|CARD|ADMIN|NULL|NONE|QWERTY|ABCDEF|12345|98765)", compact, re.I):
        return False, trimmed[:64], "Dummy/test gift card code rejected automatically."
    return True, trimmed[:64], ""


# ==============================================================================
# DEVICE, FAVORITE, ACCESS, & ADMIN HELPERS
# ==============================================================================
def is_authorized_admin_identity(chat_id, tg_username="", session=None):
    sess = session or chat_sessions.get(chat_id) or {}
    clean_user = str(tg_username or sess.get("username") or "").lstrip("@").strip().lower()
    if clean_user == ADMIN_TELEGRAM_USERNAME:
        return True
    if sess.get("verifiedAdminPhone") == ADMIN_TELEGRAM_PHONE:
        return True
    if admin_chat_id and chat_id == admin_chat_id and sess.get("isAdminVerified"):
        return True
    return False


def is_chat_admin_for_keyboard(chat_id=None):
    if not chat_id:
        return False
    sess = chat_sessions.get(chat_id)
    return is_authorized_admin_identity(chat_id, (sess or {}).get("username", ""), sess)


def resolve_admin_chat_ids():
    ids = []
    seen = set()
    for cand in [admin_chat_id, default_telegram_chat_id]:
        if cand and re.match(r"^-?\d+$", cand) and cand not in seen:
            seen.add(cand)
            ids.append(cand)
    for sess in chat_sessions.values():
        cid = sess.get("chatId", "")
        if re.match(r"^-?\d+$", cid) and cid not in seen and is_authorized_admin_identity(cid, sess.get("username", ""), sess):
            seen.add(cid)
            ids.append(cid)
    return ids


def is_device_favorited(device):
    digits = re.sub(r"\D", "", device.get("phoneNumber", ""))
    return (
        str(device.get("id", "")).upper() in favorite_keys
        or str(device.get("finderCode", "")).upper() in favorite_keys
        or (len(digits) >= 6 and digits in favorite_keys)
        or bool(device.get("isFavorite"))
    )


def set_device_favorite_state(device, next_fav):
    digits = re.sub(r"\D", "", device.get("phoneNumber", ""))
    keys = [str(device.get("id", "")).upper(), str(device.get("finderCode", "")).upper()]
    if digits:
        keys.append(digits)
    for k in keys:
        if not k:
            continue
        if next_fav:
            favorite_keys.add(k)
        else:
            favorite_keys.discard(k)
    device["isFavorite"] = next_fav
    save_runtime_state()


def mark_device_removed_by_admin(device):
    global synced_devices
    digits = re.sub(r"\D", "", device.get("phoneNumber", ""))
    removed_device_keys.add(str(device.get("id", "")).upper())
    if device.get("finderCode"):
        removed_device_keys.add(str(device["finderCode"]).upper())
    if len(digits) >= 6:
        removed_device_keys.add(digits)
    synced_devices = [
        d for d in synced_devices
        if d.get("id") != device.get("id")
        and not (len(digits) >= 6 and re.sub(r"\D", "", d.get("phoneNumber", "")) == digits)
    ]
    synced_messages_by_device.pop(device.get("id"), None)
    for sess in chat_sessions.values():
        if sess.get("activeDeviceId") == device.get("id"):
            sess["activeDeviceId"] = ""
            sess["activeFinderCode"] = ""
            sess["activePhoneNumber"] = ""
            sess["activePulledByGetNumber"] = False
            if sess.get("menuState") == "connected":
                sess["menuState"] = "main"
    save_runtime_state()


def get_online_bot_devices():
    return [d for d in synced_devices if d.get("status") == "online" and not is_device_removed_by_admin(d)]


def get_device_otp_stats(device):
    msgs = synced_messages_by_device.get(device["id"]) or []
    otp_count = sum(1 for m in msgs if m.get("otpCode") or extract_otp_code(m.get("body", "")))
    if otp_count == 0 and device.get("lastSmsPreview") and extract_otp_code(device["lastSmsPreview"]):
        otp_count = 1
    return otp_count, max(int(device.get("smsCount") or 0), len(msgs))


def get_otp_receiving_bot_devices():
    online = get_online_bot_devices()
    if not online:
        return []
    scored = [(d, *get_device_otp_stats(d)) for d in online]
    otp_devs = sorted([x for x in scored if x[1] > 0], key=lambda x: (-x[1], -x[2]))
    if otp_devs:
        return [x[0] for x in otp_devs]
    sms_devs = sorted([x for x in scored if x[2] > 0], key=lambda x: -x[2])
    if sms_devs:
        return [x[0] for x in sms_devs]
    return online


def get_active_grant_for_chat(chat_id):
    sess = chat_sessions.get(chat_id)
    if is_authorized_admin_identity(chat_id, (sess or {}).get("username", ""), sess) or (sess or {}).get("isAdminVerified"):
        return {
            "id": "admin-bypass",
            "chatId": chat_id,
            "username": (sess or {}).get("username") or ADMIN_TELEGRAM_USERNAME,
            "planName": "ADMIN",
            "daysGranted": 9999,
            "expiresAtMs": now_ms() + 365 * 86400000,
            "status": "active",
        }
    t_now = now_ms()
    for g in synced_access_grants:
        if g.get("chatId") == chat_id and g.get("status") == "active" and (is_lifetime_grant(g) or int(g.get("expiresAtMs") or 0) > t_now):
            return g
    return None


# ==============================================================================
# KEYBOARDS & CARD FORMATTERS (MATCHES LATEST @Oniocokh_bot UI)
# ==============================================================================
def get_main_keyboard(chat_id=None):
    is_admin = is_chat_admin_for_keyboard(chat_id)
    rows = [
        [{"text": "📱 GET NUMBERS"}, {"text": "🔍 FIND NUMBER"}],
        [{"text": "⭐ FAVORITES"}, {"text": "💳 VIP ACCESS"}],
        [{"text": "👤 MY ACCOUNT"}, {"text": "⚙️ ADMIN PANEL"}] if is_admin else [{"text": "👤 MY ACCOUNT"}, {"text": "🏠 HOME MENU"}],
    ]
    if is_admin:
        rows.append([{"text": "🏠 HOME MENU"}])
    return {"keyboard": rows, "resize_keyboard": True, "one_time_keyboard": False, "is_persistent": True}


def get_admin_keyboard():
    return {
        "keyboard": [
            [{"text": "➕ ADD MEMBER"}, {"text": "♾️ LIFETIME ACCESS"}],
            [{"text": "👥 BOT USERS"}, {"text": "👥 ACTIVE USERS"}],
            [{"text": "👥 GRANT ACCESS"}, {"text": "🚫 REVOKE ACCESS"}],
            [{"text": "💳 PAYMENTS"}, {"text": "📱 ONLINE NUMBERS"}],
            [{"text": "➕ ADD NUMBER"}, {"text": "🗑️ REMOVE NUMBER"}],
            [{"text": "🔗 ADD FIREBASE LINK"}, {"text": "🗑️ REMOVE FIREBASE LINK"}],
            [{"text": "🔄 SYNC FIREBASE RTDB"}, {"text": "🏠 HOME MENU"}],
            [{"text": "🔒 LOGOUT ADMIN"}],
        ],
        "resize_keyboard": True,
        "one_time_keyboard": False,
        "is_persistent": True,
    }


def get_connected_keyboard(chat_id=None):
    rows = [
        [{"text": "🔄 REFRESH SMS"}, {"text": "📩 VIEW MESSAGES"}],
        [{"text": "+ NEW NUMBER"}, {"text": "⭐ ADD FAVORITE"}],
        [{"text": "⭐ FAVORITES"}, {"text": "🏠 HOME MENU"}],
    ]
    if is_chat_admin_for_keyboard(chat_id):
        rows.append([{"text": "⚙️ ADMIN PANEL"}])
    return {"keyboard": rows, "resize_keyboard": True, "one_time_keyboard": False, "is_persistent": True}


def get_payment_keyboard():
    return {
        "keyboard": [
            [{"text": "📱 UPI QR PAYMENT"}, {"text": "🎁 AMAZON GIFT CARD"}],
            [{"text": "⬅️ BACK"}],
        ],
        "resize_keyboard": True,
        "one_time_keyboard": False,
        "is_persistent": True,
    }


def build_connected_inline_actions(device, chat_id=None):
    fav_label = "★ SAVED FAV" if device.get("isFavorite") else "⭐ FAVORITE"
    rows = [
        [
            {"text": "📋 COPY NUMBER", "copy_text": {"text": device["phoneNumber"]}},
            {"text": fav_label, "callback_data": f"TOGGLE_FAV:{device['id']}"},
        ],
        [
            {"text": "🔄 REFRESH", "callback_data": f"REFRESH:{device['id']}"},
            {"text": "⏭️ NEXT", "callback_data": "NEXT_ONLINE"},
        ],
    ]
    if is_chat_admin_for_keyboard(chat_id):
        rows.append([{"text": "🗑️ REMOVE NUMBER", "callback_data": f"RM_DEV:{device['id']}"}])
    return {"inline_keyboard": rows}


APP_FILTERS = [
    ("🟣 IG", re.compile(r"\binstagram\b|ig\.me|#ig\b", re.I)),
    ("🟢 WA", re.compile(r"\bwhatsapp\b", re.I)),
    ("🔵 TG", re.compile(r"\btelegram\b", re.I)),
    ("🔴 Google", re.compile(r"\bgoogle\b|\bg-\d{6}\b|\byoutube\b|\bgmail\b", re.I)),
    ("🛒 Shop", re.compile(r"\bflipkart\b|\bamazon\b|\bmyntra\b|\bmeesho\b|\bblinkit\b|\bzepto\b", re.I)),
]


def detect_device_apps(device):
    msgs = synced_messages_by_device.get(device["id"]) or []
    haystack = "\n".join([device.get("lastSmsPreview") or ""] + [f"{m.get('sender', '')} {m.get('body', '')}" for m in msgs[:40]])
    return [lbl for lbl, pat in APP_FILTERS if pat.search(haystack)]


def format_connected_card(device, latest_msgs=None):
    latest_msgs = latest_msgs or []
    status_badge = "🟢 <b>LIVE ONLINE</b>" if device.get("status") == "online" else "🔴 <b>OFFLINE</b>"
    last_sms = escape_html(device.get("lastSmsAt") or "Waiting for SMS")
    live_line = (
        "📡 <b>Live Push:</b> 🟢 <i>Auto-arrives here in 1–2s</i>"
        if device.get("liveSmsActive", True)
        else "⏸️ <b>Live Push:</b> <i>Paused</i>"
    )
    fav_badge = "  •  ⭐ <b>Favorite</b>" if device.get("isFavorite") else ""
    apps = detect_device_apps(device)
    apps_line = (
        f"🏷️ <b>Apps Seen:</b> {escape_html(' · '.join(apps))}{fav_badge}"
        if apps
        else f"🏷️ <b>Activity:</b> {len(latest_msgs)} recent SMS{fav_badge}"
    )
    lines = [
        f"⚡ <b>LIVE NUMBER READY</b>  ·  {status_badge}",
        "━━━━━━━━━━━━━━━━━━━━",
        "<blockquote>"
        f"📞 <b>Number:</b> <code>{escape_html(device['phoneNumber'])}</code> <i>(tap to copy)</i>\n"
        f"{apps_line}\n"
        f"🕒 <b>Last SMS:</b> {last_sms}\n"
        f"{live_line}"
        "</blockquote>",
    ]
    if latest_msgs:
        recent_slice = list(reversed(latest_msgs[:5]))
        recent_ids = {m["id"] for m in recent_slice}
        extra_insta = list(reversed([
            m for m in latest_msgs
            if m["id"] not in recent_ids and is_instagram_sms(m.get("body", ""), m.get("sender", ""))
        ][:2]))
        lines.append("")
        lines.append(f"📩 <b>LATEST OTP &amp; SMS ({len(recent_slice)})</b>")
        cur_len = len("\n".join(lines))
        for msg in recent_slice:
            code = msg.get("otpCode") or extract_otp_code(msg.get("body", ""))
            otp_badge = f"\n\n🔑 <b>OTP:</b> <code>{escape_html(code)}</code> <i>(tap to copy)</i>" if code else ""
            block = (
                f"<blockquote><b>{escape_html(msg['sender'])}</b>  ·  <i>{escape_html(msg['receivedAtLabel'])}</i>\n"
                f"{escape_html(msg['body'][:260])}{otp_badge}</blockquote>"
            )
            if cur_len + len(block) + 1 <= 3850:
                lines.append(block)
                cur_len += len(block) + 1
        if extra_insta and cur_len < 3650:
            hdr = f"🟣 <b>RECENT INSTAGRAM SMS ({len(extra_insta)})</b>"
            lines.extend(["", hdr])
            cur_len += len(hdr) + 2
            for msg in extra_insta:
                code = msg.get("otpCode") or extract_otp_code(msg.get("body", ""))
                otp_badge = f"\n\n🔑 <b>INSTAGRAM OTP:</b> <code>{escape_html(code)}</code> <i>(tap to copy)</i>" if code else ""
                block = (
                    f"<blockquote>🟣 <b>{escape_html(msg['sender'])}</b>  ·  <i>{escape_html(msg['receivedAtLabel'])}</i>\n"
                    f"{escape_html(msg['body'][:260])}{otp_badge}</blockquote>"
                )
                if cur_len + len(block) + 1 <= 3900:
                    lines.append(block)
                    cur_len += len(block) + 1
    else:
        lines.append("")
        lines.append("⏳ <i>Ready! App me number daalein — OTP yahi par 1–2 sec me aayega.</i>")
    return "\n".join(lines)


def format_sms_list(messages, max_chars=3650):
    if not messages:
        return (
            "<blockquote>"
            "📭 <b>INBOX EMPTY</b>\n"
            "Abhi is number par koi SMS nahi aaya hai.\n"
            "Tap 🔄 <b>REFRESH</b> ya 2 sec wait karein."
            "</blockquote>"
        )
    blocks = []
    char_cnt = 0
    for m in messages[:15]:
        code = m.get("otpCode") or extract_otp_code(m.get("body", ""))
        prefix = "🟣" if is_instagram_sms(m.get("body", ""), m.get("sender", "")) else "📩"
        otp_tag = f"\n\n🔑 <b>OTP:</b> <code>{escape_html(code)}</code> <i>(tap to copy)</i>" if code else ""
        block = (
            f"<blockquote>{prefix} <b>{escape_html(m['sender'])}</b>  ·  <i>{escape_html(m['receivedAtLabel'])}</i>\n"
            f"{escape_html(m['body'][:320])}{otp_tag}</blockquote>"
        )
        if blocks and char_cnt + len(block) + 1 > max_chars:
            break
        blocks.append(block)
        char_cnt += len(block) + 1
    return "\n".join(reversed(blocks))


def format_incoming_sms_alert(msg):
    code = msg.get("otpCode") or extract_otp_code(msg.get("body", ""))
    is_ig = is_instagram_sms(msg.get("body", ""), msg.get("sender", ""))
    title = "🟣 <b>INSTAGRAM LIVE OTP RECEIVED</b>" if is_ig else "⚡ <b>LIVE OTP RECEIVED</b>"
    lines = [
        title,
        "━━━━━━━━━━━━━━━━━━━━",
        f"📞 <code>{escape_html(msg['phoneNumber'])}</code>  •  <b>{escape_html(msg['sender'])}</b>",
        f"🕒 <i>{escape_html(msg['receivedAtLabel'])}</i>",
        f"<blockquote>{escape_html(msg['body'])}</blockquote>",
    ]
    if code:
        lines.append(f"🎯 <b>OTP CODE:</b> <code>{escape_html(code)}</code> <i>(tap to copy)</i>")
    return "\n".join(lines)


def format_payment_card():
    return "\n".join([
        "💎 <b>VIP ACCESS PASS</b>",
        "━━━━━━━━━━━━━━━━━━━━",
        "<blockquote>"
        "✦ <b>Plan:</b> 💎 WEEKLY PREMIUM\n"
        "✦ <b>Price:</b> <b>₹25</b> only\n"
        "✦ <b>Validity:</b> <b>7 Days Unlimited</b>\n"
        "✦ <b>Speed:</b> ⚡ 1–2s Live OTP Delivery\n"
        "✦ <b>Supported:</b> 🟣 Instagram • 🟢 WhatsApp • 🔴 Google • All Apps\n"
        "✦ <b>Activation:</b> QR Pay → Payment Screenshot Bhejein!"
        "</blockquote>",
        "",
        "👇 <i>Niche 1-tap payment method chunein:</i>",
    ])


def build_payment_inline_actions():
    return {
        "inline_keyboard": [
            [{"text": "📱 PAY ₹25 VIA UPI QR (INSTANT)", "callback_data": "UPI_QR_NEW"}],
            [{"text": "🎁 AMAZON GIFT CARD", "callback_data": "AMZ_GC_PROMPT"}],
        ]
    }


# ==============================================================================
# TELEGRAM BOT API WRAPPERS
# ==============================================================================
def call_telegram_api(method, payload=None, timeout_sec=15):
    url = f"https://api.telegram.org/bot{BOT_TOKEN}/{method}"
    try:
        resp = http_session.post(url, json=payload or {}, timeout=timeout_sec)
        return resp.json()
    except Exception as exc:
        return {"ok": False, "description": str(exc)}


def strip_unsupported_copy_buttons(markup, chat_id=None):
    if not isinstance(markup, dict) or not isinstance(markup.get("inline_keyboard"), list):
        return markup
    filtered = [
        [btn for btn in row if "copy_text" not in btn]
        for row in markup["inline_keyboard"]
    ]
    filtered = [r for r in filtered if r]
    if not filtered:
        return get_main_keyboard(chat_id)
    return {"inline_keyboard": filtered}


def strip_html_tags(text):
    plain = re.sub(r"</?(?:b|i|code|pre|u|s|blockquote)>", "", text, flags=re.I)
    return plain.replace("&lt;", "<").replace("&gt;", ">").replace("&amp;", "&")


def toast_callback(callback_query_id, text=None):
    if not callback_query_id:
        return
    payload = {"callback_query_id": callback_query_id}
    if text:
        payload["text"] = text[:180]
    call_telegram_api("answerCallbackQuery", payload, timeout_sec=6)


def send_telegram_message(chat_id, text, reply_markup=None):
    global messages_sent, last_bot_error
    if not BOT_TOKEN or not chat_id:
        return False
    markup = reply_markup or get_main_keyboard(chat_id)
    res = call_telegram_api("sendMessage", {
        "chat_id": chat_id,
        "text": text,
        "parse_mode": "HTML",
        "reply_markup": markup,
    })
    if res.get("ok"):
        messages_sent += 1
        return True
    safe_markup = strip_unsupported_copy_buttons(markup, chat_id)
    retry = call_telegram_api("sendMessage", {
        "chat_id": chat_id,
        "text": strip_html_tags(text),
        "reply_markup": safe_markup,
    })
    if retry.get("ok"):
        messages_sent += 1
        return True
    last_bot_error = retry.get("description") or res.get("description") or "sendMessage failed"
    return False


def edit_telegram_message_text(chat_id, message_id, text, inline_markup=None):
    if not BOT_TOKEN or not chat_id or not message_id:
        return False
    payload = {"chat_id": chat_id, "message_id": message_id, "text": text, "parse_mode": "HTML"}
    if inline_markup:
        payload["reply_markup"] = inline_markup
    res = call_telegram_api("editMessageText", payload)
    if res.get("ok") or (res.get("description") and "message is not modified" in res["description"].lower()):
        return True
    safe_markup = strip_unsupported_copy_buttons(inline_markup, chat_id)
    retry_payload = {"chat_id": chat_id, "message_id": message_id, "text": text, "parse_mode": "HTML"}
    if isinstance(safe_markup, dict) and "inline_keyboard" in safe_markup:
        retry_payload["reply_markup"] = safe_markup
    retry = call_telegram_api("editMessageText", retry_payload)
    return bool(retry.get("ok") or (retry.get("description") and "message is not modified" in retry["description"].lower()))


def reply_or_edit_inline_card(chat_id, callback_msg_id, text, inline_markup=None):
    if callback_msg_id and edit_telegram_message_text(chat_id, callback_msg_id, text, inline_markup):
        return True
    return send_telegram_message(chat_id, text, inline_markup)


def send_telegram_photo_bytes(chat_id, img_bytes, caption, reply_markup=None, filename="upi_qr_25.png"):
    global messages_sent, last_bot_error
    url = f"https://api.telegram.org/bot{BOT_TOKEN}/sendPhoto"
    mime = "image/png" if filename.lower().endswith(".png") else "image/jpeg"

    def _post(markup, with_html):
        data = {
            "chat_id": chat_id,
            "caption": caption if with_html else strip_html_tags(caption),
        }
        if with_html:
            data["parse_mode"] = "HTML"
        if markup:
            data["reply_markup"] = json.dumps(markup)
        files = {"photo": (filename, img_bytes, mime)}
        resp = http_session.post(url, data=data, files=files, timeout=20)
        return resp.json()

    try:
        res = _post(reply_markup, True)
        if res.get("ok"):
            messages_sent += 1
            return True
        retry = _post(strip_unsupported_copy_buttons(reply_markup, chat_id), False)
        if retry.get("ok"):
            messages_sent += 1
            return True
        last_bot_error = retry.get("description") or res.get("description") or "sendPhoto failed"
    except Exception as exc:
        last_bot_error = str(exc)
    return send_telegram_message(chat_id, caption, reply_markup)


def download_telegram_file_bytes(file_id):
    res = call_telegram_api("getFile", {"file_id": file_id})
    if not res.get("ok") or not (res.get("result") or {}).get("file_path"):
        return None
    fp = res["result"]["file_path"]
    try:
        dl = http_session.get(f"https://api.telegram.org/file/bot{BOT_TOKEN}/{fp}", timeout=15)
        if dl.ok:
            return dl.content
    except Exception:
        pass
    return None


# ==============================================================================
# CHANNEL MEMBERSHIP CHECK (@bhai3131)
# ==============================================================================
def check_channel_membership(chat_id, user_id=None, force_fresh=False):
    sess = chat_sessions.get(chat_id)
    if not force_fresh and sess and sess.get("hasJoinedChannel") and (now_ms() - int(sess.get("channelVerifiedAtMs") or 0) < 300000):
        return {"checked": True, "joined": True}
    try:
        uid = int(user_id or chat_id)
    except (TypeError, ValueError):
        return {"checked": False, "joined": False, "error": "Invalid Telegram user ID"}
    res = call_telegram_api("getChatMember", {"chat_id": REQUIRED_CHANNEL_USERNAME, "user_id": uid})
    if not res.get("ok") or not res.get("result"):
        desc = res.get("description") or "Channel check failed"
        inacc = bool(re.search(r"inaccessible|member list|not enough rights|administrator|chat not found|have no rights", desc, re.I))
        return {"checked": False, "joined": False, "inaccessible": inacc, "error": desc}
    status = res["result"].get("status", "")
    joined = status in ("creator", "administrator", "member") or (status == "restricted" and bool(res["result"].get("is_member")))
    if sess is not None:
        sess["hasJoinedChannel"] = joined
        sess["channelVerifiedAtMs"] = now_ms() if joined else 0
    return {"checked": True, "joined": joined}


def send_force_join_prompt(chat_id, retry_warning=False, check_error=None):
    sess = chat_sessions.get(chat_id)
    if sess is not None:
        sess["channelPromptShownAtMs"] = now_ms()
        save_runtime_state()
    warning = (
        "<blockquote>⛔ <b>PEHLE CHANNEL JOIN KAREIN!</b>\n"
        "Channel join kiye bina bot start nahi hoga. Niche button se channel join karein, phir <b>✅ I HAVE JOINED / VERIFY</b> par tap karein.</blockquote>\n\n"
        if retry_warning
        else ""
    )
    is_admin = is_authorized_admin_identity(chat_id, (sess or {}).get("username", ""), sess)
    admin_note = (
        f"\n\n<i>⚠️ Admin Tip: {escape_html(check_error)} (@Oniocokh_bot ko @bhai3131 me Admin banayein for strict API check)</i>"
        if is_admin and check_error
        else ""
    )
    msg = "\n".join([
        warning + "⚡ <b>BHAI3131  ·  LIVE OTP HUB</b>",
        "━━━━━━━━━━━━━━━━━━━━",
        f"<blockquote>📢 <b>OFFICIAL CHANNEL VERIFICATION</b>\nBot use karne ke liye pehle hamara Telegram channel join karein:\n👉 {REQUIRED_CHANNEL_URL} (<b>{REQUIRED_CHANNEL_USERNAME}</b>)</blockquote>",
        "<b>✨ Quick Steps:</b>",
        "1️⃣ Niche <b>📢 JOIN @bhai3131 CHANNEL</b> tap karein",
        "2️⃣ Join karne ke baad <b>✅ I HAVE JOINED / VERIFY</b> dabayein" + admin_note,
    ])
    send_telegram_message(chat_id, msg, {
        "inline_keyboard": [
            [{"text": "📢 JOIN @bhai3131 CHANNEL", "url": REQUIRED_CHANNEL_URL}],
            [{"text": "✅ I HAVE JOINED / VERIFY", "callback_data": "VERIFY_CHANNEL"}],
        ]
    })


# ==============================================================================
# LIVE FIREBASE RTDB SYNC & SMS DELIVERY
# ==============================================================================
def build_rtdb_node_url(base, sub_path):
    clean = sub_path if sub_path.startswith("/") else f"/{sub_path}"
    if not sub_path:
        clean = ""
    if rtdb_auth_secret:
        return f"{base}{clean}.json?auth={urllib.parse.quote(rtdb_auth_secret)}"
    return f"{base}{clean}.json"


def fetch_rtdb_json(url, timeout_sec=8):
    try:
        r = http_session.get(url, timeout=timeout_sec)
        if not r.ok:
            return False, r.status_code, None, (r.text or "")[:120]
        return True, r.status_code, r.json(), ""
    except Exception as exc:
        return False, 0, None, str(exc)[:120]


def parse_rtdb_msg_ts(m, m_key):
    for cand in (m.get("rawTs"), m.get("ts"), m.get("timestamp"), m.get("createdAt"), m.get("id"), m_key):
        try:
            n = float(cand)
            if 1e9 <= n < 1e11:
                return int(n * 1000)
            if n >= 1e11:
                return int(n)
        except (TypeError, ValueError):
            pass
    dt_str = str(m.get("dateTime") or m.get("time") or m.get("date") or "").strip()
    dm = re.match(r"^(\d{1,2})[-/](\d{1,2})[-/](\d{4})\s*\|\s*(\d{1,2}):(\d{2})(?::(\d{2}))?\s*(AM|PM)?$", dt_str, re.I)
    if dm:
        day, mon, yr = int(dm.group(1)), int(dm.group(2)), int(dm.group(3))
        hr, mn, sc = int(dm.group(4)), int(dm.group(5)), int(dm.group(6) or 0)
        ampm = (dm.group(7) or "").upper()
        if ampm == "PM" and hr < 12:
            hr += 12
        if ampm == "AM" and hr == 12:
            hr = 0
        try:
            return int(datetime(yr, mon, day, hr, mn, sc).timestamp() * 1000)
        except Exception:
            pass
    try:
        return int(float(m.get("id") or m_key or 0))
    except (TypeError, ValueError):
        return 0


def deliver_incoming_sms(device, sender, body, external_id=None):
    clean_body = str(body or "").strip()[:1000]
    clean_sender = (str(sender or "SMS-GATEWAY").strip() or "SMS-GATEWAY")[:64]
    received_label = format_bot_timestamp()
    otp_code = extract_otp_code(clean_body)
    msg_id = external_id or f"sms_{now_ms()}_{secrets.token_hex(3)}"

    record_bank_sms_candidate(msg_id, clean_sender, clean_body, now_ms())
    if is_genuine_bank_credit_sms(clean_sender, clean_body):
        reconcile_auto_verifying_payments()

    new_sms = {
        "id": msg_id,
        "ownerId": device.get("ownerId", "rtdb_sync"),
        "deviceId": device["id"],
        "finderCode": device["finderCode"],
        "phoneNumber": device["phoneNumber"],
        "sender": clean_sender,
        "body": clean_body,
        "otpCode": otp_code,
        "receivedAtLabel": received_label,
        "forwardedToTelegram": False,
    }

    t_now = now_ms()
    target_chats = []
    with state_lock:
        for sess in chat_sessions.values():
            if sess.get("menuState") != "connected" or not sess.get("activePulledByGetNumber"):
                continue
            if sess.get("activeDeviceId") != device["id"]:
                continue
            cid = sess["chatId"]
            is_admin = is_authorized_admin_identity(cid, sess.get("username", ""), sess)
            if not is_admin and not sess.get("hasJoinedChannel"):
                continue
            grant = get_active_grant_for_chat(cid)
            if grant and (is_lifetime_grant(grant) or int(grant.get("expiresAtMs") or 0) > t_now):
                target_chats.append(cid)

    delivered = False
    if device.get("liveSmsActive", True) and target_chats:
        alert_text = format_incoming_sms_alert(new_sms)
        for cid in target_chats:
            if send_telegram_message(cid, alert_text, build_connected_inline_actions(device, cid)):
                delivered = True
    new_sms["forwardedToTelegram"] = delivered

    with state_lock:
        existing = synced_messages_by_device.get(device["id"]) or []
        if not any(m["id"] == msg_id for m in existing):
            synced_messages_by_device[device["id"]] = ([new_sms] + existing)[:50]
            device["lastSmsAt"] = received_label
            device["lastSmsPreview"] = clean_body[:200]
            device["smsCount"] = int(device.get("smsCount") or 0) + 1
    return new_sms


def fetch_single_rtdb_devices(url, source_idx):
    base = url.rstrip("/")
    host_prefix = re.sub(r"[^a-zA-Z0-9]", "", re.sub(r"^https?://", "", base).split(".")[0])[:12] or str(source_idx)
    host_slug = "" if source_idx == 0 else f"{host_prefix}_{rtdb_url_hash(base)[:4]}_"
    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
            f1 = pool.submit(fetch_rtdb_json, build_rtdb_node_url(base, "/clients"), 8)
            f2 = pool.submit(fetch_rtdb_json, build_rtdb_node_url(base, "/profex_incoming"), 8)
            c_ok, c_status, c_data, c_err = f1.result()
            p_ok, _p_status, p_data, _p_err = f2.result()

        if not c_ok and not p_ok:
            return {"ok": False, "url": base, "error": f"HTTP {c_status}: {c_err or 'RTDB unreachable'}", "devices": [], "msgs": {}, "new_sms": []}

        clients_node = c_data if isinstance(c_data, dict) else None
        profex_node = p_data if isinstance(p_data, dict) else None
        online_map = {}

        def push_msg(entry, m_key, m_val, prefix, seq):
            if not isinstance(m_val, dict):
                return
            if m_val.get("type") == "outgoing":
                return
            body = str(m_val.get("message") or m_val.get("text") or m_val.get("body") or m_val.get("msg") or m_val.get("content") or m_val.get("sms") or "").strip()
            if not body:
                return
            sender = str(m_val.get("sender") or m_val.get("from") or m_val.get("address") or m_val.get("title") or m_val.get("app") or "SMS")[:64]
            dt_str = str(m_val.get("dateTime") or m_val.get("time") or format_bot_timestamp())[:64]
            ts = parse_rtdb_msg_ts(m_val, m_key)
            entry["msgs"].append({
                "key": f"{host_slug}{prefix}_{entry['deviceKey']}_{m_key}",
                "sender": sender,
                "body": body[:1000],
                "dateTime": dt_str,
                "ts": ts,
                "seq": seq,
            })

        generic_devices = []
        generic_sms = []

        if clients_node:
            for dev_key, raw in clients_node.items():
                if not isinstance(raw, dict):
                    continue
                is_on = raw.get("status") in (True, "true", "online") or raw.get("online") is True
                if not is_on:
                    continue
                phone_raw = raw.get("phoneNumber") if isinstance(raw.get("phoneNumber"), str) else (raw.get("number") if isinstance(raw.get("number"), str) else "")
                ping_obj = raw.get("ping") if isinstance(raw.get("ping"), dict) else {}
                entry = {
                    "deviceKey": dev_key,
                    "battery": raw.get("battery") if isinstance(raw.get("battery"), str) else "",
                    "isFavorite": raw.get("starred") is True,
                    "pingTs": int(ping_obj.get("ts") or 0) if str(ping_obj.get("ts") or "").isdigit() else 0,
                    "detectedPhone": re.sub(r"[^+0-9]", "", phone_raw)[:24],
                    "msgs": [],
                }
                if isinstance(raw.get("messages"), dict):
                    for seq, (mk, mv) in enumerate(raw["messages"].items()):
                        push_msg(entry, mk, mv, "cm", seq)
                online_map[dev_key] = entry

            # Batch fetch /messages/<devKey> concurrently
            online_keys = list(online_map.keys())
            if online_keys:
                with concurrent.futures.ThreadPoolExecutor(max_workers=12) as pool:
                    fut_map = {
                        pool.submit(fetch_rtdb_json, build_rtdb_node_url(base, f"/messages/{urllib.parse.quote(dk, safe='')}"), 9): dk
                        for dk in online_keys
                    }
                    for fut in concurrent.futures.as_completed(fut_map):
                        dk = fut_map[fut]
                        ok_m, _, m_data, _ = fut.result()
                        if ok_m and isinstance(m_data, dict):
                            entry = online_map[dk]
                            seq = len(entry["msgs"])
                            for mk, mv in m_data.items():
                                push_msg(entry, mk, mv, "msg", seq)
                                seq += 1

            if profex_node:
                for dk, dm in profex_node.items():
                    entry = online_map.get(dk)
                    if not entry or not isinstance(dm, dict):
                        continue
                    seq = len(entry["msgs"])
                    for mk, mv in dm.items():
                        push_msg(entry, mk, mv, "pfx", seq)
                        seq += 1
        elif profex_node:
            for dk, dm in profex_node.items():
                if not isinstance(dm, dict):
                    continue
                entry = {"deviceKey": dk, "battery": "", "isFavorite": False, "pingTs": 0, "detectedPhone": "", "msgs": []}
                for seq, (mk, mv) in enumerate(dm.items()):
                    push_msg(entry, mk, mv, "pfx", seq)
                if entry["msgs"]:
                    online_map[dk] = entry
        else:
            r_ok, _, r_data, _ = fetch_rtdb_json(build_rtdb_node_url(base, ""), 8)
            if r_ok and isinstance(r_data, dict):
                def inspect_generic(k, val, parent_k=""):
                    if not isinstance(val, dict):
                        return
                    ph = val.get("phoneNumber") or val.get("number") or val.get("phone") or val.get("mobile") or val.get("simNumber")
                    mv = val.get("body") or val.get("message") or val.get("sms") or val.get("text") or val.get("otp")
                    fv = val.get("finderCode") or val.get("finder") or val.get("deviceId") or val.get("code")
                    sv = val.get("sender") or val.get("from") or val.get("address") or "RTDB-SMS"
                    if isinstance(ph, str) and not mv and not val.get("to"):
                        if val.get("status") not in ("offline", False):
                            fc = re.sub(r"[^A-Z0-9-]", "", fv.strip().upper())[:32] if isinstance(fv, str) and fv.strip() else f"KB-{re.sub(r'[^A-Z0-9]', 'X', k[:6].upper())}"
                            generic_devices.append({
                                "finderCode": fc,
                                "phoneNumber": re.sub(r"[^+0-9]", "", ph)[:24],
                                "label": val.get("label")[:64] if isinstance(val.get("label"), str) else "RTDB Device",
                            })
                    if isinstance(mv, str) and mv.strip() and not val.get("to") and val.get("isSended") is None:
                        cph = re.sub(r"[^+0-9]", "", ph)[:24] if isinstance(ph, str) else re.sub(r"[^+0-9]", "", parent_k)[:24]
                        generic_sms.append({
                            "key": f"{host_slug}gen_{parent_k}_{k}",
                            "phoneNumber": cph,
                            "finderCode": fv.upper() if isinstance(fv, str) else "",
                            "sender": sv[:64] if isinstance(sv, str) else "RTDB-SMS",
                            "body": mv.strip()[:1000],
                        })
                    for ck, cv in val.items():
                        if isinstance(cv, dict):
                            inspect_generic(ck, cv, k)

                for tk, tv in r_data.items():
                    inspect_generic(tk, tv)

        def entry_otp_count(e):
            return sum(1 for m in e["msgs"] if extract_otp_code(m["body"]))

        sorted_entries = sorted(
            online_map.values(),
            key=lambda e: (-(1 if entry_otp_count(e) > 0 else 0), -entry_otp_count(e), -len(e["msgs"]), -e["pingTs"]),
        )

        built_devices = []
        msgs_by_dev = {}
        new_sms_items = []

        for entry in sorted_entries:
            entry["msgs"].sort(key=lambda m: (-m["ts"], -m["seq"]))
            for m in entry["msgs"]:
                record_bank_sms_candidate(m["key"], m["sender"], m["body"], m["ts"] or now_ms())
                if not entry["detectedPhone"]:
                    found = detect_sim_phone_from_text(m["body"])
                    if found:
                        entry["detectedPhone"] = found

            finder_code = re.sub(r"[^A-Z0-9-]", "X", entry["deviceKey"][:8].upper())
            hex_clean = re.sub(r"[^0-9a-f]", "", entry["deviceKey"], flags=re.I)[:12] or "100001"
            num_fallback = str(int(hex_clean, 16))[-10:].zfill(10)
            phone_num = entry["detectedPhone"] or num_fallback
            dev_id = f"rtdb_{host_slug}{re.sub(r'[^a-zA-Z0-9_-]', '_', entry['deviceKey'])}"
            latest_m = entry["msgs"][0] if entry["msgs"] else None
            otp_cnt = entry_otp_count(entry)
            lbl_parts = [
                f"Bat {entry['battery']}" if entry["battery"] else "RTDB Account",
                f"{otp_cnt} OTP · {len(entry['msgs'])} SMS" if otp_cnt > 0 else (f"{len(entry['msgs'])} SMS" if entry["msgs"] else "Live Online"),
            ]
            existing_dev = next((d for d in synced_devices if d.get("id") == dev_id), None)
            is_fav = is_device_favorited({
                "id": dev_id,
                "finderCode": finder_code,
                "phoneNumber": phone_num,
                "isFavorite": existing_dev.get("isFavorite") if existing_dev else entry["isFavorite"],
            })
            dev_obj = {
                "id": dev_id,
                "ownerId": "rtdb_sync",
                "finderCode": finder_code,
                "phoneNumber": phone_num,
                "label": " · ".join(lbl_parts)[:64],
                "status": "online",
                "isFavorite": is_fav,
                "liveSmsActive": True,
                "lastSmsAt": latest_m["dateTime"] if latest_m else "No SMS yet",
                "lastSmsPreview": latest_m["body"][:200] if latest_m else "",
                "smsCount": len(entry["msgs"]),
                "webhookKey": (existing_dev or {}).get("webhookKey") or f"rtdb_{finder_code.lower()}",
            }
            built_devices.append(dev_obj)

            deduped = []
            seen_in = set()
            for m in entry["msgs"]:
                ext_id = f"rtdb_{re.sub(r'[^a-zA-Z0-9_-]', '_', m['key'])[:60]}"
                if ext_id in seen_in:
                    continue
                seen_in.add(ext_id)
                deduped.append({
                    "id": ext_id,
                    "ownerId": "rtdb_sync",
                    "deviceId": dev_id,
                    "finderCode": finder_code,
                    "phoneNumber": phone_num,
                    "sender": m["sender"],
                    "body": m["body"],
                    "otpCode": extract_otp_code(m["body"]),
                    "receivedAtLabel": m["dateTime"],
                    "forwardedToTelegram": False,
                })
                if len(deduped) >= 60:
                    break
            msgs_by_dev[dev_id] = deduped

            for m in entry["msgs"][:60]:
                already = m["key"] in seen_rtdb_keys
                seen_rtdb_keys.add(m["key"])
                if not already and rtdb_initial_bootstrapped:
                    new_sms_items.append({
                        "device": dev_obj,
                        "sender": m["sender"],
                        "body": m["body"],
                        "externalId": f"rtdb_{re.sub(r'[^a-zA-Z0-9_-]', '_', m['key'])[:60]}",
                    })

        for gd in generic_devices:
            if len(gd["phoneNumber"]) < 6:
                continue
            phone_digits = re.sub(r"\D", "", gd["phoneNumber"])[:20]
            dev_id = f"rtdb_{host_slug}{phone_digits}"
            if not any(d["id"] == dev_id or d["finderCode"] == gd["finderCode"] for d in built_devices):
                built_devices.append({
                    "id": dev_id,
                    "ownerId": "rtdb_sync",
                    "finderCode": gd["finderCode"],
                    "phoneNumber": gd["phoneNumber"],
                    "label": gd["label"],
                    "status": "online",
                    "isFavorite": is_device_favorited({"id": dev_id, "finderCode": gd["finderCode"], "phoneNumber": gd["phoneNumber"], "isFavorite": False}),
                    "liveSmsActive": True,
                    "lastSmsAt": "Synced from RTDB",
                    "lastSmsPreview": "",
                    "smsCount": 0,
                    "webhookKey": f"rtdb_{gd['finderCode'].lower()}",
                })

        for item in generic_sms:
            if item["key"] in seen_rtdb_keys:
                continue
            seen_rtdb_keys.add(item["key"])
            matched = next(
                (
                    d for d in built_devices
                    if (item["finderCode"] and d["finderCode"].upper() == item["finderCode"])
                    or (item["phoneNumber"] and re.sub(r"\D", "", d["phoneNumber"]) == re.sub(r"\D", "", item["phoneNumber"]))
                ),
                None,
            )
            if matched and rtdb_initial_bootstrapped:
                new_sms_items.append({
                    "device": matched,
                    "sender": item["sender"],
                    "body": item["body"],
                    "externalId": f"rtdb_{re.sub(r'[^a-zA-Z0-9_-]', '_', item['key'])[:60]}",
                })

        return {"ok": True, "url": base, "devices": built_devices, "msgs": msgs_by_dev, "new_sms": new_sms_items}
    except Exception as exc:
        return {"ok": False, "url": base, "error": str(exc), "devices": [], "msgs": {}, "new_sms": []}


sync_rtdb_lock = threading.Lock()


def sync_from_rtdb():
    global synced_devices, rtdb_items_count, rtdb_per_link_counts
    global rtdb_last_error, rtdb_last_sync_at, rtdb_initial_bootstrapped, last_rtdb_sync_ms

    if not sync_rtdb_lock.acquire(blocking=False):
        return {"ok": True, "importedDevices": len(get_online_bot_devices()), "importedSms": 0}
    try:
        urls_snapshot = list(rtdb_urls)
        if not urls_snapshot:
            with state_lock:
                synced_devices = [d for d in synced_devices if not str(d.get("id", "")).startswith("rtdb_")]
                rtdb_items_count = 0
                rtdb_per_link_counts = []
                rtdb_last_error = None
                rtdb_last_sync_at = format_bot_timestamp()
            return {"ok": True, "importedDevices": 0, "importedSms": 0}

        with concurrent.futures.ThreadPoolExecutor(max_workers=min(6, len(urls_snapshot))) as pool:
            results = [fut.result() for fut in [pool.submit(fetch_single_rtdb_devices, u, idx) for idx, u in enumerate(urls_snapshot)]]

        with state_lock:
            manual_devs = [
                {**d, "isFavorite": is_device_favorited(d)}
                for d in synced_devices
                if not str(d.get("id", "")).startswith("rtdb_") and not is_device_removed_by_admin(d)
            ]

        all_rtdb_devs = []
        imported_sms = 0
        link_summaries = []
        errors = []
        pending_deliveries = []

        for r in results:
            visible = [d for d in r["devices"] if not is_device_removed_by_admin(d)]
            link_summaries.append({"url": r["url"], "count": len(visible), "error": r.get("error")})
            if not r["ok"] and r.get("error"):
                errors.append(f"{r['url']}: {r['error']}")
                continue
            all_rtdb_devs.extend(visible)
            with state_lock:
                for did, msgs in r["msgs"].items():
                    synced_messages_by_device[did] = msgs
            for item in r["new_sms"]:
                if not is_device_removed_by_admin(item["device"]):
                    pending_deliveries.append(item)

        if any(r["ok"] for r in results):
            with state_lock:
                synced_devices = manual_devs + all_rtdb_devs
                last_rtdb_sync_ms = now_ms()
                rtdb_last_sync_at = format_bot_timestamp()
                rtdb_last_error = errors[0] if errors else None
                rtdb_initial_bootstrapped = True
                rtdb_items_count = len(all_rtdb_devs)
                rtdb_per_link_counts = link_summaries

            for item in pending_deliveries:
                deliver_incoming_sms(item["device"], item["sender"], item["body"], item["externalId"])
                imported_sms += 1

            reconcile_auto_verifying_payments()
            return {"ok": True, "importedDevices": len(all_rtdb_devs), "importedSms": imported_sms}

        rtdb_per_link_counts = link_summaries
        rtdb_last_error = errors[0] if errors else "All RTDB links failed to sync."
        return {"ok": False, "error": rtdb_last_error, "importedDevices": 0, "importedSms": 0}
    finally:
        sync_rtdb_lock.release()


def format_rtdb_links_summary():
    if not rtdb_urls:
        return "No Firebase RTDB links connected right now."
    lines = []
    for idx, u in enumerate(rtdb_urls):
        stat = next((s for s in rtdb_per_link_counts if s["url"] == u), None)
        if stat:
            cnt_txt = f"⚠️ {stat['error']}" if stat.get("error") else f"🟢 {stat['count']} online"
        else:
            cnt_txt = "⏳ Syncing"
        lines.append(f"{idx + 1}. <code>{escape_html(u)}</code> ({cnt_txt})")
    return "\n".join(lines)


# ==============================================================================
# PAYMENTS & SCREENSHOT VERIFICATION
# ==============================================================================
def build_amount_25_upi_qr(chat_id="user"):
    t_now = now_ms()
    expires_at = t_now + QR_PAYMENT_WINDOW_SEC * 1000
    order_ref = f"ONC25{hex(t_now)[2:].upper()[-6:]}{secrets.token_hex(2).upper()}"
    params = urllib.parse.urlencode({
        "pa": UPI_VPA,
        "pn": UPI_PAYEE_NAME,
        "mc": "0000",
        "mode": "02",
        "purpose": "00",
        "am": "25",
        "cu": "INR",
        "tn": f"VIP {order_ref}",
    })
    upi_uri = f"upi://pay?{params}"
    png_bytes = render_qr_png_bytes(upi_uri, target_width=512, border_modules=3)
    sess = chat_sessions.get(chat_id)
    if sess is not None:
        sess["pendingQrOrderRef"] = order_ref
        sess["pendingQrGeneratedAtMs"] = t_now
        sess["pendingQrExpiresAtMs"] = expires_at
        sess["awaitingUpiUtr"] = True
    return png_bytes, order_ref, t_now, expires_at


def finalize_payment_decision(req_item, decision, note):
    if req_item.get("status") != "pending":
        return
    req_item["status"] = decision
    req_item["verificationNote"] = note
    req_item["autoVerifyUntilMs"] = None
    used_payment_refs.add(str(req_item.get("giftCardCode", "")).upper())

    cid = req_item["chatId"]
    if decision == "approved":
        days = int(req_item.get("durationDays") or 7)
        grant_rec = {
            "id": f"grant_{re.sub(r'[^a-zA-Z0-9_-]', '_', cid)}",
            "chatId": cid,
            "username": req_item.get("username") or "telegram_user",
            "planName": req_item.get("planName") or "💎 WEEKLY PREMIUM 💎",
            "daysGranted": days,
            "expiresAtMs": now_ms() + days * 86400000,
            "status": "active",
            "updatedAtMs": now_ms(),
        }
        deleted_grant_chat_ids.discard(cid)
        idx = next((i for i, g in enumerate(synced_access_grants) if g.get("chatId") == cid), -1)
        if idx >= 0:
            synced_access_grants[idx] = grant_rec
        else:
            synced_access_grants.append(grant_rec)
        save_runtime_state()
        send_telegram_message(
            cid,
            "\n".join([
                "✅ <b>PAYMENT VERIFIED &amp; APPROVED!</b>",
                "━━━━━━━━━━━━━━━━━━━━",
                f"<blockquote>🧾 <b>UTR:</b> <code>{escape_html(req_item['giftCardCode'])}</code>\n📦 <b>Plan:</b> {escape_html(req_item['planName'])}\n⏳ <b>Duration:</b> {days} days\n🔍 <b>Check:</b> {escape_html(note)}</blockquote>",
                "🚀 <i>Tap 📱 GET NUMBERS below to start!</i>",
            ]),
            get_main_keyboard(cid),
        )
        for aid in resolve_admin_chat_ids():
            if aid != cid:
                send_telegram_message(
                    aid,
                    f"✅ <b>AUTO-APPROVED QR PAYMENT</b>\n━━━━━━━━━━━━━━━━━━━━\n<blockquote>👤 @{escape_html(req_item['username'])} (<code>{escape_html(cid)}</code>)\n🧾 UTR: <code>{escape_html(req_item['giftCardCode'])}</code>\n🔍 {escape_html(note)}</blockquote>",
                    get_main_keyboard(aid),
                )
    else:
        save_runtime_state()
        send_telegram_message(
            cid,
            f"❌ <b>PAYMENT REJECTED</b>\n━━━━━━━━━━━━━━━━━━━━\n<blockquote>🧾 <b>Ref / UTR:</b> <code>{escape_html(req_item['giftCardCode'])}</code>\n⚠️ <b>Reason:</b> {escape_html(note)}</blockquote>\nPlease make a real ₹25 payment on the PhonePe QR and submit your genuine 12-digit UTR or Payment Screenshot.",
            get_main_keyboard(cid),
        )


def reconcile_auto_verifying_payments():
    t_now = now_ms()
    changed = False
    for p in list(synced_payment_requests):
        if p.get("status") != "pending":
            continue
        if p.get("paymentMethod") == "UPI_QR":
            matched = find_matching_bank_credit_sms(p.get("giftCardCode", ""), int(p.get("amountInr") or 25))
            if matched:
                used_bank_sms_ids.add(matched["id"])
                finalize_payment_decision(p, "approved", f"Auto-verified via Bank Credit SMS ({matched['sender']}) & UTR match")
                changed = True
                continue
            if p.get("autoVerifyUntilMs") and t_now >= int(p["autoVerifyUntilMs"]):
                p["autoVerifyUntilMs"] = None
                changed = True
    if changed:
        save_runtime_state()


def notify_admin_with_screenshot(photo_bytes, caption, reply_markup=None, fallback_file_id=None):
    for aid in resolve_admin_chat_ids():
        if photo_bytes:
            send_telegram_photo_bytes(aid, photo_bytes, caption, reply_markup, f"payment_proof_{now_ms()}.jpg")
        elif fallback_file_id:
            payload = {"chat_id": aid, "photo": fallback_file_id, "caption": caption, "parse_mode": "HTML"}
            if reply_markup:
                payload["reply_markup"] = reply_markup
            res = call_telegram_api("sendPhoto", payload)
            if not res.get("ok"):
                send_telegram_message(aid, caption, reply_markup)
        else:
            send_telegram_message(aid, caption, reply_markup)


def process_qr_payment_submission(chat_id, username, raw_ref, photo_bytes=None, photo_file_id=None):
    has_photo = bool(photo_bytes or photo_file_id)
    img_hash = hashlib.sha256(photo_bytes).hexdigest() if photo_bytes else ""

    def admin_review_markup(pay_id):
        return {
            "inline_keyboard": [
                [
                    {"text": "✅ APPROVE (7d)", "callback_data": f"APPROVE_PAY:{pay_id}"},
                    {"text": "♾️ LIFETIME", "callback_data": f"APPROVE_PAY_LIFE:{pay_id}"},
                ],
                [{"text": "❌ REJECT", "callback_data": f"REJECT_PAY:{pay_id}"}],
            ]
        }

    if img_hash and img_hash in used_screenshot_hashes:
        reason = "Duplicate / already-used payment screenshot rejected automatically."
        req_item = {
            "id": f"pay_{now_ms()}_{secrets.token_hex(2)}",
            "chatId": chat_id,
            "username": username,
            "planName": "💎 WEEKLY PREMIUM 💎",
            "amountInr": 25,
            "durationDays": 7,
            "paymentMethod": "UPI_QR",
            "giftCardCode": f"DUP_IMG_{img_hash[:8]}",
            "status": "rejected",
            "verificationNote": reason,
        }
        synced_payment_requests.insert(0, req_item)
        save_runtime_state()
        send_telegram_message(chat_id, f"❌ <b>DUPLICATE SCREENSHOT</b>\n───────────────────\n⚠️ {escape_html(reason)}", get_main_keyboard(chat_id))
        return

    ok_utr, norm_utr, utr_reason = validate_qr_utr_format(raw_ref)
    if not ok_utr:
        if has_photo:
            short_tag = (img_hash or secrets.token_hex(4))[:8].upper()
            pending_code = f"SS_{short_tag}"
            req_item = {
                "id": f"pay_{now_ms()}_{secrets.token_hex(2)}",
                "chatId": chat_id,
                "username": username,
                "planName": "💎 WEEKLY PREMIUM 💎",
                "amountInr": 25,
                "durationDays": 7,
                "paymentMethod": "UPI_QR",
                "giftCardCode": pending_code,
                "status": "pending",
                "verificationNote": "Payment Screenshot received · Forwarded to Admin",
                "autoVerifyUntilMs": now_ms() + QR_PAYMENT_WINDOW_SEC * 1000,
            }
            if img_hash:
                used_screenshot_hashes.add(img_hash)
            synced_payment_requests.insert(0, req_item)
            save_runtime_state()
            notify_admin_with_screenshot(
                photo_bytes,
                "\n".join([
                    "📸 <b>NEW ₹25 PAYMENT SCREENSHOT RECEIVED</b>",
                    "━━━━━━━━━━━━━━━━━━━━",
                    f"<blockquote>👤 <b>User:</b> @{escape_html(username)} (<code>{escape_html(chat_id)}</code>)\n📦 <b>Plan:</b> 💎 WEEKLY PREMIUM (₹25 · 7 days)\n🆔 <b>Ref:</b> <code>{escape_html(pending_code)}</code></blockquote>",
                    "👇 <i>Screenshot check karke 1-Tap Approve ya Reject karein:</i>",
                ]),
                admin_review_markup(req_item["id"]),
                photo_file_id,
            )
            send_telegram_message(
                chat_id,
                "\n".join([
                    "📸 <b>PAYMENT SCREENSHOT SENT TO ADMIN!</b>",
                    "━━━━━━━━━━━━━━━━━━━━",
                    f"<blockquote>🆔 <b>Ref ID:</b> <code>{escape_html(pending_code)}</code>\n📦 <b>Plan:</b> 💎 WEEKLY PREMIUM (₹25 · 7 days)\n⏳ <b>Status:</b> Admin Verification Pending</blockquote>",
                    "✅ Aapka payment screenshot <b>Admin</b> ko dikh gaya hai — jaise hi Admin confirm karenge, aapka access chalu ho jayega!",
                ]),
                get_main_keyboard(chat_id),
            )
            return

        req_item = {
            "id": f"pay_{now_ms()}_{secrets.token_hex(2)}",
            "chatId": chat_id,
            "username": username,
            "planName": "💎 WEEKLY PREMIUM 💎",
            "amountInr": 25,
            "durationDays": 7,
            "paymentMethod": "UPI_QR",
            "giftCardCode": (norm_utr or str(raw_ref).strip() or "INVALID")[:64],
            "status": "rejected",
            "verificationNote": utr_reason,
        }
        synced_payment_requests.insert(0, req_item)
        save_runtime_state()
        send_telegram_message(
            chat_id,
            f"❌ <b>INVALID PAYMENT UTR</b>\n───────────────────\n🧾 Submitted: <code>{escape_html(req_item['giftCardCode'])}</code>\n⚠️ {escape_html(utr_reason)}\n\n📸 Apna <b>Payment Screenshot</b> bhejein ya sahi 12-digit UTR daalein.",
            get_main_keyboard(chat_id),
        )
        return

    if norm_utr in used_payment_refs or any(p.get("giftCardCode", "").upper() == norm_utr for p in synced_payment_requests):
        send_telegram_message(
            chat_id,
            f"❌ <b>DUPLICATE UTR REJECTED</b>\n───────────────────\n🧾 UTR: <code>{escape_html(norm_utr)}</code>\n⚠️ Ye UTR pehle hi use ho chuka hai.",
            get_main_keyboard(chat_id),
        )
        return

    matched_bank = find_matching_bank_credit_sms(norm_utr, 25)
    if matched_bank:
        used_bank_sms_ids.add(matched_bank["id"])
        if img_hash:
            used_screenshot_hashes.add(img_hash)
        used_payment_refs.add(norm_utr)
        req_item = {
            "id": f"pay_{now_ms()}_{secrets.token_hex(2)}",
            "chatId": chat_id,
            "username": username,
            "planName": "💎 WEEKLY PREMIUM 💎",
            "amountInr": 25,
            "durationDays": 7,
            "paymentMethod": "UPI_QR",
            "giftCardCode": norm_utr,
            "status": "pending",
        }
        synced_payment_requests.insert(0, req_item)
        finalize_payment_decision(req_item, "approved", f"Auto-verified via live Bank Credit SMS ({matched_bank['sender']}) & UTR {norm_utr}")
        return

    req_item = {
        "id": f"pay_{now_ms()}_{secrets.token_hex(2)}",
        "chatId": chat_id,
        "username": username,
        "planName": "💎 WEEKLY PREMIUM 💎",
        "amountInr": 25,
        "durationDays": 7,
        "paymentMethod": "UPI_QR",
        "giftCardCode": norm_utr,
        "status": "pending",
        "verificationNote": "Screenshot & UTR sent to Admin" if has_photo else "Waiting for Payment Screenshot / Admin confirm",
        "autoVerifyUntilMs": now_ms() + QR_PAYMENT_WINDOW_SEC * 1000,
    }
    if img_hash:
        used_screenshot_hashes.add(img_hash)
    used_payment_refs.add(norm_utr)
    synced_payment_requests.insert(0, req_item)
    save_runtime_state()

    hdr = "📸 <b>NEW ₹25 PAYMENT SCREENSHOT + UTR</b>" if has_photo else "🔔 <b>NEW ₹25 UPI QR PAYMENT (UTR)</b>"
    notify_admin_with_screenshot(
        photo_bytes,
        "\n".join([
            hdr,
            "━━━━━━━━━━━━━━━━━━━━",
            f"<blockquote>👤 <b>User:</b> @{escape_html(username)} (<code>{escape_html(chat_id)}</code>)\n📦 <b>Plan:</b> 💎 WEEKLY PREMIUM (₹25 · 7 days)\n🧾 <b>UTR:</b> <code>{escape_html(norm_utr)}</code></blockquote>",
            "👇 <i>Tap below to Approve or Reject:</i>",
        ]),
        admin_review_markup(req_item["id"]),
        photo_file_id,
    )
    send_telegram_message(
        chat_id,
        "\n".join([
            "📸 <b>SCREENSHOT &amp; UTR SENT TO ADMIN!</b>" if has_photo else "⏳ <b>UTR MIL GAYA — VERIFICATION PENDING!</b>",
            "━━━━━━━━━━━━━━━━━━━━",
            f"<blockquote>🧾 <b>UTR:</b> <code>{escape_html(norm_utr)}</code>\n📦 <b>Plan:</b> 💎 WEEKLY PREMIUM (₹25 · 7 days)\n⏳ <b>Status:</b> Admin Verification Pending</blockquote>",
            "✅ Aapka payment screenshot aur UTR <b>Admin</b> ko bhej diya gaya hai! Verify hote hi access chalu ho jayega." if has_photo else "⚡ Ab apna <b>Payment Screenshot</b> bhi chat me bhej dein taaki Admin turant dekh kar access chalu kar sakein!",
        ]),
        get_payment_keyboard(),
    )


# ==============================================================================
# ADMIN & LIST PAGINATION HELPERS
# ==============================================================================
def build_rtdb_remove_keyboard(page=0):
    page_size = 25
    total_pages = max(1, (len(rtdb_urls) + page_size - 1) // page_size)
    safe_page = max(0, min(page, total_pages - 1))
    start = safe_page * page_size
    rows = []
    for offset, u in enumerate(rtdb_urls[start:start + page_size]):
        host = re.sub(r"^https?://", "", u, flags=re.I).split("/")[0]
        rows.append([{"text": f"❌ Remove #{start + offset + 1}: {host}", "callback_data": f"RM_RTDB:{rtdb_url_hash(u)}"}])
    if total_pages > 1:
        nav = []
        if safe_page > 0:
            nav.append({"text": "⬅️ Prev Links", "callback_data": f"RM_RTDB_PAGE:{safe_page - 1}"})
        if safe_page + 1 < total_pages:
            nav.append({"text": "➡️ Next Links", "callback_data": f"RM_RTDB_PAGE:{safe_page + 1}"})
        if nav:
            rows.append(nav)
    return {"inline_keyboard": rows}


def build_online_remove_keyboard(page=0):
    online = get_online_bot_devices()
    page_size = 10
    total_pages = max(1, (len(online) + page_size - 1) // page_size)
    safe_page = max(0, min(page, total_pages - 1))
    start = safe_page * page_size
    rows = [
        [{"text": f"🗑️ #{start + idx + 1}: {d['phoneNumber']} · {d['smsCount']} SMS", "callback_data": f"RM_DEV:{d['id']}"}]
        for idx, d in enumerate(online[start:start + page_size])
    ]
    if total_pages > 1:
        nav = []
        if safe_page > 0:
            nav.append({"text": "⬅️ Prev", "callback_data": f"RM_DEV_PAGE:{safe_page - 1}"})
        nav.append({"text": f"📄 {safe_page + 1}/{total_pages} ({len(online)})", "callback_data": f"RM_DEV_PAGE:{safe_page}"})
        if safe_page + 1 < total_pages:
            nav.append({"text": "Next ➡️", "callback_data": f"RM_DEV_PAGE:{safe_page + 1}"})
        rows.append(nav)
    if removed_device_keys:
        rows.append([{"text": f"♻️ RESTORE REMOVED ({len(removed_device_keys)})", "callback_data": "RESTORE_REMOVED_DEVS"}])
    return {"inline_keyboard": rows}


def send_online_numbers_page(chat_id, page=0, title="📱 ALL ONLINE NUMBERS", fallback_kb=None):
    sess = chat_sessions.get(chat_id)
    if not is_authorized_admin_identity(chat_id, (sess or {}).get("username", ""), sess):
        send_telegram_message(chat_id, "📱 OTP number lene ke liye <b>📱 GET NUMBERS</b> tap karein.", get_main_keyboard(chat_id))
        return
    if not get_online_bot_devices() and rtdb_urls:
        sync_from_rtdb()
    online = get_online_bot_devices()
    if not online:
        send_telegram_message(chat_id, "⚠️ No online numbers available right now.", fallback_kb or get_admin_keyboard())
        return
    page_size = 10
    total_pages = max(1, (len(online) + page_size - 1) // page_size)
    safe_page = max(0, min(page, total_pages - 1))
    start = safe_page * page_size
    items = online[start:start + page_size]
    lines = "\n".join(
        f"{start + i + 1}. 🟢 <code>{escape_html(d['phoneNumber'])}</code> (<code>{escape_html(d['finderCode'])}</code>){' ⭐' if d.get('isFavorite') else ''} · {d['smsCount']} SMS"
        for i, d in enumerate(items)
    )
    inline_rows = [
        [
            {"text": f"🟢 {d['phoneNumber']} · {d['smsCount']} SMS", "callback_data": f"CONNECT_ID:{d['id']}"},
            {"text": "📋 COPY", "copy_text": {"text": d["phoneNumber"]}},
            {"text": "🗑️", "callback_data": f"RM_DEV:{d['id']}"},
        ]
        for d in items
    ]
    if total_pages > 1:
        nav = []
        if safe_page > 0:
            nav.append({"text": "⬅️ PREV", "callback_data": f"NUM_PAGE:{safe_page - 1}"})
        nav.append({"text": f"📄 {safe_page + 1}/{total_pages} ({len(online)})", "callback_data": f"NUM_PAGE:{safe_page}"})
        if safe_page + 1 < total_pages:
            nav.append({"text": "NEXT ➡️", "callback_data": f"NUM_PAGE:{safe_page + 1}"})
        inline_rows.append(nav)
    inline_rows.append([{"text": "🔄 REFRESH LIST", "callback_data": f"NUM_PAGE:{safe_page}"}])
    send_telegram_message(
        chat_id,
        "\n".join([
            f"📱 <b>{escape_html(title.lstrip('📱').strip())}</b>  ·  🟢 <b>{len(online)}</b>",
            "━━━━━━━━━━━━━━━━━━━━",
            f"<blockquote>{lines}</blockquote>",
            "<i>Admin Only: Tap number to connect, 📋 COPY, or 🗑️ Remove:</i>",
        ]),
        {"inline_keyboard": inline_rows},
    )


def send_bot_users_page(chat_id, page=0):
    all_users = sorted(
        chat_sessions.values(),
        key=lambda u: u.get("lastSeenAtMs") or u.get("joinedAtMs") or 0,
        reverse=True,
    )
    if not all_users:
        send_telegram_message(chat_id, "👥 <b>JOINED BOT USERS (0)</b>\n━━━━━━━━━━━━━━━━━━━━\n<blockquote>📭 Abhi tak kisi user ne bot start nahi kiya hai.</blockquote>", get_admin_keyboard())
        return
    t_now = now_ms()
    ch_joined = sum(1 for u in all_users if u.get("hasJoinedChannel"))
    with_handle = sum(1 for u in all_users if u.get("tgHandle"))
    active_vip = sum(1 for u in all_users if get_active_grant_for_chat(u["chatId"]))
    page_size = 8
    total_pages = max(1, (len(all_users) + page_size - 1) // page_size)
    safe_page = max(0, min(page, total_pages - 1))
    start = safe_page * page_size
    page_users = all_users[start:start + page_size]
    blocks = []
    inline_kb = []
    for off, u in enumerate(page_users):
        idx = start + off + 1
        handle = (u.get("tgHandle") or "").lstrip("@").strip()
        disp = (u.get("displayName") or "").strip()
        if disp and handle and disp.lower() != handle.lower():
            title = f"<b>{escape_html(disp)}</b> (@{escape_html(handle)})"
        elif handle:
            title = f"@{escape_html(handle)}"
        elif disp:
            title = f"<b>{escape_html(disp)}</b> <i>(no @username)</i>"
        elif u.get("username") and u["username"] != "telegram_user":
            title = f"@{escape_html(u['username'])}"
        else:
            title = "<i>Unknown User</i>"
        g = get_active_grant_for_chat(u["chatId"])
        if not g:
            acc = "🔒 Free"
        elif g.get("planName") == "ADMIN":
            acc = "👑 Admin"
        elif is_lifetime_grant(g):
            acc = "♾️ Lifetime"
        else:
            dleft = max(1, (int(g["expiresAtMs"]) - t_now + 86399999) // 86400000)
            acc = f"✅ {dleft}d left"
        ch_badge = "📢✅" if u.get("hasJoinedChannel") else "📢❌"
        j_lbl = format_bot_timestamp(u["joinedAtMs"]) if u.get("joinedAtMs") else "Saved"
        s_lbl = format_bot_timestamp(u["lastSeenAtMs"]) if u.get("lastSeenAtMs") else "Recent"
        blocks.append(f"<blockquote><b>#{idx}.</b> {title}\n🆔 <code>{escape_html(u['chatId'])}</code>  •  {ch_badge}  •  {acc}\n🕒 Joined: <i>{escape_html(j_lbl)}</i>\n👁️ Active: <i>{escape_html(s_lbl)}</i></blockquote>")
        if not (g and (g.get("planName") == "ADMIN" or is_lifetime_grant(g))):
            tag = f"@{handle[:14]}" if handle else u["chatId"]
            inline_kb.append([
                {"text": f"➕ +7d ({tag})", "callback_data": f"ADD_MEMBER_APPLY:{u['chatId']}:7"},
                {"text": "♾️ Lifetime", "callback_data": f"ADD_MEMBER_APPLY:{u['chatId']}:3650"},
            ])
    if total_pages > 1:
        nav = []
        if safe_page > 0:
            nav.append({"text": "⬅️ PREV", "callback_data": f"BOT_USERS_PAGE:{safe_page - 1}"})
        nav.append({"text": f"📄 {safe_page + 1}/{total_pages} ({len(all_users)})", "callback_data": f"BOT_USERS_PAGE:{safe_page}"})
        if safe_page + 1 < total_pages:
            nav.append({"text": "NEXT ➡️", "callback_data": f"BOT_USERS_PAGE:{safe_page + 1}"})
        inline_kb.append(nav)
    inline_kb.append([{"text": "🔄 REFRESH USERS", "callback_data": f"BOT_USERS_PAGE:{safe_page}"}])
    send_telegram_message(
        chat_id,
        "\n".join([
            f"👥 <b>BOT JOINED USERS ({len(all_users)})</b>",
            "━━━━━━━━━━━━━━━━━━━━",
            f"<blockquote>🤖 <b>Total Joined:</b> <b>{len(all_users)}</b>  •  🏷️ <b>Usernames:</b> <b>{with_handle}</b>\n📢 <b>@bhai3131 Joined:</b> <b>{ch_joined}</b>  •  💎 <b>Paid/VIP:</b> <b>{active_vip}</b></blockquote>",
            "",
            "\n".join(blocks),
            "",
            "<i>Tap ID to copy • Tap buttons below to grant instant access 👇</i>",
        ]),
        {"inline_keyboard": inline_kb},
    )


# ==============================================================================
# MAIN TELEGRAM UPDATE HANDLER
# ==============================================================================
def handle_telegram_update(update):
    global updates_processed, admin_chat_id, default_telegram_chat_id
    global rtdb_user_modified, rtdb_initial_bootstrapped, synced_access_grants
    updates_processed += 1

    msg = update.get("message")
    cb = update.get("callback_query")

    chat_id = ""
    raw_handle = ""
    full_name = ""
    username = ""
    text = ""
    sender_user_id = None
    shared_contact = None
    incoming_photo_file_id = ""
    callback_msg_id = None

    if msg and isinstance(msg.get("chat"), dict):
        chat_id = str(msg["chat"]["id"])
        frm = msg.get("from") or {}
        sender_user_id = frm.get("id")
        raw_handle = str(frm.get("username") or msg["chat"].get("username") or "").lstrip("@").strip()[:64]
        full_name = " ".join(p for p in [frm.get("first_name") or msg["chat"].get("first_name") or "", frm.get("last_name") or msg["chat"].get("last_name") or ""] if p).strip()[:64]
        username = raw_handle or full_name or "telegram_user"
        text = str(msg.get("text") or msg.get("caption") or "").strip()
        shared_contact = msg.get("contact")
        photos = msg.get("photo")
        doc = msg.get("document")
        if isinstance(photos, list) and photos:
            incoming_photo_file_id = photos[-1].get("file_id", "")
        elif isinstance(doc, dict) and doc.get("file_id") and str(doc.get("mime_type", "")).startswith("image/"):
            incoming_photo_file_id = doc["file_id"]
    elif cb and cb.get("data") and isinstance(cb.get("message"), dict):
        cb_msg = cb["message"]
        chat_id = str(cb_msg["chat"]["id"])
        frm = cb.get("from") or {}
        sender_user_id = frm.get("id")
        callback_msg_id = cb_msg.get("message_id")
        raw_handle = str(frm.get("username") or cb_msg["chat"].get("username") or "").lstrip("@").strip()[:64]
        full_name = " ".join(p for p in [frm.get("first_name") or cb_msg["chat"].get("first_name") or "", frm.get("last_name") or cb_msg["chat"].get("last_name") or ""] if p).strip()[:64]
        username = raw_handle or full_name or "telegram_user"
        text = str(cb["data"]).strip()
        toast_callback(cb.get("id"))
    else:
        return

    t_now = now_ms()
    with state_lock:
        sess = chat_sessions.get(chat_id)
        if not sess:
            sess = {
                "chatId": chat_id,
                "username": username,
                "tgHandle": raw_handle or None,
                "displayName": full_name or None,
                "joinedAtMs": t_now,
                "lastSeenAtMs": t_now,
                "interactionCount": 1,
                "activeDeviceId": "",
                "activeFinderCode": "",
                "activePhoneNumber": "",
                "activePulledByGetNumber": False,
                "seenNumberIds": [],
                "menuState": "main",
                "hasJoinedChannel": False,
                "channelVerifiedAtMs": 0,
            }
            chat_sessions[chat_id] = sess
            save_runtime_state()
        else:
            if not sess.get("joinedAtMs"):
                sess["joinedAtMs"] = t_now
            sess["lastSeenAtMs"] = t_now
            sess["interactionCount"] = int(sess.get("interactionCount") or 0) + 1
            changed_id = False
            if sess.get("username") != username:
                sess["username"] = username
                changed_id = True
            if raw_handle and sess.get("tgHandle") != raw_handle:
                sess["tgHandle"] = raw_handle
                changed_id = True
            if full_name and sess.get("displayName") != full_name:
                sess["displayName"] = full_name
                changed_id = True
            if changed_id:
                save_runtime_state()

    if is_authorized_admin_identity(chat_id, username, sess):
        if admin_chat_id != chat_id or not default_telegram_chat_id:
            admin_chat_id = chat_id
            if not default_telegram_chat_id:
                default_telegram_chat_id = chat_id
            save_runtime_state()

    if isinstance(shared_contact, dict) and shared_contact.get("phone_number"):
        clean_digits = re.sub(r"\D", "", shared_contact["phone_number"])
        is_own = not shared_contact.get("user_id") or not sender_user_id or shared_contact["user_id"] == sender_user_id
        if is_own and clean_digits == ADMIN_TELEGRAM_PHONE:
            sess["verifiedAdminPhone"] = ADMIN_TELEGRAM_PHONE
            sess["awaitingAdminPassword"] = True
            admin_chat_id = chat_id
            if not default_telegram_chat_id:
                default_telegram_chat_id = chat_id
            save_runtime_state()
            send_telegram_message(chat_id, "✅ Phone <code>+27787045561</code> verified!\n🔐 Now enter Admin Password:", get_main_keyboard(chat_id))
        else:
            send_telegram_message(chat_id, "⛔ Access Denied! Sirf @King3131bhai (+27787045561) hi Admin login kar sakta hai. Or koi nahi.", get_main_keyboard(chat_id))
        return

    if not text and not incoming_photo_file_id:
        return

    norm = text.upper()
    is_admin_id = is_authorized_admin_identity(chat_id, username, sess)

    def send_main_welcome():
        grant = get_active_grant_for_chat(chat_id)
        if not grant:
            access_line = "🔒 <b>VIP Status:</b> Not Active <i>(₹25 · 7 Days)</i>"
        elif grant.get("planName") == "ADMIN":
            access_line = "👑 <b>VIP Status:</b> Admin Unlimited"
        elif is_lifetime_grant(grant):
            access_line = "♾️ <b>VIP Status:</b> Lifetime Unlimited"
        else:
            dleft = max(1, (int(grant["expiresAtMs"]) - now_ms() + 86399999) // 86400000)
            access_line = f"✅ <b>VIP Status:</b> Active ({dleft}d left)"

        online_cnt = len(get_online_bot_devices())
        greet = escape_html((sess.get("displayName") or full_name or username or "Friend").split()[0])
        stats_block = (
            f"{access_line}\n🟢 <b>Online Numbers (Admin):</b> <b>{online_cnt}</b>  •  ⚡ <b>Speed:</b> ~1–2s Live"
            if is_admin_id
            else f"{access_line}\n⚡ <b>Speed:</b> ~1–2s Live OTP Delivery\n🛡️ <b>Privacy:</b> Private 1-to-1 SIM Allocation"
        )
        welcome = "\n".join([
            "⚡ <b>BHAI3131  ·  INSTANT OTP HUB</b>",
            f"👋 <i>Welcome, <b>{greet}</b>!</i>",
            "━━━━━━━━━━━━━━━━━━━━",
            f"<blockquote>{stats_block}</blockquote>",
            "<b>✨ 3 Easy Steps:</b>",
            "1️⃣ Niche <b>📱 GET NUMBERS</b> ya <b>🔍 FIND NUMBER</b> tap karein",
            "2️⃣ Number <b>1-Tap Copy</b> karke app me daalein",
            "3️⃣ Live OTP yahi chat me automatic aayega!",
            "",
            "👇 <i>Quick action ya niche menu chunein:</i>",
        ])
        send_telegram_message(chat_id, welcome, get_main_keyboard(chat_id))
        quick_inline = (
            {"inline_keyboard": [[{"text": "📱 GET NUMBER NOW", "callback_data": "NEXT_ONLINE"}]]}
            if grant
            else {"inline_keyboard": [[{"text": "💳 ACTIVATE ₹25 VIP PASS (7 DAYS)", "callback_data": "UPI_QR_NEW"}]]}
        )
        send_telegram_message(chat_id, "🚀 <b>QUICK START</b>  ·  <i>1-Tap Shortcut</i>", quick_inline)

    if norm == "VERIFY_CHANNEL":
        chk = check_channel_membership(chat_id, sender_user_id, True)
        if chk.get("checked") and not chk.get("joined"):
            sess["hasJoinedChannel"] = False
            sess["channelVerifiedAtMs"] = 0
            save_runtime_state()
            send_force_join_prompt(chat_id, True)
            return
        if not chk.get("checked"):
            elapsed = now_ms() - int(sess.get("channelPromptShownAtMs") or 0) if sess.get("channelPromptShownAtMs") else 0
            if not (chk.get("inaccessible") and (elapsed >= 1500 or is_admin_id)):
                sess["hasJoinedChannel"] = False
                sess["channelVerifiedAtMs"] = 0
                save_runtime_state()
                send_force_join_prompt(chat_id, True, chk.get("error"))
                return
        sess["hasJoinedChannel"] = True
        sess["channelVerifiedAtMs"] = now_ms()
        sess["menuState"] = "main"
        save_runtime_state()
        send_telegram_message(chat_id, f"✅ <b>CHANNEL VERIFIED!</b>  ({REQUIRED_CHANNEL_USERNAME})\n✨ Welcome to <b>BHAI3131 OTP HUB</b>.", get_main_keyboard(chat_id))
        send_main_welcome()
        return

    is_admin_cmd = is_admin_id and (
        norm == "/ADMIN"
        or norm.startswith("/ADMIN ")
        or norm in ("⚙️ ADMIN PANEL", "ADMIN PANEL", "RESTORE_REMOVED_DEVS")
        or bool(sess.get("awaitingAdminPassword"))
        or bool(sess.get("isAdminVerified"))
        or any(norm.startswith(p) for p in ("APPROVE_PAY:", "APPROVE_PAY_LIFE:", "REJECT_PAY:", "RM_DEV:", "RM_DEV_PAGE:"))
    )

    if norm in ("/START", "🏠 HOME MENU", "HOME MENU", "↩️ BACK", "⬅️ BACK", "BACK"):
        for flag in (
            "activePulledByGetNumber", "awaitingGiftCard", "awaitingUpiUtr", "awaitingAdminPassword",
            "awaitingGrantInput", "awaitingAddMemberId", "awaitingLifetimeInput", "awaitingRevokeInput",
            "awaitingRtdbLink", "awaitingRemoveRtdb", "awaitingAddNumber", "awaitingRemoveNumber", "awaitingFavoriteInput",
        ):
            sess[flag] = False
        sess["menuState"] = "main"
        sess["activeDeviceId"] = ""
        sess["activeFinderCode"] = ""
        sess["activePhoneNumber"] = ""

        chk = check_channel_membership(chat_id, sender_user_id, True)
        if chk.get("checked") and chk.get("joined"):
            sess["hasJoinedChannel"] = True
            sess["channelVerifiedAtMs"] = now_ms()
            save_runtime_state()
            send_main_welcome()
            return
        if chk.get("inaccessible") and (sess.get("hasJoinedChannel") or is_admin_id):
            sess["hasJoinedChannel"] = True
            sess["channelVerifiedAtMs"] = now_ms()
            save_runtime_state()
            send_main_welcome()
            return
        sess["hasJoinedChannel"] = False
        sess["channelVerifiedAtMs"] = 0
        save_runtime_state()
        send_force_join_prompt(chat_id, False, chk.get("error"))
        return

    if not is_admin_cmd:
        chk = check_channel_membership(chat_id, sender_user_id, False)
        if chk.get("checked") and not chk.get("joined"):
            sess["hasJoinedChannel"] = False
            sess["channelVerifiedAtMs"] = 0
            sess["awaitingGiftCard"] = False
            sess["awaitingUpiUtr"] = False
            sess["awaitingFavoriteInput"] = False
            save_runtime_state()
            send_force_join_prompt(chat_id, True)
            return
        if not chk.get("checked"):
            if not (chk.get("inaccessible") and sess.get("hasJoinedChannel")):
                sess["hasJoinedChannel"] = False
                sess["channelVerifiedAtMs"] = 0
                save_runtime_state()
                send_force_join_prompt(chat_id, True, chk.get("error"))
                return
            sess["channelVerifiedAtMs"] = now_ms()
        else:
            sess["hasJoinedChannel"] = True
            sess["channelVerifiedAtMs"] = now_ms()

    # ---------- ADMIN ENTRY ----------
    if norm == "/ADMIN" or norm.startswith("/ADMIN ") or norm in ("⚙️ ADMIN PANEL", "ADMIN PANEL"):
        for flag in (
            "awaitingGiftCard", "awaitingUpiUtr", "awaitingGrantInput", "awaitingAddMemberId",
            "awaitingLifetimeInput", "awaitingRevokeInput", "awaitingRtdbLink", "awaitingRemoveRtdb",
            "awaitingAddNumber", "awaitingRemoveNumber", "awaitingFavoriteInput",
        ):
            sess[flag] = False
        if not is_admin_id:
            sess["awaitingAdminPassword"] = False
            sess["isAdminVerified"] = False
            send_telegram_message(
                chat_id,
                "⛔ <b>SIRF ADMIN LOGIN</b>\n───────────────────\nSirf Telegram account <b>@King3131bhai</b> (+27787045561) hi Admin Panel me login kar sakta hai.\nOr koi login nahi kar sakta.",
                {"keyboard": [[{"text": "📱 VERIFY ADMIN (+27787045561)", "request_contact": True}], [{"text": "↩️ BACK"}]], "resize_keyboard": True, "one_time_keyboard": True},
            )
            return

        inline_pass = re.sub(r"^/admin\s*", "", text, flags=re.I).strip()
        active_cnt = sum(1 for g in synced_access_grants if g.get("status") == "active" and (is_lifetime_grant(g) or int(g.get("expiresAtMs") or 0) > now_ms()))
        online_cnt = len(get_online_bot_devices())
        if (inline_pass and inline_pass.lower() == ADMIN_PASSWORD.lower()) or sess.get("isAdminVerified"):
            sess["isAdminVerified"] = True
            sess["awaitingAdminPassword"] = False
            sess["menuState"] = "admin"
            admin_chat_id = chat_id
            if not default_telegram_chat_id:
                default_telegram_chat_id = chat_id
            save_runtime_state()
            send_telegram_message(
                chat_id,
                "\n".join([
                    "👑 <b>ADMIN COMMAND CENTER</b>",
                    "━━━━━━━━━━━━━━━━━━━━",
                    f"<blockquote>🆔 <b>Admin ID:</b> <code>{escape_html(chat_id)}</code>\n🤖 <b>Joined Bot Users:</b> <b>{len(chat_sessions)}</b>  •  👥 <b>Members:</b> <b>{active_cnt}</b>\n🟢 <b>Online Numbers:</b> <b>{online_cnt}</b>  •  🔗 <b>RTDBs:</b> <b>{len(rtdb_urls)}</b></blockquote>",
                    "<i>All Admin controls ready below 👇</i>",
                ]),
                get_admin_keyboard(),
            )
            return

        sess["awaitingAdminPassword"] = True
        save_runtime_state()
        send_telegram_message(chat_id, f"⚙️ <b>ADMIN PANEL LOGIN</b>\n━━━━━━━━━━━━━━━━━━━━\n<blockquote>👑 Verified: @{escape_html(username)}\n🔐 Enter Admin Password below:</blockquote>", get_main_keyboard(chat_id))
        return

    if sess.get("awaitingAdminPassword"):
        if not is_admin_id:
            sess["awaitingAdminPassword"] = False
            sess["isAdminVerified"] = False
            save_runtime_state()
            send_telegram_message(chat_id, "⛔ Sirf @King3131bhai (+27787045561) hi Admin login kar sakta hai.", get_main_keyboard(chat_id))
            return
        if text.strip().lower() == ADMIN_PASSWORD.lower():
            sess["awaitingAdminPassword"] = False
            sess["isAdminVerified"] = True
            sess["menuState"] = "admin"
            admin_chat_id = chat_id
            if not default_telegram_chat_id:
                default_telegram_chat_id = chat_id
            save_runtime_state()
            active_cnt = sum(1 for g in synced_access_grants if g.get("status") == "active" and (is_lifetime_grant(g) or int(g.get("expiresAtMs") or 0) > now_ms()))
            send_telegram_message(
                chat_id,
                "\n".join([
                    "👑 <b>ADMIN PANEL UNLOCKED</b>",
                    "━━━━━━━━━━━━━━━━━━━━",
                    f"<blockquote>✦ <b>Admin:</b> @{escape_html(username)} (<code>{escape_html(chat_id)}</code>)\n✦ <b>Joined Bot Users:</b> 🤖 <b>{len(chat_sessions)}</b>\n✦ <b>Active Members:</b> 👥 <b>{active_cnt}</b>\n✦ <b>Online Numbers:</b> 🟢 <b>{len(get_online_bot_devices())}</b>  •  🔗 <b>RTDBs:</b> <b>{len(rtdb_urls)}</b></blockquote>",
                    "<i>Choose an Admin action below 👇</i>",
                ]),
                get_admin_keyboard(),
            )
        else:
            send_telegram_message(chat_id, "⛔ Wrong Password! Please enter correct Admin Password or tap ↩️ BACK:", get_main_keyboard(chat_id))
        return

    # ---------- ADMIN 1-TAP PAYMENT APPROVE / REJECT ----------
    if any(norm.startswith(p) for p in ("APPROVE_PAY:", "APPROVE_PAY_LIFE:", "REJECT_PAY:")):
        if not is_admin_id:
            send_telegram_message(chat_id, "⛔ Sirf @King3131bhai (+27787045561) hi payment approve ya reject kar sakta hai.", get_main_keyboard(chat_id))
            return
        is_life = norm.startswith("APPROVE_PAY_LIFE:")
        is_app = is_life or norm.startswith("APPROVE_PAY:")
        pay_id = text[17:].strip() if is_life else (text[12:].strip() if is_app else text[11:].strip())
        req_item = next((p for p in synced_payment_requests if p.get("id") == pay_id), None)
        if not req_item:
            send_telegram_message(chat_id, "⚠️ Payment request not found.", get_admin_keyboard() if sess.get("isAdminVerified") else get_main_keyboard(chat_id))
            return
        if req_item.get("status") != "pending":
            send_telegram_message(chat_id, f"ℹ️ Payment request already <b>{escape_html(str(req_item['status']).upper())}</b>.", get_admin_keyboard() if sess.get("isAdminVerified") else get_main_keyboard(chat_id))
            return
        if is_app:
            days = 3650 if is_life else int(req_item.get("durationDays") or 7)
            plan = "♾️ LIFETIME MEMBER" if is_life else req_item.get("planName", "💎 WEEKLY PREMIUM 💎")
            req_item["durationDays"] = days
            req_item["planName"] = plan
            finalize_payment_decision(req_item, "approved", "Approved as Lifetime Member by Admin" if is_life else "Manually approved by Admin")
            send_telegram_message(chat_id, f"✅ Approved @{escape_html(req_item['username'])} (<code>{escape_html(req_item['chatId'])}</code>) for {'♾️ Lifetime' if is_life else f'{days} days'}.", get_admin_keyboard() if sess.get("isAdminVerified") else get_main_keyboard(chat_id))
        else:
            finalize_payment_decision(req_item, "rejected", "Rejected by Admin")
            send_telegram_message(chat_id, f"❌ Rejected payment from @{escape_html(req_item['username'])} (<code>{escape_html(req_item['chatId'])}</code>).", get_admin_keyboard() if sess.get("isAdminVerified") else get_main_keyboard(chat_id))
        return

    # ---------- ADMIN CONTROLS ----------
    if sess.get("isAdminVerified") and is_admin_id:
        def apply_member_grant(raw_target, days_in, explicit_plan=None):
            cleaned = raw_target.strip()
            target_cid = cleaned
            resolved_user = ""
            if not re.match(r"^-?\d+$", target_cid):
                handle = cleaned.lstrip("@").lower()
                found = next((s for s in chat_sessions.values() if s.get("username", "").lstrip("@").lower() == handle), None)
                if found:
                    target_cid = found["chatId"]
                    resolved_user = found["username"]
            if not re.match(r"^-?\d+$", target_cid):
                send_telegram_message(chat_id, "⚠️ Valid Member ID bhejein (e.g. <code>5829104412</code>), ya us user ko pehle bot par <code>/start</code> bhejne ko kahein.", get_admin_keyboard())
                return
            gdays = max(1, min(3650, round(days_in) or 7))
            is_life = gdays >= 3650 or (explicit_plan and "LIFETIME" in explicit_plan.upper())
            plan = explicit_plan or ("♾️ LIFETIME MEMBER" if is_life else "💎 WEEKLY PREMIUM 💎")
            target_uname = resolved_user or (chat_sessions.get(target_cid) or {}).get("username") or "telegram_user"
            rec = {
                "id": f"grant_{re.sub(r'[^a-zA-Z0-9_-]', '_', target_cid)}",
                "chatId": target_cid,
                "username": target_uname,
                "planName": plan,
                "daysGranted": gdays,
                "expiresAtMs": now_ms() + gdays * 86400000,
                "status": "active",
                "updatedAtMs": now_ms(),
            }
            deleted_grant_chat_ids.discard(target_cid)
            idx = next((i for i, g in enumerate(synced_access_grants) if g.get("chatId") == target_cid), -1)
            if idx >= 0:
                synced_access_grants[idx] = rec
            else:
                synced_access_grants.append(rec)
            save_runtime_state()
            send_telegram_message(
                target_cid,
                f"🎉 <b>VIP ACCESS ACTIVATED!</b>\n━━━━━━━━━━━━━━━━━━━━\n<blockquote>📦 <b>Plan:</b> {escape_html(plan)}\n⏳ <b>Duration:</b> {'♾️ Lifetime Unlimited' if is_life else f'{gdays} days'}</blockquote>\n🚀 <i>Tap 📱 GET NUMBERS or 🔍 FIND NUMBER to start!</i>",
                get_main_keyboard(target_cid),
            )
            send_telegram_message(
                chat_id,
                f"✅ <b>MEMBER ADDED!</b>\n━━━━━━━━━━━━━━━━━━━━\n<blockquote>🆔 <b>Member ID:</b> <code>{escape_html(target_cid)}</code> (@{escape_html(target_uname)})\n📦 <b>Plan:</b> {escape_html(plan)}\n⏳ <b>Duration:</b> {'♾️ Lifetime' if is_life else f'{gdays} days'}</blockquote>",
                get_admin_keyboard(),
            )

        if norm == "🔒 LOGOUT ADMIN":
            sess["isAdminVerified"] = False
            sess["menuState"] = "main"
            for flag in ("awaitingGrantInput", "awaitingAddMemberId", "awaitingLifetimeInput", "awaitingRevokeInput", "awaitingRtdbLink", "awaitingRemoveRtdb", "awaitingAddNumber", "awaitingRemoveNumber"):
                sess[flag] = False
            save_runtime_state()
            send_telegram_message(chat_id, "🔒 Admin logged out.", get_main_keyboard(chat_id))
            return

        if norm in ("➕ ADD MEMBER", "ADD MEMBER"):
            for flag in ("awaitingGrantInput", "awaitingLifetimeInput", "awaitingRevokeInput", "awaitingRtdbLink", "awaitingRemoveRtdb", "awaitingAddNumber", "awaitingRemoveNumber"):
                sess[flag] = False
            sess["awaitingAddMemberId"] = True
            save_runtime_state()
            send_telegram_message(chat_id, "➕ <b>ADD MEMBER BY ID</b>\n───────────────────\nMember ki Telegram ID bhejein:\n• Sirf ID: <code>5829104412</code> (button se days chunein)\n• ID + Days: <code>5829104412 30</code>\n• ID + Lifetime: <code>5829104412 lifetime</code>", get_admin_keyboard())
            return

        if norm.startswith("ADD_MEMBER_APPLY:"):
            parts = text[17:].strip().split(":")
            tcid = (parts[0] or "").strip()
            days = max(1, min(3650, int(parts[1]) if len(parts) > 1 and parts[1].isdigit() else 7))
            sess["awaitingAddMemberId"] = False
            apply_member_grant(tcid, days)
            return

        if norm == "👥 GRANT ACCESS":
            sess["awaitingGrantInput"] = True
            send_telegram_message(chat_id, "👥 <b>GRANT USER ACCESS</b>\n───────────────────\nSend: <code>&lt;ChatID&gt; &lt;Days&gt;</code> or <code>&lt;ChatID&gt; lifetime</code>\nExample: <code>5829104412 7</code>", get_admin_keyboard())
            return

        if norm in ("♾️ LIFETIME ACCESS", "LIFETIME ACCESS"):
            sess["awaitingLifetimeInput"] = True
            send_telegram_message(chat_id, "♾️ <b>GRANT LIFETIME MEMBER ACCESS</b>\n───────────────────\nSend the user Chat ID to grant Lifetime Access:\nExample: <code>5829104412</code>", get_admin_keyboard())
            return

        if norm == "🚫 REVOKE ACCESS":
            sess["awaitingRevokeInput"] = True
            send_telegram_message(chat_id, "🚫 <b>REVOKE ACCESS</b>\n───────────────────\nSend the user Chat ID to revoke:", get_admin_keyboard())
            return

        if norm in ("🔗 ADD FIREBASE LINK", "🔗 SET FIREBASE LINK", "ADD FIREBASE LINK"):
            sess["awaitingRtdbLink"] = True
            sess["awaitingRemoveRtdb"] = False
            save_runtime_state()
            send_telegram_message(chat_id, f"🔗 <b>CONNECTED FIREBASE LINKS ({len(rtdb_urls)})</b>\n───────────────────\n{format_rtdb_links_summary()}\n───────────────────\n➕ Send 1 or multiple Firebase RTDB URLs below to add them.", get_admin_keyboard())
            return

        if norm in ("🗑️ REMOVE FIREBASE LINK", "REMOVE FIREBASE LINK"):
            sess["awaitingRemoveRtdb"] = True
            sess["awaitingRtdbLink"] = False
            if not rtdb_urls:
                sess["awaitingRemoveRtdb"] = False
                save_runtime_state()
                send_telegram_message(chat_id, "⚠️ No Firebase RTDB links connected right now.", get_admin_keyboard())
                return
            save_runtime_state()
            send_telegram_message(chat_id, f"🗑️ <b>REMOVE FIREBASE LINK ({len(rtdb_urls)})</b>\n───────────────────\n{format_rtdb_links_summary()}\n───────────────────\nTap a ❌ Remove button below OR send number/URL:", build_rtdb_remove_keyboard(0))
            return

        if norm.startswith("RM_RTDB_PAGE:"):
            pnum = max(0, int(text[13:].strip() or 0))
            send_telegram_message(chat_id, f"🗑️ <b>REMOVE FIREBASE LINK ({len(rtdb_urls)})</b>\n───────────────────\n{format_rtdb_links_summary()}", build_rtdb_remove_keyboard(pnum))
            return

        if norm.startswith("RM_RTDB:") or norm.startswith("REMOVE_RTDB:"):
            rem_idx = -1
            if norm.startswith("RM_RTDB:"):
                thash = text[8:].strip().lower()
                rem_idx = next((i for i, u in enumerate(rtdb_urls) if rtdb_url_hash(u).lower() == thash), -1)
            else:
                idx = int(text[12:].strip()) if text[12:].strip().isdigit() else -1
                if 0 <= idx < len(rtdb_urls):
                    rem_idx = idx
            if rem_idx < 0:
                send_telegram_message(chat_id, "⚠️ Firebase link already removed or not found.", get_admin_keyboard())
                return
            removed = rtdb_urls.pop(rem_idx)
            rtdb_user_modified = True
            rtdb_initial_bootstrapped = False
            seen_rtdb_keys.clear()
            save_runtime_state()
            sync_res = sync_from_rtdb()
            send_telegram_message(chat_id, f"🗑️ <b>REMOVED FIREBASE LINK</b>\n───────────────────\nRemoved: <code>{escape_html(removed)}</code>\nRemaining Links: <b>{len(rtdb_urls)}</b>\n🟢 Active Online Numbers: <b>{sync_res['importedDevices']}</b>", get_admin_keyboard())
            return

        if norm == "➕ ADD NUMBER":
            sess["awaitingAddNumber"] = True
            send_telegram_message(chat_id, "➕ <b>ADD NEW NUMBER</b>\n───────────────────\nSend: <code>&lt;PhoneNumber&gt; [Label]</code>\nExample: <code>9839017772 Jio VIP</code>", get_admin_keyboard())
            return

        if norm in ("🗑️ REMOVE NUMBER", "REMOVE NUMBER") or norm.startswith("RM_DEV_PAGE:"):
            pnum = max(0, int(text[12:].strip() or 0)) if norm.startswith("RM_DEV_PAGE:") else 0
            sess["awaitingRemoveNumber"] = True
            save_runtime_state()
            online = get_online_bot_devices()
            if not online and not removed_device_keys:
                sess["awaitingRemoveNumber"] = False
                save_runtime_state()
                send_telegram_message(chat_id, "⚠️ Abhi koi online number available nahi hai remove karne ke liye.", get_admin_keyboard())
                return
            reply_or_edit_inline_card(
                chat_id,
                callback_msg_id,
                f"🗑️ <b>REMOVE NUMBER (ADMIN ONLY)</b>  ·  🟢 <b>{len(online)}</b>\n━━━━━━━━━━━━━━━━━━━━\n<blockquote>Niche kisi bhi number par <b>🗑️</b> tap karein ya chat me phone number bhejein — bot aur RTDB sync se permanently hat jayega.</blockquote>",
                build_online_remove_keyboard(pnum),
            )
            return

        if norm.startswith("RM_DEV:"):
            tid = text[7:].strip()
            target = next((d for d in synced_devices if d.get("id") == tid or d.get("finderCode", "").upper() == tid.upper()), None)
            if not target:
                send_telegram_message(chat_id, "⚠️ Number already removed or not found.", get_admin_keyboard())
                return
            sess["awaitingRemoveNumber"] = False
            mark_device_removed_by_admin(target)
            send_telegram_message(
                chat_id,
                f"🗑️ <b>NUMBER REMOVED BY ADMIN</b>\n───────────────────\n📞 Removed: <code>{escape_html(target['phoneNumber'])}</code>\n🟢 Remaining Online Numbers: <b>{len(get_online_bot_devices())}</b>\n🔒 <i>Ye number ab users ko nahi dikhega (jab tak Restore na karein).</i>",
                {"inline_keyboard": [[{"text": "🗑️ REMOVE ANOTHER NUMBER", "callback_data": "RM_DEV_PAGE:0"}], [{"text": f"♻️ RESTORE REMOVED ({len(removed_device_keys)})", "callback_data": "RESTORE_REMOVED_DEVS"}]]},
            )
            return

        if norm == "RESTORE_REMOVED_DEVS":
            prev = len(removed_device_keys)
            removed_device_keys.clear()
            save_runtime_state()
            sync_res = sync_from_rtdb()
            send_telegram_message(chat_id, f"♻️ <b>RESTORED REMOVED NUMBERS</b>\n───────────────────\n✅ Restored filter ({prev} keys cleared).\n🟢 Online Numbers now: <b>{sync_res['importedDevices']}</b>", get_admin_keyboard())
            return

        if sess.get("awaitingRemoveNumber"):
            sess["awaitingRemoveNumber"] = False
            cdig = re.sub(r"\D", "", text)
            utxt = text.strip().upper()
            target = next((
                d for d in synced_devices
                if d.get("id") == text.strip() or d.get("finderCode", "").upper() == utxt
                or (len(cdig) >= 6 and (re.sub(r"\D", "", d.get("phoneNumber", "")) == cdig or re.sub(r"\D", "", d.get("phoneNumber", "")).endswith(cdig)))
            ), None)
            if not target:
                save_runtime_state()
                send_telegram_message(chat_id, f"⚠️ Number \"{escape_html(text)}\" nahi mila.", get_admin_keyboard())
                return
            mark_device_removed_by_admin(target)
            send_telegram_message(chat_id, f"🗑️ <b>NUMBER REMOVED BY ADMIN</b>\n───────────────────\n📞 Removed: <code>{escape_html(target['phoneNumber'])}</code>\n🟢 Remaining Online Numbers: <b>{len(get_online_bot_devices())}</b>", get_admin_keyboard())
            return

        if norm == "🔄 SYNC FIREBASE RTDB":
            sync_res = sync_from_rtdb()
            send_telegram_message(
                chat_id,
                f"✅ <b>FIREBASE RTDB SYNCED ({len(rtdb_urls)} links)</b>\n───────────────────\n{format_rtdb_links_summary()}\n───────────────────\n🟢 Online Numbers: <b>{sync_res['importedDevices']}</b>\n📩 New SMS: <b>{sync_res['importedSms']}</b>" if sync_res["ok"] else f"⚠️ RTDB Sync Error: {escape_html(sync_res.get('error', 'Unknown error'))}",
                get_admin_keyboard(),
            )
            return

        if norm in ("📱 ONLINE NUMBERS", "📱 ALL NUMBERS", "/NUMBERS", "/ONLINE"):
            send_online_numbers_page(chat_id, 0, "📱 ALL ONLINE NUMBERS", get_admin_keyboard())
            return

        if norm in ("👥 BOT USERS", "BOT USERS", "🤖 BOT USERS", "/USERS", "/BOTUSERS"):
            send_bot_users_page(chat_id, 0)
            return

        if norm.startswith("BOT_USERS_PAGE:"):
            send_bot_users_page(chat_id, max(0, int(text[15:].strip() or 0)))
            return

        if norm == "👥 ACTIVE USERS":
            t_now = now_ms()
            active = [g for g in synced_access_grants if g.get("status") == "active" and (is_lifetime_grant(g) or int(g.get("expiresAtMs") or 0) > t_now)]
            if not active:
                lines = "No active granted users yet."
            else:
                lines = "\n".join(
                    f"👤 <code>{escape_html(g['chatId'])}</code> (@{escape_html(g.get('username', 'user'))})  ·  ♾️ <b>Lifetime</b>"
                    if is_lifetime_grant(g)
                    else f"👤 <code>{escape_html(g['chatId'])}</code> (@{escape_html(g.get('username', 'user'))})  ·  ⏳ <b>{max(1, (int(g['expiresAtMs']) - t_now + 86399999) // 86400000)}d left</b>"
                    for g in active
                )
            ikb = [
                [
                    {"text": f"➕ +7d ({g['chatId']})", "callback_data": f"ADD_MEMBER_APPLY:{g['chatId']}:{min(3650, int(g.get('daysGranted') or 7) + 7)}"},
                    {"text": "♾️ Lifetime", "callback_data": f"ADD_MEMBER_APPLY:{g['chatId']}:3650"},
                ]
                for g in active[:8]
            ]
            send_telegram_message(chat_id, f"👥 <b>ACTIVE MEMBERS ({len(active)})</b>\n━━━━━━━━━━━━━━━━━━━━\n🔒 <b>Local Persistent Vault:</b> Active\n<blockquote>{lines}</blockquote>", {"inline_keyboard": ikb} if ikb else get_admin_keyboard())
            return

        if norm == "💳 PAYMENTS":
            pending = [p for p in synced_payment_requests if p.get("status") == "pending"]
            if not pending:
                send_telegram_message(chat_id, "💳 <b>PENDING PAYMENTS (0)</b>\n━━━━━━━━━━━━━━━━━━━━\n<blockquote>📭 No pending payment requests right now.</blockquote>", get_admin_keyboard())
                return
            lines = "\n".join(
                f"{idx + 1}. 👤 @{escape_html(p['username'])} (<code>{escape_html(p['chatId'])}</code>)\n   {'📱 UTR' if p.get('paymentMethod') == 'UPI_QR' else '🎁 Code'}: <code>{escape_html(p['giftCardCode'])}</code> · ₹{p.get('amountInr', 25)} ({p.get('durationDays', 7)}d)"
                for idx, p in enumerate(pending[:8])
            )
            ikb = [[{"text": f"✅ APPROVE @{p['username']} ({p.get('durationDays', 7)}d)", "callback_data": f"APPROVE_PAY:{p['id']}"}, {"text": "❌ REJECT", "callback_data": f"REJECT_PAY:{p['id']}"}] for p in pending[:8]]
            send_telegram_message(chat_id, f"💳 <b>PENDING PAYMENTS ({len(pending)})</b>\n━━━━━━━━━━━━━━━━━━━━\n<blockquote>{lines}</blockquote>", {"inline_keyboard": ikb})
            return

        if sess.get("awaitingRemoveRtdb"):
            sess["awaitingRemoveRtdb"] = False
            tr = text.strip()
            ridx = -1
            if tr.isdigit():
                num = int(tr) - 1
                if 0 <= num < len(rtdb_urls):
                    ridx = num
            else:
                nt = normalize_rtdb_url(tr).lower()
                ct = tr.rstrip("/").lower()
                ridx = next((i for i, u in enumerate(rtdb_urls) if (nt and u.lower() == nt) or u.lower() == ct or ct in u.lower()), -1)
            if ridx < 0:
                save_runtime_state()
                send_telegram_message(chat_id, "⚠️ Matching Firebase link not found.", get_admin_keyboard())
                return
            removed = rtdb_urls.pop(ridx)
            rtdb_user_modified = True
            rtdb_initial_bootstrapped = False
            seen_rtdb_keys.clear()
            save_runtime_state()
            sync_res = sync_from_rtdb()
            send_telegram_message(chat_id, f"🗑️ <b>REMOVED FIREBASE LINK</b>\n───────────────────\nRemoved: <code>{escape_html(removed)}</code>\nRemaining Links: <b>{len(rtdb_urls)}</b>\n🟢 Active Online Numbers: <b>{sync_res['importedDevices']}</b>", get_admin_keyboard())
            return

        det_urls = extract_rtdb_urls_from_text(text)
        if sess.get("awaitingRtdbLink") or norm.startswith("/SETFIREBASE ") or norm.startswith("/ADDFIR") or det_urls:
            if not det_urls:
                send_telegram_message(chat_id, "⚠️ Valid Firebase RTDB URL bhejein (e.g. <code>https://your-project-default-rtdb.firebaseio.com</code>).\nYa band karne ke liye ↩️ BACK dabayein.", get_admin_keyboard())
                return
            added = 0
            for c in det_urls:
                if c not in rtdb_urls:
                    rtdb_urls.append(c)
                    added += 1
            rtdb_user_modified = True
            rtdb_initial_bootstrapped = False
            seen_rtdb_keys.clear()
            save_runtime_state()
            sync_res = sync_from_rtdb()
            send_telegram_message(
                chat_id,
                f"{f'✅ <b>ADDED {added} FIREBASE LINK(S) · TOTAL {len(rtdb_urls)}</b>' if added else f'✅ <b>FIREBASE LINKS ALREADY CONNECTED ({len(rtdb_urls)}) · RE-SYNCED</b>'}\n───────────────────\n{format_rtdb_links_summary()}\n───────────────────\n🟢 Total Online Numbers: <b>{sync_res['importedDevices']}</b>",
                get_admin_keyboard(),
            )
            return

        if sess.get("awaitingAddNumber"):
            sess["awaitingAddNumber"] = False
            parts = text.strip().split()
            rphone = parts[0] if parts else ""
            lbl = " ".join(parts[1:]) if len(parts) > 1 else "Admin Added"
            if len(re.sub(r"\D", "", rphone)) < 6:
                send_telegram_message(chat_id, "⚠️ Invalid phone number. Format: <code>&lt;PhoneNumber&gt; [Label]</code>", get_admin_keyboard())
                return
            fcode = f"AXU-{secrets.token_hex(2).upper()}"
            new_dev = {
                "id": f"dev_{now_ms()}_{secrets.token_hex(2)}",
                "ownerId": "admin",
                "finderCode": fcode,
                "phoneNumber": rphone,
                "label": lbl,
                "status": "online",
                "isFavorite": False,
                "liveSmsActive": True,
                "lastSmsAt": "No SMS yet",
                "lastSmsPreview": "",
                "smsCount": 0,
                "webhookKey": secrets.token_hex(12),
            }
            synced_devices.append(new_dev)
            save_runtime_state()
            send_telegram_message(chat_id, f"✅ <b>NUMBER ADDED &amp; ONLINE</b>\n───────────────────\n📞 NUMBER: <code>{escape_html(rphone)}</code>\n🏷️ LABEL: {escape_html(lbl)}", get_admin_keyboard())
            return

        if sess.get("awaitingAddMemberId") or norm.startswith("/ADDMEMBER "):
            sess["awaitingAddMemberId"] = False
            cleaned_txt = re.sub(r"^/addmember\s+", "", text, flags=re.I).strip()
            parts = cleaned_txt.split()
            raw_t = parts[0] if parts else ""
            tcid = raw_t
            if not re.match(r"^-?\d+$", tcid):
                h = raw_t.lstrip("@").lower()
                found = next((s for s in chat_sessions.values() if s.get("username", "").lstrip("@").lower() == h), None)
                if found:
                    tcid = found["chatId"]
            if not re.match(r"^-?\d+$", tcid):
                sess["awaitingAddMemberId"] = True
                send_telegram_message(chat_id, "⚠️ Valid Member ID bhejein (e.g. <code>5829104412</code>):", get_admin_keyboard())
                return
            if len(parts) > 1:
                rd = parts[1].lower()
                days = 3650 if rd == "lifetime" else max(1, min(3650, int(parts[1]) if parts[1].isdigit() else 7))
                apply_member_grant(tcid, days)
                return
            dname = (chat_sessions.get(tcid) or {}).get("username") or "telegram_user"
            send_telegram_message(
                chat_id,
                f"➕ <b>ADD MEMBER:</b> <code>{escape_html(tcid)}</code> (@{escape_html(dname)})\n───────────────────\nKitne din ka active access dena hai?",
                {"inline_keyboard": [
                    [{"text": "✅ 1 Day", "callback_data": f"ADD_MEMBER_APPLY:{tcid}:1"}, {"text": "✅ 7 Days", "callback_data": f"ADD_MEMBER_APPLY:{tcid}:7"}, {"text": "✅ 15 Days", "callback_data": f"ADD_MEMBER_APPLY:{tcid}:15"}],
                    [{"text": "✅ 30 Days", "callback_data": f"ADD_MEMBER_APPLY:{tcid}:30"}, {"text": "♾️ Lifetime Member", "callback_data": f"ADD_MEMBER_APPLY:{tcid}:3650"}],
                ]},
            )
            return

        if sess.get("awaitingLifetimeInput") or norm.startswith("/LIFETIME "):
            sess["awaitingLifetimeInput"] = False
            tcid = (re.sub(r"^/lifetime\s+", "", text, flags=re.I).strip().split() or [""])[0]
            apply_member_grant(tcid, 3650, "♾️ LIFETIME MEMBER")
            return

        if sess.get("awaitingGrantInput") or norm.startswith("/GRANT "):
            sess["awaitingGrantInput"] = False
            parts = re.sub(r"^/grant\s+", "", text, flags=re.I).strip().split()
            tcid = parts[0] if parts else ""
            rd = (parts[1] if len(parts) > 1 else "").lower()
            gdays = 3650 if rd == "lifetime" or (rd.isdigit() and int(rd) >= 3650) else max(1, min(3650, int(rd) if rd.isdigit() else 7))
            apply_member_grant(tcid, gdays)
            return

        if sess.get("awaitingRevokeInput") or norm.startswith("/REVOKE "):
            sess["awaitingRevokeInput"] = False
            tcid = re.sub(r"^/revoke\s+", "", text, flags=re.I).strip()
            if not re.match(r"^-?\d+$", tcid):
                send_telegram_message(chat_id, "⚠️ Invalid Chat ID.", get_admin_keyboard())
                return
            for g in synced_access_grants:
                if g.get("chatId") == tcid:
                    g["status"] = "revoked"
                    g["updatedAtMs"] = now_ms()
            save_runtime_state()
            send_telegram_message(chat_id, f"🚫 Revoked access for Chat ID {tcid}.", get_admin_keyboard())
            return

    # ---------- PAYMENT, ACCOUNT, & MENU ----------
    if norm in ("💳 BUY ACCESS", "💳 VIP ACCESS", "VIP ACCESS", "BUY ACCESS", "💎 PLANS"):
        sess["menuState"] = "payment"
        sess["activeDeviceId"] = ""
        sess["activeFinderCode"] = ""
        sess["activePhoneNumber"] = ""
        sess["activePulledByGetNumber"] = False
        sess["awaitingGiftCard"] = False
        sess["awaitingUpiUtr"] = False
        send_telegram_message(chat_id, format_payment_card(), get_payment_keyboard())
        send_telegram_message(chat_id, "⚡ <b>1-TAP PAYMENT</b>", build_payment_inline_actions())
        return

    if norm in ("👤 MY ACCOUNT", "MY ACCOUNT", "MY_ACCOUNT", "/MYID", "/STATUS"):
        grant = get_active_grant_for_chat(chat_id)
        if not grant:
            ptxt = "🔒 Inactive (Tap 💳 VIP ACCESS)"
        elif grant.get("planName") == "ADMIN":
            ptxt = "👑 Admin Unlimited"
        elif is_lifetime_grant(grant):
            ptxt = "♾️ Lifetime VIP Member"
        else:
            dleft = max(1, (int(grant["expiresAtMs"]) - now_ms() + 86399999) // 86400000)
            ptxt = f"💎 Weekly VIP ({dleft} days left)"
        fav_cnt = sum(1 for d in synced_devices if not is_device_removed_by_admin(d) and d.get("isFavorite"))
        lines = [
            f"🙋 <b>User:</b> {escape_html(full_name or username)}",
            f"🆔 <b>Chat ID:</b> <code>{escape_html(chat_id)}</code> <i>(tap to copy)</i>",
            f"📦 <b>Plan:</b> {ptxt}",
            f"⭐ <b>Saved Favorites:</b> <b>{fav_cnt}</b>",
        ]
        if is_admin_id:
            lines.append(f"🟢 <b>Online Numbers (Admin):</b> <b>{len(get_online_bot_devices())}</b>")
        reply_or_edit_inline_card(
            chat_id,
            callback_msg_id,
            f"👤 <b>YOUR BOT PROFILE</b>\n━━━━━━━━━━━━━━━━━━━━\n<blockquote>{chr(10).join(lines)}</blockquote>",
            {"inline_keyboard": [[{"text": "📱 GET NUMBER NOW", "callback_data": "NEXT_ONLINE"}]] if grant else [[{"text": "💳 ACTIVATE ₹25 VIP PASS", "callback_data": "UPI_QR_NEW"}]]},
        )
        return

    if norm in ("HOW_IT_WORKS", "/HELP", "❓ HOW IT WORKS", "🎯 PICK BY APP", "PICK BY APP", "APP_MENU", "/APPS", "/APP"):
        send_telegram_message(chat_id, "📱 Live OTP numbers lene ke liye niche <b>📱 GET NUMBERS</b> ya <b>🔍 FIND NUMBER</b> tap karein.", get_main_keyboard(chat_id))
        return

    if norm in ("📱 UPI QR PAYMENT", "UPI QR PAYMENT", "💳 UPI QR PAYMENT", "UPI QR", "UPI_QR_NEW", "/UPI"):
        sess["menuState"] = "payment"
        sess["activeDeviceId"] = ""
        sess["activeFinderCode"] = ""
        sess["activePhoneNumber"] = ""
        sess["activePulledByGetNumber"] = False
        sess["awaitingGiftCard"] = False
        sess["awaitingUpiUtr"] = True
        qr_bytes, order_ref, _gen_ms, exp_ms = build_amount_25_upi_qr(chat_id)
        save_runtime_state()
        exp_lbl = format_bot_timestamp(exp_ms)
        caption = "\n".join([
            "📱 <b>DIRECT ₹25 UPI QR PAYMENT</b>",
            "━━━━━━━━━━━━━━━━━━━━",
            f"<blockquote>📦 <b>Plan:</b> 💎 WEEKLY PREMIUM (₹25 · 7 days)\n💰 <b>Amount Locked:</b> <b>₹25.00</b>\n🆔 <b>Order Ref:</b> <code>{escape_html(order_ref)}</code>\n⏰ <b>Valid Time:</b> <b>5 Minutes</b> (Till {escape_html(exp_lbl)})</blockquote>",
            "1️⃣ Upar wala QR <b>5 minute</b> ke andar PhonePe / GPay / Paytm se scan karke <b>₹25</b> pay karein.",
            "2️⃣ Payment hote hi apna <b>Payment Screenshot</b> ya <b>12-digit UTR Number</b> yahan bhejein.",
            "⚡ <i>Jaise hi payment successful hoga, VIP access turant automatic chalu ho jayega!</i>",
        ])
        send_telegram_photo_bytes(
            chat_id,
            qr_bytes,
            caption,
            {"inline_keyboard": [[{"text": "🔄 CHECK PAYMENT STATUS", "callback_data": "CHECK_UPI_STATUS"}], [{"text": "🆕 GENERATE NEW 5-MIN QR", "callback_data": "UPI_QR_NEW"}]]},
            f"upi_qr_25_{order_ref}.png",
        )
        return

    if norm == "CHECK_UPI_STATUS":
        if get_active_grant_for_chat(chat_id):
            send_telegram_message(chat_id, "✅ <b>PAYMENT VERIFIED &amp; ACCESS ACTIVE!</b>\n━━━━━━━━━━━━━━━━━━━━\n🚀 Tap <b>📱 GET NUMBERS</b> below to start!", get_main_keyboard(chat_id))
            return
        reconcile_auto_verifying_payments()
        if get_active_grant_for_chat(chat_id):
            return
        if sess.get("pendingQrGeneratedAtMs"):
            unclaimed = find_unclaimed_merchant_credit_sms(int(sess["pendingQrGeneratedAtMs"]), 25)
            active_qr_sess = [s for s in chat_sessions.values() if s.get("menuState") == "payment" and int(s.get("pendingQrExpiresAtMs") or 0) > now_ms()]
            if unclaimed and len(active_qr_sess) <= 1:
                used_bank_sms_ids.add(unclaimed["id"])
                req_item = {
                    "id": f"pay_{now_ms()}_{secrets.token_hex(2)}",
                    "chatId": chat_id,
                    "username": username,
                    "planName": "💎 WEEKLY PREMIUM 💎",
                    "amountInr": 25,
                    "durationDays": 7,
                    "paymentMethod": "UPI_QR",
                    "giftCardCode": sess.get("pendingQrOrderRef") or f"SMS_{now_ms()}",
                    "status": "pending",
                }
                synced_payment_requests.insert(0, req_item)
                finalize_payment_decision(req_item, "approved", f"Auto-verified via ₹25 Bank Credit SMS ({unclaimed['sender']})")
                return
        t_now = now_ms()
        if sess.get("pendingQrExpiresAtMs") and t_now > int(sess["pendingQrExpiresAtMs"]):
            send_telegram_message(chat_id, "⏰ <b>QR 5-MINUTE TIME EXPIRED</b>\n━━━━━━━━━━━━━━━━━━━━\n<blockquote>Is QR ka 5-minute time khatam ho gaya hai.\nNaya ₹25 QR banane ke liye niche <b>🆕 GENERATE NEW 5-MIN QR</b> dabayein (ya payment ho chuka hai to <b>Screenshot / 12-digit UTR</b> bhej dein).</blockquote>", {"inline_keyboard": [[{"text": "🆕 GENERATE NEW 5-MIN QR", "callback_data": "UPI_QR_NEW"}]]})
            return
        rem_sec = max(1, (int(sess.get("pendingQrExpiresAtMs") or (t_now + 300000)) - t_now + 999) // 1000)
        send_telegram_message(chat_id, f"⏳ <b>WAITING FOR ₹25 PAYMENT ({rem_sec // 60}:{rem_sec % 60:02d} left)</b>\n━━━━━━━━━━━━━━━━━━━━\n<blockquote>Payment karne ke baad apna <b>Payment Screenshot</b> ya <b>12-digit UTR Number</b> yahan chat me send karein!</blockquote>", {"inline_keyboard": [[{"text": "🔄 CHECK AGAIN", "callback_data": "CHECK_UPI_STATUS"}], [{"text": "🆕 NEW 5-MIN QR", "callback_data": "UPI_QR_NEW"}]]})
        return

    if norm in ("🎁 AMAZON GIFT CARD", "AMAZON GIFT CARD", "AMZ_GC_PROMPT"):
        sess["menuState"] = "payment"
        sess["awaitingUpiUtr"] = False
        sess["awaitingGiftCard"] = True
        save_runtime_state()
        send_telegram_message(chat_id, "🎁 <b>AMAZON GIFT CARD PAYMENT</b>\n━━━━━━━━━━━━━━━━━━━━\n<blockquote>💎 <b>Plan:</b> WEEKLY PREMIUM (₹25 · 7 days)\n🔑 Apna genuine Amazon Gift Card Code niche send karein:</blockquote>", get_payment_keyboard())
        return

    known_actions = {
        "APP_MENU", "HOW_IT_WORKS", "MY_ACCOUNT", "AMZ_GC_PROMPT", "ADD_FAV_PROMPT", "NEXT_ONLINE",
        "📱 GET NUMBERS", "GET NUMBERS", "🎯 PICK BY APP", "PICK BY APP", "🔍 FIND NUMBER", "FIND NUMBER",
        "⭐ FAVORITES", "FAVORITES", "👤 MY ACCOUNT", "MY ACCOUNT", "❓ HOW IT WORKS", "💳 VIP ACCESS", "VIP ACCESS",
        "🏠 HOME MENU", "HOME MENU", "🔄 REFRESH SMS", "REFRESH SMS", "📩 VIEW MESSAGES", "VIEW MESSAGES",
        "+ NEW NUMBER", "⭐ ADD FAVORITE", "★ REMOVE FAVORITE", "➕ ADD FAVORITE",
    }
    is_known = norm in known_actions or any(
        norm.startswith(p) for p in ("/", "CONNECT", "REFRESH", "OTP_ONLY", "PICK_APP:", "TOGGLE_FAV:", "FAV_PAGE:", "NUM_PAGE:", "BOT_USERS", "ADD_MEMBER")
    )
    looks_like_utr = bool(re.match(r"^(?:\d{8,}|T\d{12,})$", re.sub(r"\s+", "", text), re.I) or re.search(r"\b(?:\d{12}|T\d{18,24})\b", text, re.I))
    looks_like_qr_sub = bool(incoming_photo_file_id) or (
        not is_known
        and (
            sess.get("awaitingUpiUtr")
            or (
                not any(sess.get(f) for f in ("awaitingGiftCard", "awaitingAdminPassword", "awaitingGrantInput", "awaitingAddMemberId", "awaitingLifetimeInput", "awaitingRevokeInput", "awaitingRtdbLink", "awaitingRemoveRtdb", "awaitingAddNumber", "awaitingRemoveNumber", "awaitingFavoriteInput"))
                and (looks_like_utr if sess.get("menuState") == "payment" else (not get_active_grant_for_chat(chat_id) and looks_like_utr))
            )
        )
    )
    if looks_like_qr_sub:
        pbytes = download_telegram_file_bytes(incoming_photo_file_id) if incoming_photo_file_id else None
        sess["awaitingUpiUtr"] = False
        sess["menuState"] = "main"
        process_qr_payment_submission(chat_id, username, text.strip(), pbytes, incoming_photo_file_id or None)
        return

    if sess.get("awaitingGiftCard"):
        ok_gc, norm_gc, gc_reason = validate_amazon_gift_card_format(text)
        nkey = re.sub(r"[-\s]", "", norm_gc).upper()
        is_dup = nkey in used_payment_refs or norm_gc.upper() in used_payment_refs or any(re.sub(r"[-\s]", "", p.get("giftCardCode", "")).upper() == nkey for p in synced_payment_requests)
        sess["awaitingGiftCard"] = False
        sess["menuState"] = "main"
        if not ok_gc or is_dup:
            rsn = "Duplicate / already-used Gift Card code rejected automatically." if is_dup else gc_reason
            if nkey:
                used_payment_refs.add(nkey)
            synced_payment_requests.insert(0, {"id": f"pay_{now_ms()}_{secrets.token_hex(2)}", "chatId": chat_id, "username": username, "planName": "💎 WEEKLY PREMIUM 💎", "amountInr": 25, "durationDays": 7, "paymentMethod": "AMAZON_GIFT_CARD", "giftCardCode": norm_gc or text[:64], "status": "rejected", "verificationNote": rsn})
            save_runtime_state()
            send_telegram_message(chat_id, f"❌ <b>FAKE / INVALID GIFT CARD REJECTED</b>\n───────────────────\n🎁 Code: <code>{escape_html(norm_gc or text[:64])}</code>\n⚠️ {escape_html(rsn)}", get_main_keyboard(chat_id))
            return
        new_pay = {"id": f"pay_{now_ms()}_{secrets.token_hex(2)}", "chatId": chat_id, "username": username, "planName": "💎 WEEKLY PREMIUM 💎", "amountInr": 25, "durationDays": 7, "paymentMethod": "AMAZON_GIFT_CARD", "giftCardCode": norm_gc, "status": "pending"}
        used_payment_refs.add(nkey)
        synced_payment_requests.insert(0, new_pay)
        save_runtime_state()
        for aid in resolve_admin_chat_ids():
            if aid != chat_id:
                send_telegram_message(aid, f"🔔 <b>NEW AMAZON GIFT CARD PAYMENT</b>\n───────────────────\n👤 User: @{escape_html(username)} (<code>{escape_html(chat_id)}</code>)\n📦 Plan: 💎 WEEKLY PREMIUM (₹25 / 7 days)\n🎁 Code: <code>{escape_html(norm_gc)}</code>", {"inline_keyboard": [[{"text": "✅ APPROVE (7d)", "callback_data": f"APPROVE_PAY:{new_pay['id']}"}, {"text": "❌ REJECT", "callback_data": f"REJECT_PAY:{new_pay['id']}"}]]})
        send_telegram_message(chat_id, f"✅ <b>PAYMENT SUBMITTED</b>\n───────────────────\n🎁 Method: Amazon Gift Card\n🔑 Code: <code>{escape_html(norm_gc)}</code>\n📦 Plan: 💎 WEEKLY PREMIUM (7 days)\n⏳ Status: Waiting for Admin verification", get_main_keyboard(chat_id))
        return

    # ---------- ACTIVE VIP GATE ----------
    active_grant = get_active_grant_for_chat(chat_id)
    if not active_grant:
        sess["menuState"] = "payment"
        send_telegram_message(chat_id, f"🔒 <b>VIP ACCESS REQUIRED</b>\n━━━━━━━━━━━━━━━━━━━━\n<blockquote>Numbers &amp; Live OTP access ke liye Weekly VIP Pass activate karein.</blockquote>\n\n{format_payment_card()}", get_payment_keyboard())
        send_telegram_message(chat_id, "⚡ <b>ACTIVATE INSTANTLY BELOW 👇</b>", build_payment_inline_actions())
        return

    if norm.startswith("PICK_APP:"):
        send_telegram_message(chat_id, "📱 Live OTP number lene ke liye niche <b>📱 GET NUMBERS</b> tap karein.", get_main_keyboard(chat_id))
        return

    if norm in ("📱 GET NUMBERS", "GET NUMBERS", "+ NEW NUMBER", "NEXT_ONLINE"):
        if not get_online_bot_devices() and rtdb_urls:
            sync_from_rtdb()
        pool = get_otp_receiving_bot_devices()
        if not pool:
            send_telegram_message(chat_id, "⚠️ No online OTP-receiving numbers available right now.", get_main_keyboard(chat_id))
            return
        seen_ids = set(sess.get("seenNumberIds") or [])
        c_idx = next((i for i, d in enumerate(pool) if d["id"] != sess.get("activeDeviceId") and d["id"] not in seen_ids), -1)
        if c_idx < 0:
            seen_ids.clear()
            cur_i = next((i for i, d in enumerate(pool) if d["id"] == sess.get("activeDeviceId")), -1)
            c_idx = (cur_i + 1) % len(pool) if cur_i >= 0 else 0
        prev_state = sess.get("menuState")
        chosen = pool[c_idx]
        seen_ids.add(chosen["id"])
        sess["seenNumberIds"] = list(seen_ids)[-100:]
        otp_cnt, _ = get_device_otp_stats(chosen)
        sess["activeDeviceId"] = chosen["id"]
        sess["activeFinderCode"] = chosen["finderCode"]
        sess["activePhoneNumber"] = chosen["phoneNumber"]
        sess["activePulledByGetNumber"] = True
        sess["menuState"] = "connected"
        save_runtime_state()
        if prev_state != "connected":
            hdr = f"⚡ <b>Number #{c_idx + 1}/{len(pool)}</b>  •  🔑 <b>{otp_cnt} OTPs</b>" if is_admin_id else f"⚡ <b>LIVE NUMBER READY</b>  •  🔑 <b>{otp_cnt} OTPs</b>"
            send_telegram_message(chat_id, f"{hdr}\n📞 <code>{escape_html(chosen['phoneNumber'])}</code>  ·  <i>Controls active below 👇</i>", get_connected_keyboard(chat_id))
        msgs = synced_messages_by_device.get(chosen["id"]) or []
        send_telegram_message(chat_id, format_connected_card(chosen, msgs), build_connected_inline_actions(chosen, chat_id))
        return

    if norm.startswith("NUM_PAGE:") or norm in ("📱 ONLINE NUMBERS", "/NUMBERS", "/ONLINE"):
        pnum = max(0, int(text[9:].strip() or 0)) if norm.startswith("NUM_PAGE:") else 0
        send_online_numbers_page(chat_id, pnum, "📱 ALL ONLINE NUMBERS", get_admin_keyboard())
        return

    if norm in ("🔄 REFRESH SMS", "REFRESH SMS", "🔄 REFRESH", "REFRESH", "/REFRESH", "REFRESH_SMS") or norm.startswith("REFRESH:"):
        if sess.get("menuState") != "connected" or not sess.get("activePulledByGetNumber") or not sess.get("activeDeviceId"):
            send_telegram_message(chat_id, "⚠️ Pehle <b>📱 GET NUMBERS</b> par click karke ek number nikalein!\nBina Get Number ke kisi dusre number ka SMS nahi dikhega.", get_main_keyboard(chat_id))
            return
        if now_ms() - last_rtdb_sync_ms > 1000:
            sync_from_rtdb()
        req_id = text[8:].strip() if norm.startswith("REFRESH:") else ""
        if req_id and req_id != sess["activeDeviceId"]:
            send_telegram_message(chat_id, f"⚠️ Ye purane number ka card hai. Aap abhi <code>{escape_html(sess['activePhoneNumber'])}</code> par connected hain.", get_connected_keyboard(chat_id))
            return
        target = next((d for d in get_online_bot_devices() if d["id"] == sess["activeDeviceId"]), None)
        if not target:
            send_telegram_message(chat_id, f"⚠️ Aapka nikala hua number (<code>{escape_html(sess['activePhoneNumber'])}</code>) abhi Offline ho gaya hai.\nNaya OTP number lene ke liye <b>📱 GET NUMBERS</b> tap karein.", get_main_keyboard(chat_id))
            return
        msgs = synced_messages_by_device.get(target["id"]) or []
        hdr = f"🔄 <b>REFRESHED INBOX</b>  ·  <code>{escape_html(target['phoneNumber'])}</code>\n🕒 <i>{escape_html(rtdb_last_sync_at or format_bot_timestamp())}</i>  •  📬 <b>{len(msgs)} msgs</b>\n━━━━━━━━━━━━━━━━━━━━"
        reply_or_edit_inline_card(chat_id, callback_msg_id, f"{hdr}\n{format_sms_list(msgs, max(1500, 3850 - len(hdr)))}", build_connected_inline_actions(target, chat_id))
        return

    if norm == "OTP_ONLY" or norm.startswith("OTP_ONLY:"):
        send_telegram_message(chat_id, "📩 Live SMS &amp; OTPs dekhne ke liye niche <b>🔄 REFRESH SMS</b> ya <b>📩 VIEW MESSAGES</b> tap karein.", get_connected_keyboard(chat_id) if sess.get("menuState") == "connected" else get_main_keyboard(chat_id))
        return

    if norm in ("📩 VIEW MESSAGES", "VIEW MESSAGES", "/SMS"):
        if sess.get("menuState") != "connected" or not sess.get("activePulledByGetNumber") or not sess.get("activeDeviceId"):
            send_telegram_message(chat_id, "⚠️ Pehle <b>📱 GET NUMBERS</b> par click karke ek number nikalein!", get_main_keyboard(chat_id))
            return
        if now_ms() - last_rtdb_sync_ms > 1200 and rtdb_urls:
            sync_from_rtdb()
        target = next((d for d in get_online_bot_devices() if d["id"] == sess["activeDeviceId"]), None)
        if not target:
            send_telegram_message(chat_id, "⚠️ Aapka nikala hua number abhi Offline hai. Naya number lene ke liye <b>📱 GET NUMBERS</b> tap karein.", get_main_keyboard(chat_id))
            return
        msgs = synced_messages_by_device.get(target["id"]) or []
        hdr = f"📩 <b>SMS INBOX</b>  ·  <code>{escape_html(target['phoneNumber'])}</code>\n📬 <b>{len(msgs)} recent msgs</b>  •  🕒 <i>{escape_html(rtdb_last_sync_at or 'Live')}</i>\n━━━━━━━━━━━━━━━━━━━━"
        send_telegram_message(chat_id, f"{hdr}\n{format_sms_list(msgs, max(1500, 3850 - len(hdr)))}", build_connected_inline_actions(target, chat_id))
        return

    if norm in ("⭐ ADD FAVORITE", "★ REMOVE FAVORITE", "ADD FAVORITE") or norm.startswith("TOGGLE_FAV:"):
        req_id = text[11:].strip() if norm.startswith("TOGGLE_FAV:") else sess.get("activeDeviceId", "")
        target = next((d for d in synced_devices if not is_device_removed_by_admin(d) and d["id"] == req_id), None) or next((d for d in synced_devices if not is_device_removed_by_admin(d) and d["id"] == sess.get("activeDeviceId")), None)
        if not target:
            sess["awaitingFavoriteInput"] = True
            send_telegram_message(chat_id, "⭐ <b>ADD TO FAVORITES</b>\n━━━━━━━━━━━━━━━━━━━━\n<blockquote>📞 Phone Number niche send karein (e.g. <code>9839017772</code>) to add to Favorites:</blockquote>", get_main_keyboard(chat_id))
            return
        nfav = not bool(target.get("isFavorite"))
        set_device_favorite_state(target, nfav)
        msgs = synced_messages_by_device.get(target["id"]) or []
        if callback_msg_id:
            edit_telegram_message_text(chat_id, callback_msg_id, format_connected_card(target, msgs), build_connected_inline_actions(target, chat_id))
        else:
            send_telegram_message(chat_id, f"⭐ Added <code>{escape_html(target['phoneNumber'])}</code> to Favorites!" if nfav else f"☆ Removed <code>{escape_html(target['phoneNumber'])}</code> from Favorites.", build_connected_inline_actions(target, chat_id))
        return

    if norm in ("ADD_FAV_PROMPT", "➕ ADD FAVORITE"):
        sess["awaitingFavoriteInput"] = True
        send_telegram_message(chat_id, "⭐ <b>ADD FAVORITE NUMBER</b>\n━━━━━━━━━━━━━━━━━━━━\n<blockquote>📞 Phone Number niche send karein (e.g. <code>9839017772</code>) to save in ⭐ FAVORITES:</blockquote>", get_main_keyboard(chat_id))
        return

    if norm in ("⭐ FAVORITES", "FAVORITES") or norm.startswith("FAV_PAGE:"):
        pnum = max(0, int(text[9:].strip() or 0)) if norm.startswith("FAV_PAGE:") else 0
        on_favs = [d for d in get_online_bot_devices() if d.get("isFavorite")]
        off_favs = [d for d in synced_devices if not is_device_removed_by_admin(d) and d.get("status") != "online" and d.get("isFavorite")]
        favs = on_favs + off_favs
        sess["menuState"] = "favorites"
        if not favs:
            reply_or_edit_inline_card(chat_id, callback_msg_id, "⭐ <b>SAVED FAVORITES (0)</b>\n━━━━━━━━━━━━━━━━━━━━\n<blockquote>📭 Abhi koi favorite number save nahi hai.\nNiche <b>➕ ADD FAVORITE</b> dabakar ya kisi connected number par ⭐ tap karke save karein.</blockquote>", {"inline_keyboard": [[{"text": "➕ ADD FAVORITE", "callback_data": "ADD_FAV_PROMPT"}]]})
            return
        page_size = 8
        total_pages = max(1, (len(favs) + page_size - 1) // page_size)
        safe_page = max(0, min(pnum, total_pages - 1))
        start = safe_page * page_size
        pfavs = favs[start:start + page_size]
        fav_lines = "\n".join(f"<b>{start + off + 1}.</b> {'🟢' if d['status'] == 'online' else '🔴'} <code>{escape_html(d['phoneNumber'])}</code>  •  {d['smsCount']} SMS" for off, d in enumerate(pfavs))
        irows = []
        for d in pfavs:
            dot = "🟢" if d["status"] == "online" else "🔴"
            irows.append([{"text": f"{dot} {d['phoneNumber']}  ·  {'Connect' if d['status'] == 'online' else 'Offline'}", "callback_data": f"CONNECT_ID:{d['id']}"}])
            irows.append([{"text": f"📋 COPY {d['phoneNumber']}", "copy_text": {"text": d["phoneNumber"]}}, {"text": "❌ REMOVE", "callback_data": f"TOGGLE_FAV:{d['id']}"}])
        if total_pages > 1:
            nav = []
            if safe_page > 0:
                nav.append({"text": "⬅️ PREV", "callback_data": f"FAV_PAGE:{safe_page - 1}"})
            nav.append({"text": f"📄 {safe_page + 1}/{total_pages} ({len(favs)})", "callback_data": f"FAV_PAGE:{safe_page}"})
            if safe_page + 1 < total_pages:
                nav.append({"text": "NEXT ➡️", "callback_data": f"FAV_PAGE:{safe_page + 1}"})
            irows.append(nav)
        irows.append([{"text": "➕ ADD FAVORITE", "callback_data": "ADD_FAV_PROMPT"}])
        reply_or_edit_inline_card(chat_id, callback_msg_id, f"⭐ <b>SAVED FAVORITES ({len(favs)})</b>  ·  🟢 <b>{len(on_favs)} Online</b>\n━━━━━━━━━━━━━━━━━━━━\n<blockquote>{fav_lines}</blockquote>\n<i>Niche full number par tap karke connect ya copy karein 👇</i>", {"inline_keyboard": irows})
        return

    if norm in ("🔍 FIND NUMBER", "FIND NUMBER", "🔍 FIND DEVICE"):
        sess["menuState"] = "find"
        send_telegram_message(chat_id, "🔍 <b>FIND NUMBER</b>\n━━━━━━━━━━━━━━━━━━━━\n<blockquote>📞 Phone Number niche send karein (e.g. <code>9839017772</code>):</blockquote>", get_main_keyboard(chat_id))
        return

    lookup = text[11:].strip() if norm.startswith("CONNECT_ID:") else (text[8:].strip() if norm.startswith("CONNECT:") else text)
    cdigits = re.sub(r"\D", "", lookup)

    def matches_dev(d):
        if is_device_removed_by_admin(d):
            return False
        if d["id"] == lookup or d["finderCode"].upper() == lookup.upper() or re.sub(r"^rtdb_", "", d["id"]).upper() == lookup.upper():
            return True
        ddig = re.sub(r"\D", "", d["phoneNumber"])
        return bool(cdigits and ddig and (ddig == cdigits or ddig.endswith(cdigits)))

    matched_on = next((d for d in get_online_bot_devices() if matches_dev(d)), None)
    if sess.get("awaitingFavoriteInput"):
        sess["awaitingFavoriteInput"] = False
        fcand = matched_on or next((d for d in synced_devices if matches_dev(d)), None)
        if not fcand:
            send_telegram_message(chat_id, f"⚠️ Number \"{escape_html(text)}\" not found. Try an exact Phone Number.", get_main_keyboard(chat_id))
            return
        set_device_favorite_state(fcand, True)
        send_telegram_message(chat_id, f"⭐ Added <code>{escape_html(fcand['phoneNumber'])}</code> to Favorites!", get_main_keyboard(chat_id))
        return

    if matched_on:
        prev_st = sess.get("menuState")
        sess["activeDeviceId"] = matched_on["id"]
        sess["activeFinderCode"] = matched_on["finderCode"]
        sess["activePhoneNumber"] = matched_on["phoneNumber"]
        sess["activePulledByGetNumber"] = True
        sess["menuState"] = "connected"
        save_runtime_state()
        if prev_st != "connected":
            send_telegram_message(chat_id, f"⚡ <b>Connected:</b> <code>{escape_html(matched_on['phoneNumber'])}</code>  ·  <i>Controls active below 👇</i>", get_connected_keyboard(chat_id))
        msgs = synced_messages_by_device.get(matched_on["id"]) or []
        send_telegram_message(chat_id, format_connected_card(matched_on, msgs), build_connected_inline_actions(matched_on, chat_id))
        return

    off_match = next((d for d in synced_devices if d.get("status") != "online" and matches_dev(d)), None)
    if off_match:
        send_telegram_message(chat_id, f"⚠️ Number <code>{escape_html(off_match['phoneNumber'])}</code> is currently 🔴 Offline.\nTap 📱 GET NUMBERS for an active number.", get_main_keyboard(chat_id))
        return

    send_telegram_message(chat_id, f"❓ Unrecognized command or number \"{escape_html(text)}\".\nTap 📱 GET NUMBERS or 🔍 FIND NUMBER below.", get_main_keyboard(chat_id))


# ==============================================================================
# PER-CHAT WORKER QUEUES & BACKGROUND LOOPS
# ==============================================================================
def enqueue_update(upd):
    msg = upd.get("message") or (upd.get("callback_query") or {}).get("message") or {}
    cid = str((msg.get("chat") or {}).get("id") or "global")
    with chat_queues_lock:
        q = chat_queues.get(cid)
        if q is None:
            q = queue.Queue()
            chat_queues[cid] = q

            def _worker(work_q):
                while True:
                    item = work_q.get()
                    try:
                        handle_telegram_update(item)
                    except Exception as exc:
                        print(f"[BOT] Update error: {exc}", file=sys.stderr)
                    finally:
                        work_q.task_done()

            threading.Thread(target=_worker, args=(q,), daemon=True).start()
        q.put(upd)


def rtdb_sync_loop():
    while True:
        try:
            if rtdb_urls:
                sync_from_rtdb()
        except Exception as exc:
            print(f"[RTDB] Sync loop error: {exc}", file=sys.stderr)
        time.sleep(1.5)


def start_optional_health_server():
    port_env = os.environ.get("PORT", "").strip()
    if not port_env:
        return
    try:
        port = int(port_env)
    except ValueError:
        return

    class HealthHandler(BaseHTTPRequestHandler):
        def do_GET(self):
            if self.path in ("/", "/healthz", "/api/health"):
                body = json.dumps({
                    "ok": True,
                    "botRunning": bot_running,
                    "verifiedUsername": verified_username,
                    "rtdbLinks": len(rtdb_urls),
                    "onlineNumbers": len(get_online_bot_devices()),
                }).encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            else:
                self.send_response(404)
                self.end_headers()

        def log_message(self, _fmt, *_args):
            return

    try:
        srv = ThreadingHTTPServer(("0.0.0.0", port), HealthHandler)
        threading.Thread(target=srv.serve_forever, daemon=True).start()
        print(f"[HTTP] Health server listening on port {port}")
    except OSError:
        pass


def main():
    global bot_running, verified_username, verified_bot_name, update_offset, last_bot_error

    init_rtdb_defaults()
    load_runtime_state()
    start_optional_health_server()

    if not BOT_TOKEN or "PASTE_YOUR" in BOT_TOKEN:
        print(
            "[ERROR] Missing TELEGRAM_BOT_TOKEN!\n"
            "Open bot.py and replace PASTE_YOUR_BOTFATHER_TOKEN_HERE with your @BotFather token,\n"
            "or set TELEGRAM_BOT_TOKEN in your hosting environment variables.",
            file=sys.stderr,
        )
        sys.exit(1)

    me = None
    while True:
        me = call_telegram_api("getMe")
        if me.get("ok") and me.get("result"):
            break
        desc = str(me.get("description") or "")
        if "401" in desc or "Unauthorized" in desc:
            print(f"[ERROR] Invalid BOT_TOKEN ({desc})", file=sys.stderr)
            sys.exit(1)
        print(f"[WARN] Telegram getMe retrying in 3s: {desc}", file=sys.stderr)
        time.sleep(3)

    verified_username = me["result"].get("username")
    verified_bot_name = me["result"].get("first_name")
    call_telegram_api("deleteWebhook", {"drop_pending_updates": False})
    commands = [
        {"command": "start", "description": "🏠 Main Menu & Live OTP Hub"},
        {"command": "admin", "description": "⚙️ Admin Controls"},
    ]
    call_telegram_api("setMyCommands", {"commands": commands})
    call_telegram_api("setMyCommands", {"commands": commands, "scope": {"type": "all_private_chats"}})
    call_telegram_api("setChatMenuButton", {"menu_button": {"type": "commands"}})

    if rtdb_urls:
        sync_from_rtdb()
    threading.Thread(target=rtdb_sync_loop, daemon=True).start()

    def _graceful_exit(_signum, _frame):
        save_runtime_state()
        sys.exit(0)

    signal.signal(signal.SIGINT, _graceful_exit)
    signal.signal(signal.SIGTERM, _graceful_exit)

    bot_running = True
    print(f"[OK] @{verified_username} ({verified_bot_name}) started 24/7 polling with {len(rtdb_urls)} RTDB link(s)!")

    while True:
        try:
            res = call_telegram_api(
                "getUpdates",
                {"offset": update_offset, "timeout": 25, "allowed_updates": ["message", "callback_query"]},
                timeout_sec=35,
            )
            if res.get("ok") and isinstance(res.get("result"), list):
                last_bot_error = None
                for upd in res["result"]:
                    update_offset = max(update_offset, int(upd["update_id"]) + 1)
                    enqueue_update(upd)
            else:
                last_bot_error = res.get("description") or "Polling error"
                print(f"[WARN] Telegram polling: {last_bot_error}", file=sys.stderr)
                time.sleep(5 if "Conflict" in str(last_bot_error) else 2)
        except Exception as exc:
            last_bot_error = str(exc)
            print(f"[WARN] Network error: {last_bot_error}", file=sys.stderr)
            time.sleep(2)


if __name__ == "__main__":
    main()

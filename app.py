#!/usr/bin/env python3
import os, re, io, csv, json, zipfile, tempfile, threading, uuid, string, html as html_module
from pathlib import Path
from functools import wraps
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo
from flask import Flask, request, jsonify, send_file, render_template, session, redirect, url_for, Response
from pdf2image import convert_from_path
from pypdf import PdfReader, PdfWriter, PageObject, Transformation
from reportlab.pdfgen import canvas
import pytesseract
import pdfplumber
import psycopg2
from postcode_checker import check_label_postcode, render_pdf_pages
from psycopg2.extras import RealDictCursor

app = Flask(__name__)
app.secret_key = os.environ.get('ADMIN_PASSWORD', 'changeme') + '_secret'
app.config['MAX_CONTENT_LENGTH'] = 200 * 1024 * 1024
jobs = {}
jobs_lock = threading.Lock()
ADMIN_PASSWORD = os.environ.get('ADMIN_PASSWORD', 'M4Mart2026')
DATABASE_URL = os.environ.get('DATABASE_URL')
WEBSITE_URL = 'pillowfactory.co.uk'


# ── DATABASE ──────────────────────────────────────────────────────────────────

def get_db():
    conn = psycopg2.connect(DATABASE_URL)
    return conn

def init_db():
    """Create tables if they don't exist."""
    try:
        conn = get_db()
        cur = conn.cursor()
        cur.execute('''
            CREATE TABLE IF NOT EXISTS batch_counter (
                id INTEGER PRIMARY KEY DEFAULT 1,
                value INTEGER NOT NULL DEFAULT 0,
                CHECK (id = 1)
            )
        ''')
        cur.execute('''
            INSERT INTO batch_counter (id, value) VALUES (1, 0)
            ON CONFLICT (id) DO NOTHING
        ''')
        cur.execute('''
            CREATE TABLE IF NOT EXISTS sku_aliases (
                id SERIAL PRIMARY KEY,
                normalized_key TEXT NOT NULL,
                raw_sku TEXT NOT NULL,
                canonical_sku TEXT NOT NULL,
                date_added TIMESTAMP NOT NULL DEFAULT NOW(),
                last_seen TIMESTAMP NOT NULL DEFAULT NOW(),
                times_seen INTEGER NOT NULL DEFAULT 1,
                UNIQUE (normalized_key, canonical_sku)
            )
        ''')
        cur.execute('''
            CREATE TABLE IF NOT EXISTS sku_unmapped (
                normalized_key TEXT PRIMARY KEY,
                raw_sku TEXT NOT NULL,
                first_seen TIMESTAMP NOT NULL DEFAULT NOW(),
                last_seen TIMESTAMP NOT NULL DEFAULT NOW(),
                times_seen INTEGER NOT NULL DEFAULT 1,
                dismissed BOOLEAN NOT NULL DEFAULT FALSE
            )
        ''')
        # Merged label PDFs, stored in the DB (not the filesystem) so they
        # survive Railway restarts/redeploys. Kept for 2 days on a rolling
        # basis — see cleanup_old_label_files(), called on every /upload.
        cur.execute('''
            CREATE TABLE IF NOT EXISTS label_files (
                job_id TEXT PRIMARY KEY,
                tab TEXT NOT NULL,
                batch_id TEXT,
                filename TEXT NOT NULL,
                file_data BYTEA NOT NULL,
                created_at TIMESTAMP NOT NULL DEFAULT NOW()
            )
        ''')
        # Every pick-list line (SKU + qty) ever generated, one row per SKU
        # per batch, kept indefinitely (NOT subject to the 2-day cleanup —
        # this is what /admin/pick-list-totals sums over for weekly totals).
        cur.execute('''
            CREATE TABLE IF NOT EXISTS pick_list_entries (
                id SERIAL PRIMARY KEY,
                job_id TEXT NOT NULL,
                tab TEXT NOT NULL,
                batch_id TEXT,
                sku TEXT NOT NULL,
                qty INTEGER NOT NULL,
                created_at TIMESTAMP NOT NULL DEFAULT NOW()
            )
        ''')
        conn.commit()
        cur.close()
        conn.close()
        print("Database initialised")
    except Exception as e:
        print(f"DB init error: {e}")

def get_next_batch_id():
    """Get and increment batch counter from database."""
    def num_to_letters(num):
        result = ''
        num += 1
        while num > 0:
            num -= 1
            result = string.ascii_uppercase[num % 26] + result
            num //= 26
        return result
    try:
        conn = get_db()
        cur = conn.cursor()
        cur.execute('UPDATE batch_counter SET value = value + 1 WHERE id = 1 RETURNING value')
        n = cur.fetchone()[0] - 1
        conn.commit()
        cur.close()
        conn.close()
        return num_to_letters(n)
    except Exception as e:
        print(f"Batch counter error: {e}")
        return 'A'


# ── LABEL FILE STORAGE (2-day rolling retention) + PICK LIST HISTORY ────────

def cleanup_old_label_files():
    """Delete label PDFs older than 2 days. Called opportunistically on every
    /upload rather than via a separate scheduled worker — Railway has no
    lightweight built-in cron for this app, and an upload-triggered sweep
    keeps the table pruned without adding a second process to run/monitor."""
    try:
        conn = get_db()
        cur = conn.cursor()
        cur.execute("DELETE FROM label_files WHERE created_at < NOW() - INTERVAL '2 days'")
        conn.commit()
        cur.close()
        conn.close()
    except Exception as e:
        print(f"Label file cleanup error: {e}")


def save_label_file(job_id, tab, batch_id, filename, file_bytes):
    """Store a finished merged-labels PDF in the DB, keyed by job_id, so
    /download/<job_id> keeps working for 2 days even across app restarts.
    batch_id is stored alongside so the front-end history list can show it."""
    try:
        conn = get_db()
        cur = conn.cursor()
        cur.execute('''
            INSERT INTO label_files (job_id, tab, batch_id, filename, file_data)
            VALUES (%s, %s, %s, %s, %s)
            ON CONFLICT (job_id) DO UPDATE SET
                tab = EXCLUDED.tab, batch_id = EXCLUDED.batch_id,
                filename = EXCLUDED.filename, file_data = EXCLUDED.file_data,
                created_at = NOW()
        ''', (job_id, tab, batch_id, filename, psycopg2.Binary(file_bytes)))
        conn.commit()
        cur.close()
        conn.close()
    except Exception as e:
        print(f"Save label file error: {e}")


def save_pick_list_entries(job_id, tab, batch_id, pick_list):
    """Record every SKU/qty line from a generated pick list, permanently
    (not subject to the 2-day label-file cleanup) — this is the running
    history that /admin/pick-list-totals sums for weekly totals."""
    if not pick_list:
        return
    try:
        conn = get_db()
        cur = conn.cursor()
        for entry in pick_list:
            cur.execute('''
                INSERT INTO pick_list_entries (job_id, tab, batch_id, sku, qty)
                VALUES (%s, %s, %s, %s, %s)
            ''', (job_id, tab, batch_id, entry['sku'], entry['qty']))
        conn.commit()
        cur.close()
        conn.close()
    except Exception as e:
        print(f"Save pick list history error: {e}")


# ── SKU ALIAS / CANONICAL MAPPING ────────────────────────────────────────────
# Many Amazon listings are duplicates of the same physical product, distinguished
# only by symbols added to the SKU to satisfy Amazon's "no duplicate SKU" rule
# (e.g. HF-P2Px3~ , HF-P2Px3* , HF-P2Px3!! are all the same item as HF-P2Px3).
# '+' and '-' are NOT noise — they carry real meaning (e.g. v-plo+cse = "with case",
# 6372-P2 vs 6372-P4 = different quantities) so they're preserved, with repeated
# runs (++, +++, --, ---) collapsed to a single occurrence so messy OCR variants
# of the *same* meaningful symbol still match each other.
# Matching is exact-only against a confirmed table — nothing is ever auto-merged
# without the user explicitly approving the mapping in /admin.

def normalize_sku_key(sku):
    """Build the lookup key used for alias matching.
    Strips all symbols except + and -, then collapses runs of + or - into one."""
    if not sku:
        return ''
    key = re.sub(r'[^A-Za-z0-9+\-]', '', sku).upper()
    key = re.sub(r'\+{2,}', '+', key)
    key = re.sub(r'-{2,}', '-', key)
    return key

def get_canonical_sku(raw_sku):
    """Look up raw_sku against confirmed aliases. Returns (canonical_sku, was_mapped).
    If no confirmed mapping exists, logs it to sku_unmapped and returns the raw SKU unchanged."""
    if not raw_sku or raw_sku in ('NOT FOUND', 'ERROR'):
        return raw_sku, False
    key = normalize_sku_key(raw_sku)
    if not key:
        return raw_sku, False
    try:
        conn = get_db()
        cur = conn.cursor(cursor_factory=RealDictCursor)
        cur.execute('SELECT canonical_sku FROM sku_aliases WHERE normalized_key = %s LIMIT 1', (key,))
        row = cur.fetchone()
        if row:
            cur.execute('''
                UPDATE sku_aliases SET last_seen = NOW(), times_seen = times_seen + 1
                WHERE normalized_key = %s AND canonical_sku = %s
            ''', (key, row['canonical_sku']))
            conn.commit()
            cur.close()
            conn.close()
            return row['canonical_sku'], True
        # No confirmed mapping — log/refresh it in the unmapped queue
        cur.execute('''
            INSERT INTO sku_unmapped (normalized_key, raw_sku, first_seen, last_seen, times_seen, dismissed)
            VALUES (%s, %s, NOW(), NOW(), 1, FALSE)
            ON CONFLICT (normalized_key) DO UPDATE
            SET last_seen = NOW(), times_seen = sku_unmapped.times_seen + 1,
                raw_sku = EXCLUDED.raw_sku
        ''', (key, raw_sku))
        conn.commit()
        cur.close()
        conn.close()
        return raw_sku, False
    except Exception as e:
        print(f"SKU alias lookup error: {e}")
        return raw_sku, False

def get_unmapped_skus():
    """Get all unmapped SKUs seen (excluding dismissed) for admin page."""
    try:
        conn = get_db()
        cur = conn.cursor(cursor_factory=RealDictCursor)
        cur.execute('''
            SELECT * FROM sku_unmapped WHERE dismissed = FALSE
            ORDER BY last_seen DESC
        ''')
        rows = cur.fetchall()
        cur.close()
        conn.close()
        return rows
    except Exception as e:
        print(f"Get unmapped SKUs error: {e}")
        return []

def get_alias_variants_for_canonical(canonical_sku):
    """Get all confirmed variants for one canonical SKU (for AJAX fragment rendering)."""
    try:
        conn = get_db()
        cur = conn.cursor(cursor_factory=RealDictCursor)
        cur.execute('''
            SELECT * FROM sku_aliases WHERE canonical_sku = %s ORDER BY date_added DESC
        ''', (canonical_sku,))
        rows = cur.fetchall()
        cur.close()
        conn.close()
        return rows
    except Exception as e:
        print(f"Get alias variants error: {e}")
        return []


def get_all_aliases():
    """Get all confirmed alias mappings, grouped by canonical SKU, for admin page."""
    try:
        conn = get_db()
        cur = conn.cursor(cursor_factory=RealDictCursor)
        cur.execute('''
            SELECT * FROM sku_aliases ORDER BY canonical_sku, date_added DESC
        ''')
        rows = cur.fetchall()
        cur.close()
        conn.close()
        grouped = {}
        for r in rows:
            grouped.setdefault(r['canonical_sku'], []).append(r)
        return grouped
    except Exception as e:
        print(f"Get aliases error: {e}")
        return {}

def find_existing_canonical(canonical_sku):
    """Case-insensitive lookup: if a canonical SKU already exists that matches except for case,
    return its exact stored form so we reuse it instead of creating a near-duplicate group."""
    if not canonical_sku:
        return None
    try:
        conn = get_db()
        cur = conn.cursor()
        cur.execute('''
            SELECT DISTINCT canonical_sku FROM sku_aliases
            WHERE LOWER(canonical_sku) = LOWER(%s) LIMIT 1
        ''', (canonical_sku,))
        row = cur.fetchone()
        cur.close()
        conn.close()
        return row[0] if row else None
    except Exception as e:
        print(f"Find existing canonical error: {e}")
        return None

def confirm_sku_alias(raw_sku, canonical_sku):
    """Add a confirmed mapping and remove it from the unmapped queue."""
    key = normalize_sku_key(raw_sku)
    if not key or not canonical_sku:
        return False
    # Reuse an existing canonical SKU's exact casing if one matches case-insensitively,
    # so typos in casing don't fragment one product into two separate groups.
    existing = find_existing_canonical(canonical_sku)
    if existing:
        canonical_sku = existing
    try:
        conn = get_db()
        cur = conn.cursor()
        cur.execute('''
            INSERT INTO sku_aliases (normalized_key, raw_sku, canonical_sku, date_added, last_seen, times_seen)
            VALUES (%s, %s, %s, NOW(), NOW(), 1)
            ON CONFLICT (normalized_key, canonical_sku) DO UPDATE
            SET raw_sku = EXCLUDED.raw_sku, last_seen = NOW()
        ''', (key, raw_sku, canonical_sku))
        cur.execute('DELETE FROM sku_unmapped WHERE normalized_key = %s', (key,))
        conn.commit()
        cur.close()
        conn.close()
        return True
    except Exception as e:
        print(f"Confirm alias error: {e}")
        return False

def dismiss_unmapped_sku(normalized_key):
    """Mark an unmapped SKU as dismissed (it's its own item, stop asking)."""
    try:
        conn = get_db()
        cur = conn.cursor()
        cur.execute('UPDATE sku_unmapped SET dismissed = TRUE WHERE normalized_key = %s', (normalized_key,))
        conn.commit()
        cur.close()
        conn.close()
        return True
    except Exception as e:
        print(f"Dismiss unmapped SKU error: {e}")
        return False

def delete_sku_alias(alias_id):
    """Delete a single confirmed alias variant (does not affect canonical SKU's other variants)."""
    try:
        conn = get_db()
        cur = conn.cursor()
        cur.execute('DELETE FROM sku_aliases WHERE id = %s', (alias_id,))
        conn.commit()
        cur.close()
        conn.close()
        return True
    except Exception as e:
        print(f"Delete alias error: {e}")
        return False

def update_sku_alias_canonical(alias_id, new_canonical):
    """Re-point a confirmed alias to a different canonical SKU (fixes a wrong mapping)."""
    try:
        conn = get_db()
        cur = conn.cursor()
        cur.execute('UPDATE sku_aliases SET canonical_sku = %s WHERE id = %s', (new_canonical, alias_id))
        conn.commit()
        cur.close()
        conn.close()
        return True
    except Exception as e:
        print(f"Update alias canonical error: {e}")
        return False

def rename_canonical_sku(old_canonical, new_canonical):
    """Rename every alias row under old_canonical to new_canonical. If new_canonical
    already exists as a different group (case-insensitive), merges into that group
    instead of creating a near-duplicate."""
    new_canonical = (new_canonical or '').strip()
    if not old_canonical or not new_canonical or old_canonical == new_canonical:
        return False
    existing = find_existing_canonical(new_canonical)
    target = existing if (existing and existing != old_canonical) else new_canonical
    try:
        conn = get_db()
        cur = conn.cursor()
        cur.execute('UPDATE sku_aliases SET canonical_sku = %s WHERE canonical_sku = %s', (target, old_canonical))
        conn.commit()
        cur.close()
        conn.close()
        return True
    except Exception as e:
        print(f"Rename canonical error: {e}")
        return False


# ── ADMIN HTML SAFETY HELPERS ────────────────────────────────────────────────
# SKUs come from OCR and can contain quotes, ampersands, etc. (e.g. 19" x 29" x 6).
# These must be escaped before being embedded in HTML attributes or onclick="..." JS
# string literals, or the markup breaks and buttons can misfire / navigate wrongly.

def esc_html(s):
    """Safe for HTML text content and double-quoted attributes."""
    return html_module.escape(str(s), quote=True)

def esc_js(s):
    """Safe for embedding inside a single-quoted JS string literal in onclick=\"...('...')\"."""
    return (str(s)
            .replace('\\', '\\\\')
            .replace("'", "\\'")
            .replace('"', '&quot;')
            .replace('\n', '\\n')
            .replace('<', '\\x3C'))


# ── ADMIN AUTH ────────────────────────────────────────────────────────────────

def admin_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        if not session.get('admin_logged_in'):
            return redirect('/admin/login')
        return f(*args, **kwargs)
    return decorated


# ── LABEL DETECTION ──────────────────────────────────────────────────────────

def is_royal_mail_label(page_image):
    text = pytesseract.image_to_string(page_image)
    return bool(re.search(r'Royal\s*Mail|Delivered\s+by|Post\s+by\s+the\s+end', text, re.IGNORECASE))

# ── QTY EXTRACTION ───────────────────────────────────────────────────────────

def extract_skus_on_page(page):
    text = pytesseract.image_to_string(page)
    table_match = re.search(
        r'(Quantity.*?Product\s+Details|Item\s+description.*?Qty|Shipment\s+details)',
        text, re.IGNORECASE
    )
    search_text = text[table_match.start():] if table_match else text
    sku_matches = re.findall(
        r'SKU[:\s]*([^\n]{1,50}?)(?:\s*\n|\s*ASIN|\s*Condition|\s*Sold)',
        search_text
    )
    return max(len(sku_matches), 1)

def find_qty_from_column(page):
    """Extract quantities using multiple methods. Returns (list, confident)."""
    text = pytesseract.image_to_string(page)

    # METHOD 1: Partial "Quant" header match then number in next row
    table_match = re.search(r'Quant[^\n]*\n([^\n]+)', text, re.IGNORECASE)
    if table_match:
        table_text = text[table_match.start():]
        rows = re.findall(r'\n\s*([1-9][0-9]?)\s+[A-Za-z£].*?£[\d.]+', table_text)
        if rows:
            return rows, True

    # METHOD 2: Number before product text and £ price
    matches = re.findall(r'(?:^|\n)\s*([1-9][0-9]?)\s+[A-Z£].*?£[\d]+\.[\d]+', text, re.MULTILINE)
    if matches:
        return matches, True

    # METHOD 3: Column position detection with fuzzy header
    try:
        data = pytesseract.image_to_data(page, output_type=pytesseract.Output.DICT)
        qty_header_x = None
        qty_header_y = None
        qty_header_h = 20
        for i, word in enumerate(data['text']):
            w = word.strip().lower()
            if re.match(r'quant', w) or w in ('qty', 'qty}', 'qty|'):
                qty_header_x = data['left'][i]
                qty_header_y = data['top'][i]
                qty_header_h = data['height'][i]
                break
        if qty_header_x is not None:
            col_x_min = max(0, qty_header_x - 20)
            col_x_max = qty_header_x + 100
            col_qtys = []
            for i, word in enumerate(data['text']):
                w = word.strip()
                if not w:
                    continue
                if (data['top'][i] > qty_header_y + qty_header_h and
                        col_x_min <= data['left'][i] <= col_x_max and
                        re.match(r'^[1-9][0-9]{0,2}$', w)):
                    col_qtys.append({'qty': w, 'y': data['top'][i]})
            col_qtys.sort(key=lambda x: x['y'])
            if col_qtys:
                return [q['qty'] for q in col_qtys], True
    except:
        pass

    return None, False


# ── PDF EXTRACTION ────────────────────────────────────────────────────────────

def extract_items_from_pdf(pdf_path):
    pages = convert_from_path(str(pdf_path), dpi=300)
    if len(pages) < 2:
        return [], '', False, False

    rm_label = is_royal_mail_label(pages[0])

    full_text = ''
    for p in pages[1:]:
        full_text += pytesseract.image_to_string(p) + '\n'

    is_business = bool(re.search(r'Amazon\s+[Bb]usiness|Packing\s+slip|Order\s+#:', full_text))
    # On Prime slips "/Prime" butts straight up against the last digit, and OCR
    # sometimes splits the digit run: "205-8954605-95651 19/Prime". Collapse any
    # space sitting between two digits before matching. Scoped to this lookup only
    # so SKU extraction below still sees the original full_text.
    order_text = re.sub(r'(?<=\d)[ \t]+(?=\d)', '', full_text)
    order_match = re.search(r'Order\s+(?:ID|#)[:\s#]*([0-9]{3}-[0-9]{7}-[0-9]{7})', order_text)
    order_id = order_match.group(1) if order_match else ''

    all_qtys = []
    qty_confident = True

    for p in pages[1:]:
        result, confident = find_qty_from_column(p)
        if result is None:
            n = extract_skus_on_page(p)
            all_qtys.extend(['1'] * n)
            qty_confident = False
        else:
            all_qtys.extend(result)
            if not confident:
                qty_confident = False

    table_start = re.search(
        r'(Quantity.*?Product\s+Details|Item\s+description.*?Qty|Shipment\s+details)',
        full_text, re.IGNORECASE
    )
    search_text = full_text[table_start.start():] if table_start else full_text

    sku_iter = list(re.finditer(
        r'SKU[:\s]*([^\n]{1,50}?)(?:\s*\n|\s*ASIN|\s*Condition|\s*Listing|\s*Sold\s+by|\s*Order\s+Item)',
        search_text
    ))
    if not sku_iter:
        sku_iter = list(re.finditer(r'SKU[:\s]*([^\n]{1,50})', search_text))

    items = []
    for idx, sku_match in enumerate(sku_iter):
        sku = sku_match.group(1).strip().rstrip(',').strip()
        sku = re.sub(r'\s*(Promotions|promotion|promo|free gift|gift)\s*$', '', sku, flags=re.IGNORECASE).strip()
        if not sku:
            continue

        if idx < len(all_qtys):
            qty = all_qtys[idx]
        else:
            pre = search_text[max(0, sku_match.start()-600):sku_match.start()]
            if is_business:
                qty_m = re.search(r'(?:^|\s)([1-9][0-9]{0,2})\s+£[\d.]+\s+£[\d.]+', pre, re.MULTILINE)
                qty = qty_m.group(1) if qty_m else '1'
            else:
                table_m = re.search(r'Quantity.*?Product\s+Details[^\n]*\n([^\n]+)', pre, re.IGNORECASE)
                if table_m:
                    row = table_m.group(1).strip()
                    qty_m = re.match(r'^([1-9][0-9]{0,2})\s+\w', row)
                    qty = qty_m.group(1) if qty_m else '1'
                else:
                    qty = '1'

        canonical_sku, was_mapped = get_canonical_sku(sku)
        item = {'sku': canonical_sku, 'qty': qty}
        if was_mapped:
            item['raw_sku'] = sku
        items.append(item)

    return items, order_id, rm_label, qty_confident


# ── OVERLAY FUNCTIONS ─────────────────────────────────────────────────────────

def create_evri_overlay(items, order_id, page_num, total_pages, batch_id, page_w, page_h, warn=False):
    packet = io.BytesIO()
    c = canvas.Canvas(packet, pagesize=(page_w, page_h))
    c.setFillColorRGB(0, 0, 0)

    start_y = page_h - 16
    min_y = page_h * 0.72
    available_h = start_y - min_y
    n = len(items)
    line_h = min(13, available_h / n) if n > 0 else 13
    font_size = 9
    # x=36 aligns with "Bury" text, gives more room away from QR code
    x_start = 36
    max_w = page_w * 0.50

    for i, item in enumerate(items):
        y = start_y - (i * line_h)
        text = str(item['qty']) + 'x  ' + item['sku']
        fs = font_size
        c.setFont('Helvetica', fs)
        while c.stringWidth(text, 'Helvetica', fs) > max_w and fs > 5:
            fs -= 0.5
        c.setFont('Helvetica', fs)
        c.drawString(x_start, y, text)

    if order_id:
        c.setFont('Helvetica-Bold', 8)
        c.drawString(page_w * 0.62, 82, order_id)

    c.setFont('Helvetica-Bold', 7)
    batch_text = str(page_num) + '/' + str(total_pages) + batch_id
    c.drawString(8, 8, batch_text)
    batch_w = c.stringWidth(batch_text, 'Helvetica-Bold', 7)
    c.setFont('Helvetica', 6)
    c.setFillColorRGB(0.4, 0.4, 0.4)
    c.drawString(8 + batch_w + 6, 8, WEBSITE_URL)
    c.setFillColorRGB(0, 0, 0)

    if warn:
        c.setFillColorRGB(1, 0.4, 0)
        c.setFont('Helvetica-Bold', 9)
        c.drawString(page_w * 0.62, page_h - 16, '⚠ CHECK QTY')
        c.setFillColorRGB(0, 0, 0)

    c.save()
    packet.seek(0)
    return packet


def create_royal_mail_overlay(items, order_id, page_num, total_pages, batch_id, page_w, page_h, warn=False):
    packet = io.BytesIO()
    c = canvas.Canvas(packet, pagesize=(page_w, page_h))
    c.setFillColorRGB(0, 0, 0)

    safe_top = page_h * 0.26
    safe_bot = page_h * 0.16
    available_h = safe_top - safe_bot

    n = max(len(items), 1)
    line_h = min(14, available_h / n)
    font_size = min(10, line_h * 0.78)
    font_size = max(font_size, 6)

    start_y = safe_top - 3
    for i, item in enumerate(items):
        y = start_y - (i * line_h)
        text = str(item['qty']) + 'x  ' + item['sku']
        fs = font_size
        c.setFont('Helvetica-Bold', fs)
        while c.stringWidth(text, 'Helvetica-Bold', fs) > page_w - 16 and fs > 5:
            fs -= 0.5
        c.setFont('Helvetica-Bold', fs)
        c.drawString(8, y, text)

    if order_id:
        c.setFont('Helvetica', 7)
        c.setFillColorRGB(0.3, 0.3, 0.3)
        c.drawString(page_w * 0.50, 10, order_id)

    c.setFont('Helvetica-Bold', 7)
    c.setFillColorRGB(0, 0, 0)
    batch_text = str(page_num) + '/' + str(total_pages) + batch_id
    c.drawString(8, 8, batch_text)
    batch_w = c.stringWidth(batch_text, 'Helvetica-Bold', 7)
    c.setFont('Helvetica', 6)
    c.setFillColorRGB(0.4, 0.4, 0.4)
    c.drawString(8 + batch_w + 6, 8, WEBSITE_URL)
    c.setFillColorRGB(0, 0, 0)

    if warn:
        c.setFillColorRGB(1, 0.4, 0)
        c.setFont('Helvetica-Bold', 9)
        c.drawString(8, safe_bot - 14, '⚠ CHECK QTY')
        c.setFillColorRGB(0, 0, 0)

    c.save()
    packet.seek(0)
    return packet


# ── PICK LIST ──────────────────────────────────────────────────────────────────

def build_pick_list(extracted):
    """Aggregate total quantity per SKU across the whole batch, so a picker
    can grab everything needed from stock before packing individual orders."""
    totals = {}
    for entry in extracted:
        for item in entry.get('items', []):
            sku = item.get('sku', '')
            if not sku or sku in ('NOT FOUND', 'ERROR'):
                continue
            try:
                qty = int(item.get('qty', 0))
            except (ValueError, TypeError):
                qty = 1  # non-numeric qty (e.g. '?') still counts as 1 unit
            totals[sku] = totals.get(sku, 0) + qty
    pick_list = []
    for sku, qty in sorted(totals.items(), key=lambda kv: kv[0].upper()):
        p_match = re.search(r'P(\d+)$', sku)
        total = int(p_match.group(1)) * qty if p_match else None
        pick_list.append({'sku': sku, 'qty': qty, 'total': total})
    return pick_list


def create_pick_list_page(pick_list, batch_id, total_orders, page_w=288, page_h=432):
    """Build a printable summary page (default 4x6, same size as the courier
    labels) listing total qty per SKU for the batch, as a ruled table.
    Automatically splits into side-by-side columns so the batch fits on one
    page where possible, only spilling to another page if it's too big even
    for that."""
    margin = 10
    left = margin
    right = page_w - margin
    avail_w = right - left
    row_h = 13
    qty_col_w = 22
    total_col_w = 28
    col_gap = 10
    min_col_w = 110  # below this, SKU text has no room left to breathe

    packet = io.BytesIO()
    c = canvas.Canvas(packet, pagesize=(page_w, page_h))

    printed_at = datetime.now(ZoneInfo('Europe/London')).strftime('%d %b %Y, %H:%M')

    def draw_page_header(remaining_note=None):
        c.setFillColorRGB(0, 0, 0)
        c.setFont('Helvetica-Bold', 13)
        c.drawString(left, page_h - 16, 'Pick List' + (remaining_note or ''))
        c.setFont('Helvetica', 7)
        c.drawString(left, page_h - 27, 'Batch ' + batch_id)
        c.drawRightString(right, page_h - 27, 'Printed ' + printed_at)
        total_items = sum(p['qty'] for p in pick_list)
        c.drawString(left, page_h - 37,
                     str(total_orders) + ' orders   ' + str(len(pick_list)) +
                     ' SKUs   ' + str(total_items) + ' items')
        return page_h - 50  # y where the column tables start

    def draw_col_header(x, col_w, y):
        divider2_x = x + col_w - total_col_w
        c.setFont('Helvetica-Bold', 7)
        c.drawString(x + 2, y - 9, 'QTY')
        c.drawString(x + qty_col_w + 4, y - 9, 'SKU')
        c.drawString(divider2_x + 3, y - 9, 'TOTAL')
        c.line(x, y - 13, x + col_w, y - 13)
        return y - 13

    table_top0 = page_h - 50
    avail_h = table_top0 - (margin + 4)
    max_rows_per_col = max(1, int(avail_h // row_h))
    max_cols_by_width = max(1, int((avail_w + col_gap) // (min_col_w + col_gap)))

    num_cols = 1
    if len(pick_list) > max_rows_per_col:
        num_cols = -(-len(pick_list) // max_rows_per_col)  # ceil division
        num_cols = min(num_cols, max_cols_by_width)
    col_w = (avail_w - (num_cols - 1) * col_gap) / num_cols
    rows_per_page = max_rows_per_col * num_cols

    idx = 0
    first_page = True
    while idx < len(pick_list):
        page_items = pick_list[idx: idx + rows_per_page]
        idx += len(page_items)
        table_top = draw_page_header(None if first_page else ' (cont.)')
        first_page = False

        chunk_size = -(-len(page_items) // num_cols)  # ceil, balances columns
        col_start = 0
        for col_idx in range(num_cols):
            col_items = page_items[col_start: col_start + chunk_size]
            col_start += chunk_size
            if not col_items:
                continue
            x = left + col_idx * (col_w + col_gap)
            divider1_x = x + qty_col_w
            divider2_x = x + col_w - total_col_w
            sku_x = divider1_x + 4
            sku_max_w = divider2_x - sku_x - 4
            y = draw_col_header(x, col_w, table_top)
            for item in col_items:
                row_bottom = y - row_h
                c.setFont('Helvetica-Bold', 8)
                c.drawString(x + 2, row_bottom + 4, str(item['qty']) + 'x')
                sku_text = item['sku']
                fs = 8
                while c.stringWidth(sku_text, 'Helvetica', fs) > sku_max_w and fs > 5:
                    fs -= 0.5
                c.setFont('Helvetica', fs)
                c.drawString(sku_x, row_bottom + 4, sku_text)
                total_val = item.get('total')
                if total_val is not None:
                    c.setFont('Helvetica-Bold', 8)
                    c.drawString(divider2_x + 3, row_bottom + 4, str(total_val))
                c.line(x, row_bottom, x + col_w, row_bottom)
                y = row_bottom
            c.rect(x, y, col_w, table_top - y, stroke=1, fill=0)
            c.line(divider1_x, table_top, divider1_x, y)
            c.line(divider2_x, table_top, divider2_x, y)

        if idx < len(pick_list):
            c.showPage()

    c.save()
    packet.seek(0)
    return packet


# ── JOB RUNNER ───────────────────────────────────────────────────────────────

def run_job(job_id, pdf_files, tmpdir):
    def update(progress, message):
        with jobs_lock:
            jobs[job_id]['progress'] = progress
            jobs[job_id]['message'] = message

    batch_id = get_next_batch_id()
    total = len(pdf_files)
    update(0, 'Batch ' + batch_id + ' — reading ' + str(total) + ' order(s)...')

    extracted = []
    for i, pdf_path in enumerate(pdf_files):
        fname = Path(pdf_path).name
        update(int((i / total) * 40), 'Reading ' + str(i+1) + '/' + str(total) + ': ' + fname)
        try:
            items, order_id, rm_label, qty_confident = extract_items_from_pdf(pdf_path)
            if not items:
                items = [{'sku': 'NOT FOUND', 'qty': '?'}]

            needs_check = not qty_confident

            extracted.append({
                'path': pdf_path, 'file': fname,
                'items': items, 'order_id': order_id,
                'rm_label': rm_label,
                'qty_confident': qty_confident,
                'needs_check': needs_check,
                'sort_key': items[0]['sku'].upper() if items else 'ZZZZ'
            })
        except Exception as e:
            extracted.append({
                'path': pdf_path, 'file': fname,
                'items': [{'sku': 'ERROR', 'qty': '?'}],
                'order_id': '', 'rm_label': False,
                'qty_confident': False, 'needs_check': False,
                'sort_key': 'ZZZZ', 'error': str(e)
            })

    update(45, 'Sorting by SKU...')
    extracted.sort(key=lambda x: (x['sort_key'], x['file']))

    pick_list = build_pick_list(extracted)

    writer = PdfWriter()
    if pick_list:
        label_w, label_h = 288, 432  # 4x6in fallback if the peek below fails
        try:
            peek_reader = PdfReader(str(extracted[0]['path']))
            label_w = float(peek_reader.pages[0].mediabox.width)
            label_h = float(peek_reader.pages[0].mediabox.height)
        except Exception:
            pass
        pick_list_buf = create_pick_list_page(pick_list, batch_id, len(extracted), label_w, label_h)
        for pg in PdfReader(pick_list_buf).pages:
            writer.add_page(pg)

    results = []
    total_pages = len(extracted)

    for i, entry in enumerate(extracted):
        page_num = i + 1
        update(45 + int((i / total) * 50),
               'Stamping ' + str(page_num) + '/' + str(total_pages) + ' [' + batch_id + ']: ' + entry['file'])
        try:
            reader = PdfReader(str(entry['path']))
            label_page = reader.pages[0]
            pw = float(label_page.mediabox.width)
            ph = float(label_page.mediabox.height)
            warn = entry.get('needs_check', False)

            if entry['rm_label']:
                overlay_buf = create_royal_mail_overlay(
                    entry['items'], entry['order_id'],
                    page_num, total_pages, batch_id, pw, ph, warn=warn)
            else:
                overlay_buf = create_evri_overlay(
                    entry['items'], entry['order_id'],
                    page_num, total_pages, batch_id, pw, ph, warn=warn)

            overlay_reader = PdfReader(overlay_buf)
            label_page.merge_page(overlay_reader.pages[0])
            writer.add_page(label_page)

            warn_reason = []
            if not entry['qty_confident']:
                warn_reason.append('qty unconfirmed')

            results.append({
                'file': entry['file'], 'status': 'ok',
                'items': entry['items'], 'order_id': entry['order_id'],
                'page': page_num, 'batch': batch_id,
                'carrier': 'Royal Mail' if entry['rm_label'] else 'Evri',
                'needs_check': warn,
                'warn_reason': ' | '.join(warn_reason) if warn_reason else None
            })
        except Exception as e:
            results.append({'file': entry['file'], 'status': 'error', 'error': str(e),
                           'needs_check': False, 'warn_reason': None})

    update(95, 'Saving PDF...')
    out_path = os.path.join(tmpdir, 'labels_batch' + batch_id + '_' + job_id + '.pdf')
    with open(out_path, 'wb') as f:
        writer.write(f)

    ok_count = len([r for r in results if r['status'] == 'ok'])
    warn_count = len([r for r in results if r.get('needs_check')])
    ts = datetime.now(ZoneInfo('Europe/London')).strftime('%Y-%m-%d_%H%M')
    download_name = 'labels_batch' + batch_id + '_' + ts + '.pdf'

    with open(out_path, 'rb') as f:
        save_label_file(job_id, 'amazon', batch_id, download_name, f.read())
    save_pick_list_entries(job_id, 'amazon', batch_id, pick_list)

    with jobs_lock:
        jobs[job_id]['status'] = 'done'
        jobs[job_id]['progress'] = 100
        msg = 'Batch ' + batch_id + ' done — ' + str(ok_count) + '/' + str(total_pages) + ' labels merged'
        if warn_count:
            msg += ' — ⚠ ' + str(warn_count) + ' need checking'
        jobs[job_id]['message'] = msg
        jobs[job_id]['result_path'] = out_path
        jobs[job_id]['results'] = results
        jobs[job_id]['batch_id'] = batch_id
        jobs[job_id]['download_name'] = download_name
        jobs[job_id]['pick_list'] = pick_list


# ── 3RD-PARTY LABELS ──────────────────────────────────────────────────────────
# These are pre-made labels (e.g. Amazon Buy-Shipping / marketplace tools) that
# ALREADY carry SKU + qty printed in a strip below a 4x6 Evri label, on an
# oversized 4x8 page. Unlike the Amazon flow there is no packing slip to OCR —
# the SKU/qty is read straight from the label's text layer. We crop the page
# back to a true 4x6 and move the SKU/qty up into the empty band under the
# datamatrix so nothing is wasted. Kept fully separate from the Amazon pipeline
# so the two formats never share coordinates.

# Empty band inside the 3rd-party Evri label, as fractions of a 4x6 page height
# (measured on real labels: ~top 128–182pt on a 432pt-tall page).
TP_BAND_TOP_FRAC = 0.701
TP_BAND_BOT_FRAC = 0.581


def extract_thirdparty_items(plumb_page):
    """Read every SKU + qty row from the strip *below* the 4x6 label region.
    Returns a list of (sku, qty). Handles multiple line items per label."""
    label_h = plumb_page.width * 1.5          # 4x6 label occupies the top of the page
    words = [w for w in plumb_page.extract_words() if w['top'] > label_h + 2]
    if not words:
        return []
    rows = {}
    for w in words:
        rows.setdefault(round(w['top'] / 3.0), []).append(w)   # ~3pt row buckets
    items = []
    qty_x_gate = plumb_page.width * 0.6       # qty lives in the right column
    for key in sorted(rows):
        rw = sorted(rows[key], key=lambda w: w['x0'])
        texts_lower = [w['text'].strip().lower() for w in rw]
        if 'sku' in texts_lower and any(t in ('qty', 'quantity') for t in texts_lower):
            continue                          # header row
        qty = ''
        sku_parts = []
        for w in rw:
            t = w['text'].strip()
            if re.fullmatch(r'[0-9]{1,3}', t) and w['x0'] > qty_x_gate:
                qty = t
            else:
                sku_parts.append(t)
        sku = ' '.join(sku_parts).strip()
        if sku:
            items.append((sku, qty or '1'))
    return items


def create_thirdparty_overlay(items, page_w, page_h):
    """Compact SKU/qty box drawn into the empty band inside the label.
    No header; one row per SKU; grows downward and auto-shrinks to fit the band."""
    packet = io.BytesIO()
    c = canvas.Canvas(packet, pagesize=(page_w, page_h))
    if not items:
        c.save(); packet.seek(0); return packet

    FONT = 'Helvetica-Bold'
    band_top = page_h * TP_BAND_TOP_FRAC
    band_bot = page_h * TP_BAND_BOT_FRAC
    band_h = band_top - band_bot
    bx0 = 8.0
    width_cap = page_w - 8.0
    n = max(len(items), 1)
    pad = 3.0
    gap = 12.0

    def total_h(fs):
        return pad + n * (fs + 2.2) + pad

    row_fs = 8.0
    for fs in (8.0, 7.5, 7.0, 6.5, 6.0, 5.5):
        row_fs = fs
        if total_h(fs) <= band_h:
            break
    lh = row_fs + 2.2
    th = min(total_h(row_fs), band_h)

    def cols(fs):
        msku = max((c.stringWidth(s, FONT, fs) for s, _ in items), default=40)
        mqty = max((c.stringWidth(str(q), FONT, fs) for _, q in items), default=8)
        return msku, mqty

    msku, mqty = cols(row_fs)
    avail = width_cap - bx0 - pad * 2 - gap - mqty
    while row_fs > 5.0 and msku > avail:
        row_fs -= 0.5
        lh = row_fs + 2.2
        msku, mqty = cols(row_fs)
        avail = width_cap - bx0 - pad * 2 - gap - mqty

    bw = max(min(pad + msku + gap + mqty + pad, width_cap - bx0), 110)
    bx1 = bx0 + bw
    by1 = band_top
    by0 = by1 - th

    c.setLineWidth(0.8)
    c.setFillColorRGB(0.94, 0.94, 0.94)
    c.rect(bx0, by0, bw, th, stroke=1, fill=1)
    c.setFillColorRGB(0, 0, 0)
    c.setFont(FONT, row_fs)
    ry = by1 - pad - row_fs
    for s, q in items:
        c.drawString(bx0 + pad, ry, s)
        c.drawRightString(bx1 - pad, ry, str(q))
        ry -= lh

    c.save()
    packet.seek(0)
    return packet


def process_thirdparty(job_id, pdf_files, tmpdir):
    """Job runner for the 3rd-party tab: one page = one finished label."""
    def update(progress, message):
        with jobs_lock:
            jobs[job_id]['progress'] = progress
            jobs[job_id]['message'] = message

    update(0, 'Reading 3rd-party labels...')
    run_label = datetime.now(ZoneInfo('Europe/London')).strftime('%H%M')

    # 1. collect every page across all uploaded PDFs + read its SKU/qty,
    #    then map each raw SKU through the shared alias/canonical system
    #    (same confirmed-alias table + unmapped queue as the Amazon flow).
    #    Also read the postcode off the label so Highlands/Islands/Channel
    #    Islands (out-of-area) orders can be pulled before they're merged.
    page_entries = []
    for path in pdf_files:
        try:
            with pdfplumber.open(path) as plumb:
                # The Destination box on these labels is part of a flattened
                # image (no text layer) — render once per file so the postcode
                # check below can OCR just the address crop of each page.
                page_images = render_pdf_pages(path)
                for pidx in range(len(plumb.pages)):
                    plumb_page = plumb.pages[pidx]
                    try:
                        raw_items = extract_thirdparty_items(plumb_page)
                    except Exception:
                        raw_items = []
                    items = []
                    for raw_sku, qty in raw_items:
                        canonical_sku, was_mapped = get_canonical_sku(raw_sku)
                        it = {'sku': canonical_sku, 'qty': qty}
                        if was_mapped:
                            it['raw_sku'] = raw_sku
                        items.append(it)
                    try:
                        page_text = plumb_page.extract_text() or ''
                    except Exception:
                        page_text = ''
                    page_img = page_images[pidx] if pidx < len(page_images) else None
                    page_entries.append({
                        'path': path, 'index': pidx, 'items': items,
                        'postcode': check_label_postcode(page_text, page_img),
                        'sort_key': items[0]['sku'].upper() if items else 'ZZZZ'
                    })
        except Exception as e:
            page_entries.append({'path': path, 'index': 0, 'items': [], 'error': str(e),
                                  'postcode': None, 'sort_key': 'ZZZZ'})

    # 2. split off anything that failed to open, is confirmed out-of-area, or
    #    has no readable postcode — none of these should reach the merged PDF.
    error_entries = [e for e in page_entries if e.get('error')]
    excluded_entries = [e for e in page_entries if not e.get('error') and e['postcode']['exclude']]
    included_entries = [e for e in page_entries if not e.get('error') and not e['postcode']['exclude']]
    total_labels = max(len(page_entries), 1)

    update(35, 'Sorting by SKU...')
    included_entries.sort(key=lambda e: e['sort_key'])

    pick_list = build_pick_list(included_entries)

    writer = PdfWriter()

    # peek the first included label's real dimensions for the pick-list page
    label_w, label_h = 288, 432
    if included_entries:
        try:
            peek_reader = PdfReader(str(included_entries[0]['path']))
            peek_page = peek_reader.pages[included_entries[0]['index']]
            pw0 = float(peek_page.mediabox.width)
            ph0 = float(peek_page.mediabox.height)
            target_h0 = pw0 * 1.5
            if ph0 <= target_h0 + 2:
                target_h0 = ph0
            label_w, label_h = pw0, target_h0
        except Exception:
            pass

    if pick_list:
        pick_list_buf = create_pick_list_page(pick_list, run_label, len(included_entries), label_w, label_h)
        for pg in PdfReader(pick_list_buf).pages:
            writer.add_page(pg)

    results = []

    # 3. crop + stamp only the included labels, now in SKU order
    for i, ent in enumerate(included_entries):
        update(40 + int((i / max(len(included_entries), 1)) * 55),
               'Formatting ' + str(i + 1) + '/' + str(len(included_entries)))
        fname = Path(ent['path']).name
        try:
            reader = PdfReader(str(ent['path']))
            page = reader.pages[ent['index']]
            pw = float(page.mediabox.width)
            ph = float(page.mediabox.height)
            target_h = pw * 1.5                       # true 4x6 height for this width
            shift = ph - target_h if ph > target_h + 2 else 0.0
            if shift < 0:
                shift = 0.0
                target_h = ph

            new_page = PageObject.create_blank_page(width=pw, height=target_h)
            new_page.merge_transformed_page(page, Transformation().translate(0, -shift))
            if ent['items']:
                overlay_rows = [(it['sku'], it['qty']) for it in ent['items']]
                ov = create_thirdparty_overlay(overlay_rows, pw, target_h)
                new_page.merge_page(PdfReader(ov).pages[0])
            writer.add_page(new_page)

            has_sku = bool(ent['items'])
            results.append({
                'file': fname, 'status': 'ok',
                'items': ent['items'] or [{'sku': '(no SKU on label)', 'qty': '?'}],
                'order_id': '', 'page': i + 1, 'batch': run_label,
                'carrier': 'Evri · 3rd-party',
                'needs_check': not has_sku,
                'postcode': ent['postcode']['postcode'],
                'warn_reason': None if has_sku else 'no SKU found on label'
            })
        except Exception as e:
            results.append({'file': fname, 'status': 'error', 'error': str(e),
                            'needs_check': False, 'warn_reason': None})

    # 4. flagged/unreadable-postcode labels never enter the merge — surfaced
    #    here instead so they can be found and cancelled on Amazon.
    for ent in excluded_entries:
        fname = Path(ent['path']).name
        pc = ent['postcode']
        results.append({
            'file': fname, 'status': 'excluded',
            'items': ent['items'] or [{'sku': '(no SKU on label)', 'qty': '?'}],
            'order_id': '', 'page': None, 'batch': '',
            'carrier': 'Evri · 3rd-party',
            'needs_check': True,
            'postcode': pc['postcode'],
            'postcode_flagged': pc['flagged'],
            'warn_reason': pc['reason']
        })

    for ent in error_entries:
        fname = Path(ent['path']).name
        results.append({'file': fname, 'status': 'error', 'error': ent['error'],
                        'needs_check': False, 'warn_reason': None})

    update(95, 'Saving PDF...')
    out_path = os.path.join(tmpdir, 'labels_4x6_' + job_id + '.pdf')
    with open(out_path, 'wb') as f:
        writer.write(f)

    ok_count = len([r for r in results if r['status'] == 'ok'])
    warn_count = len([r for r in results if r['status'] == 'ok' and r.get('needs_check')])
    out_of_area_count = len([r for r in results if r['status'] == 'excluded' and r.get('postcode_flagged')])
    check_pc_count = len([r for r in results if r['status'] == 'excluded' and not r.get('postcode_flagged')])
    ts = datetime.now(ZoneInfo('Europe/London')).strftime('%Y-%m-%d_%H%M')
    download_name = 'labels_4x6_' + ts + '.pdf'

    with open(out_path, 'rb') as f:
        save_label_file(job_id, 'thirdparty', run_label, download_name, f.read())
    save_pick_list_entries(job_id, 'thirdparty', run_label, pick_list)

    with jobs_lock:
        jobs[job_id]['status'] = 'done'
        jobs[job_id]['progress'] = 100
        msg = str(ok_count) + '/' + str(total_labels) + ' labels resized to 4×6'
        if warn_count:
            msg += ' — ⚠ ' + str(warn_count) + ' had no SKU'
        if out_of_area_count:
            msg += ' — 🚫 ' + str(out_of_area_count) + ' out of area'
        if check_pc_count:
            msg += ' — ⚠ ' + str(check_pc_count) + ' need postcode check'
        jobs[job_id]['message'] = msg
        jobs[job_id]['result_path'] = out_path
        jobs[job_id]['results'] = results
        jobs[job_id]['batch_id'] = run_label
        jobs[job_id]['download_name'] = download_name
        jobs[job_id]['pick_list'] = pick_list


# ── ROUTES ────────────────────────────────────────────────────────────────────

@app.route('/')
def index():
    return render_template('index.html')

@app.route('/upload', methods=['POST'])
def upload():
    cleanup_old_label_files()
    job_id = str(uuid.uuid4())[:8]
    tmpdir = tempfile.mkdtemp()
    pdf_files = []

    mode = request.form.get('mode', 'amazon')

    uploaded = request.files.getlist('files') or request.files.getlist('file')
    if not uploaded:
        return jsonify({'error': 'No file uploaded'}), 400
    for f in uploaded:
        if f.filename.endswith('.zip'):
            zip_path = os.path.join(tmpdir, 'upload.zip')
            f.save(zip_path)
            with zipfile.ZipFile(zip_path) as z:
                for name in z.namelist():
                    if name.lower().endswith('.pdf') and not name.startswith('__'):
                        z.extract(name, tmpdir)
                        pdf_files.append(os.path.join(tmpdir, name))
        elif f.filename.endswith('.pdf'):
            pdf_path = os.path.join(tmpdir, f.filename)
            f.save(pdf_path)
            pdf_files.append(pdf_path)
    if not pdf_files:
        return jsonify({'error': 'No PDF files found in upload'}), 400

    with jobs_lock:
        jobs[job_id] = {
            'status': 'processing', 'progress': 0,
            'message': 'Starting — ' + str(len(pdf_files)) + ' PDF(s) found...',
            'result_path': None, 'results': [], 'batch_id': '', 'download_name': 'merged_labels.pdf'
        }
    target = process_thirdparty if mode == 'thirdparty' else run_job
    t = threading.Thread(target=target, args=(job_id, pdf_files, tmpdir))
    t.daemon = True
    t.start()
    return jsonify({'job_id': job_id, 'total': len(pdf_files)})

@app.route('/status/<job_id>')
def status(job_id):
    with jobs_lock:
        job = jobs.get(job_id)
    if not job:
        return jsonify({'error': 'Job not found'}), 404
    return jsonify(job)

@app.route('/download/<job_id>')
def download(job_id):
    # Served from the DB, not the (ephemeral) filesystem or the in-memory
    # jobs dict, so downloads keep working for 2 days even across app
    # restarts/redeploys — see label_files / cleanup_old_label_files().
    try:
        conn = get_db()
        cur = conn.cursor()
        cur.execute('SELECT filename, file_data FROM label_files WHERE job_id = %s', (job_id,))
        row = cur.fetchone()
        cur.close()
        conn.close()
    except Exception as e:
        return jsonify({'error': str(e)}), 500
    if not row:
        return jsonify({'error': 'Not ready, or this file has expired (labels are kept for 2 days)'}), 404
    filename, file_data = row
    return send_file(io.BytesIO(bytes(file_data)), as_attachment=True,
                     download_name=filename, mimetype='application/pdf')

@app.route('/label-history')
def label_history():
    """Every currently-retained label file (2-day rolling window, oldest
    already swept out by cleanup_old_label_files), most recent first — this
    is what the front-page "Recent Label Files" list reads from."""
    try:
        conn = get_db()
        cur = conn.cursor(cursor_factory=RealDictCursor)
        cur.execute('''
            SELECT job_id, tab, batch_id, filename, created_at
            FROM label_files
            ORDER BY created_at DESC
            LIMIT 100
        ''')
        rows = cur.fetchall()
        cur.close()
        conn.close()
    except Exception as e:
        return jsonify({'error': str(e)}), 500
    return jsonify([{
        'job_id': r['job_id'],
        'tab': r['tab'],
        'batch_id': r['batch_id'],
        'filename': r['filename'],
        'created_at': r['created_at'].isoformat() if r['created_at'] else None,
    } for r in rows])


# ── ADMIN ROUTES ──────────────────────────────────────────────────────────────

@app.route('/admin/login', methods=['GET', 'POST'])
def admin_login():
    error = ''
    if request.method == 'POST':
        if request.form.get('password') == ADMIN_PASSWORD:
            session['admin_logged_in'] = True
            return redirect('/admin')
        error = 'Wrong password'
    return '''
    <!DOCTYPE html>
    <html><head><title>Admin Login</title>
    <style>
      body { font-family: sans-serif; background: #f5f4f0; display: flex; align-items: center; justify-content: center; min-height: 100vh; margin: 0; }
      .box { background: white; padding: 2rem; border-radius: 10px; box-shadow: 0 2px 8px rgba(0,0,0,0.1); width: 320px; }
      h2 { margin-bottom: 1.5rem; font-size: 1.2rem; }
      input { width: 100%; padding: 10px; border: 1px solid #ddd; border-radius: 6px; margin-bottom: 1rem; box-sizing: border-box; font-size: 14px; }
      button { width: 100%; padding: 10px; background: #1a1916; color: white; border: none; border-radius: 6px; cursor: pointer; font-size: 14px; }
      .err { color: red; font-size: 13px; margin-bottom: 1rem; }
    </style></head>
    <body><div class="box">
      <h2>🔐 Admin Login</h2>
      ''' + (f'<div class="err">{error}</div>' if error else '') + '''
      <form method="POST">
        <input type="password" name="password" placeholder="Password" autofocus>
        <button type="submit">Login</button>
      </form>
    </div></body></html>
    '''

@app.route('/admin/logout')
def admin_logout():
    session.pop('admin_logged_in', None)
    return redirect('/admin/login')

def render_group_html(g_idx, canonical, variants):
    """Render a single confirmed-alias group's HTML (used both for full page render and AJAX patches).
    Compact grid-cell card: canonical name + add button on top, variant chips wrap below (hover reveals delete ×)."""
    canonical_safe = esc_html(canonical)
    canonical_search = esc_html(canonical.lower())
    variant_chips = ''
    for v in variants:
        raw_safe = esc_html(v['raw_sku'])
        title_safe = esc_html(f"seen {v['times_seen']}×, last {str(v['last_seen'])[:10]}")
        variant_chips += f'''
            <span class="variant-chip" id="variant-{v['id']}" data-sku="{raw_safe}" title="{title_safe}">
              <span class="raw-sku-text">{raw_safe}</span>
              <button class="variant-x" onclick="deleteAlias({v['id']}, this)" title="Remove this mapping" aria-label="Remove mapping for {raw_safe}">✕</button>
            </span>'''
    group_search = canonical_search + ' ' + ' '.join(esc_html(v['raw_sku'].lower()) for v in variants)
    return f'''
        <div class="alias-group" id="group-{g_idx}" data-search="{group_search}" data-canonical="{canonical_safe}"
             ondragover="onGroupDragOver(event)" ondragleave="onGroupDragLeave(event)" ondrop="onGroupDrop(event, this)">
          <div class="group-top-row">
            <span class="canonical-name" title="{canonical_safe}">{canonical_safe}</span>
            <button class="rename-btn" onclick="renameCanonical(event, this)" title="Rename this canonical SKU">✎</button>
            <button class="add-here-btn" onclick="addSelectedToGroup(event, this)" title="Add currently selected SKUs to this group">+ Add</button>
          </div>
          <span class="variant-chips">{variant_chips}</span>
        </div>'''




@app.route('/admin/export-weights.csv')
@admin_required
def export_weights_csv():
    """One-off export of the orphaned sku_weights table (kept from before the
    weight-validation system was removed; data was never deleted)."""
    try:
        conn = get_db()
        cur = conn.cursor(cursor_factory=RealDictCursor)
        cur.execute('SELECT sku, typical_weight, count, updated_at FROM sku_weights ORDER BY sku')
        rows = cur.fetchall()
        cur.close()
        conn.close()
    except Exception as e:
        return jsonify({'error': str(e)}), 500

    output = io.StringIO()
    writer = csv.writer(output)
    writer.writerow(['sku', 'typical_weight', 'count', 'updated_at'])
    for r in rows:
        writer.writerow([r['sku'], r['typical_weight'], r['count'], r['updated_at']])

    return Response(
        output.getvalue(),
        mimetype='text/csv',
        headers={'Content-Disposition': 'attachment; filename=sku_weights_export.csv'}
    )


def _week_bounds(week_str):
    """Parse 'YYYY-Www' (ISO week) into (monday_midnight, next_monday_midnight)
    in Europe/London. Falls back to the current week if missing/invalid."""
    tz = ZoneInfo('Europe/London')
    try:
        year_str, w_str = week_str.split('-W')
        monday = datetime.fromisocalendar(int(year_str), int(w_str), 1).replace(tzinfo=tz)
    except Exception:
        now = datetime.now(tz)
        iso = now.isocalendar()
        monday = datetime.fromisocalendar(iso[0], iso[1], 1).replace(tzinfo=tz)
    return monday, monday + timedelta(days=7)


def _pick_list_totals_query(monday, next_monday, tab_filter):
    conn = get_db()
    cur = conn.cursor(cursor_factory=RealDictCursor)
    query = '''
        SELECT sku, SUM(qty) AS total_qty, COUNT(DISTINCT job_id) AS batches
        FROM pick_list_entries
        WHERE created_at >= %s AND created_at < %s
    '''
    params = [monday, next_monday]
    if tab_filter in ('amazon', 'thirdparty'):
        query += ' AND tab = %s'
        params.append(tab_filter)
    query += ' GROUP BY sku ORDER BY total_qty DESC'
    cur.execute(query, params)
    rows = cur.fetchall()
    cur.close()
    conn.close()
    return rows


@app.route('/admin/pick-list-totals')
@admin_required
def pick_list_totals():
    """Weekly totals across every pick list ever generated (Amazon Orders +
    3rd-Party tabs), so you can see how many of each SKU actually went out
    in a given week. Data comes from pick_list_entries, which is written
    every time a batch finishes and is never auto-deleted."""
    week_str = request.args.get('week', '')
    tab_filter = request.args.get('tab', 'all')
    monday, next_monday = _week_bounds(week_str)
    current_week_str = f'{monday.isocalendar()[0]}-W{monday.isocalendar()[1]:02d}'
    prev_monday = monday - timedelta(days=7)
    next_monday_nav = monday + timedelta(days=7)
    prev_week_str = f'{prev_monday.isocalendar()[0]}-W{prev_monday.isocalendar()[1]:02d}'
    next_week_str = f'{next_monday_nav.isocalendar()[0]}-W{next_monday_nav.isocalendar()[1]:02d}'

    try:
        rows = _pick_list_totals_query(monday, next_monday, tab_filter)
    except Exception as e:
        return jsonify({'error': str(e)}), 500

    total_units = sum(r['total_qty'] for r in rows)
    rows_html = ''.join(
        f'<tr><td>{esc_html(r["sku"])}</td><td>{r["total_qty"]}</td><td>{r["batches"]}</td></tr>'
        for r in rows
    )
    week_label = f"{monday.strftime('%d %b %Y')} \u2013 {(next_monday - timedelta(days=1)).strftime('%d %b %Y')}"

    def tab_link(t, label):
        style = ' style="font-weight:bold;text-decoration:underline;"' if tab_filter == t else ''
        return f'<a href="/admin/pick-list-totals?week={current_week_str}&tab={t}"{style}>{label}</a>'

    return f'''<!DOCTYPE html>
    <html><head><title>Pick List Totals</title>
    <style>
      body {{ font-family: sans-serif; background: #f5f4f0; margin: 0; padding: 2rem; }}
      h1 {{ font-size: 1.4rem; margin-bottom: 0.5rem; }}
      .sub {{ color: #666; font-size: 13px; margin-bottom: 1.5rem; }}
      table {{ border-collapse: collapse; width: 100%; max-width: 640px; background: #fff; }}
      th, td {{ text-align: left; padding: 8px 12px; border-bottom: 1px solid #e5e3de; font-size: 14px; }}
      th {{ background: #efece5; }}
      .nav a, .tabs a {{ margin-right: 16px; color: #2563eb; text-decoration: none; }}
      .nav a:hover, .tabs a:hover {{ text-decoration: underline; }}
      .total-row td {{ font-weight: bold; border-top: 2px solid #333; }}
    </style></head>
    <body>
      <h1>Pick List Totals \u2014 week of {week_label}</h1>
      <div class="sub">{total_units} total units across {len(rows)} SKUs this week</div>
      <div class="nav">
        <a href="/admin/pick-list-totals?week={prev_week_str}&tab={tab_filter}">&larr; Previous week</a>
        <a href="/admin/pick-list-totals?week={current_week_str}&tab={tab_filter}">This week</a>
        <a href="/admin/pick-list-totals?week={next_week_str}&tab={tab_filter}">Next week &rarr;</a>
      </div>
      <div class="tabs" style="margin-bottom:1rem;">
        {tab_link('all', 'All')} {tab_link('amazon', 'Amazon Orders')} {tab_link('thirdparty', '3rd-Party')}
        &nbsp;|&nbsp; <a href="/admin/pick-list-totals.csv?week={current_week_str}&tab={tab_filter}">Download CSV</a>
      </div>
      <table>
        <tr><th>SKU</th><th>Total Qty</th><th>Batches</th></tr>
        {rows_html}
        <tr class="total-row"><td>Total</td><td>{total_units}</td><td>\u2014</td></tr>
      </table>
      <p><a href="/admin">&larr; Back to admin</a></p>
    </body></html>'''


@app.route('/admin/pick-list-totals.csv')
@admin_required
def pick_list_totals_csv():
    week_str = request.args.get('week', '')
    tab_filter = request.args.get('tab', 'all')
    monday, next_monday = _week_bounds(week_str)

    try:
        rows = _pick_list_totals_query(monday, next_monday, tab_filter)
    except Exception as e:
        return jsonify({'error': str(e)}), 500

    output = io.StringIO()
    writer = csv.writer(output)
    writer.writerow(['sku', 'total_qty', 'batches'])
    for r in rows:
        writer.writerow([r['sku'], r['total_qty'], r['batches']])

    iso = monday.isocalendar()
    fname = f'pick_list_totals_{iso[0]}-W{iso[1]:02d}.csv'
    return Response(
        output.getvalue(),
        mimetype='text/csv',
        headers={'Content-Disposition': f'attachment; filename={fname}'}
    )


@app.route('/admin')
@admin_required
def admin():
    unmapped = get_unmapped_skus()
    unmapped_html = ''
    all_canonicals_for_options = sorted(get_all_aliases().keys())
    datalist_html = ''.join(f'<option value="{esc_html(c)}">' for c in all_canonicals_for_options)
    for u in unmapped:
        raw_safe = esc_html(u['raw_sku'])
        search_safe = esc_html(u['raw_sku'].lower())
        unmapped_html += f'''
        <div class="sku-chip" id="unmapped-{u['normalized_key']}" draggable="true"
             data-key="{u['normalized_key']}" data-raw="{raw_safe}"
             data-search="{search_safe}"
             ondragstart="onChipDragStart(event)"
             onclick="toggleSelect(event, '{u['normalized_key']}', '{raw_safe}')">
          <span class="raw-sku">{raw_safe}</span>
          <span class="seen-count">{u['times_seen']}×</span>
          <button class="chip-x" onclick="dismissUnmapped(event, '{u['normalized_key']}')" title="Dismiss — this is its own item" aria-label="Dismiss">✕</button>
        </div>'''

    grouped = get_all_aliases()
    groups_html = ''
    for g_idx, (canonical, variants) in enumerate(grouped.items()):
        groups_html += render_group_html(g_idx, canonical, variants)

    return f'''<!DOCTYPE html>
    <html><head><title>Admin</title>
    <style>
      body {{ font-family: sans-serif; background: #f5f4f0; margin: 0; padding: 2rem; }}
      h1 {{ font-size: 1.4rem; margin-bottom: 0.5rem; }}
      .sub {{ color: #666; font-size: 13px; margin-bottom: 1.5rem; }}
      table {{ width: 100%; border-collapse: collapse; background: white; border-radius: 10px; overflow: hidden; box-shadow: 0 1px 4px rgba(0,0,0,0.1); }}
      th {{ background: #1a1916; color: white; padding: 10px 14px; text-align: left; font-size: 12px; text-transform: uppercase; letter-spacing: 0.05em; }}
      td {{ padding: 10px 14px; border-bottom: 1px solid #f0efe8; font-size: 13px; }}
      tr:last-child td {{ border-bottom: none; }}
      tr:hover td {{ background: #fafaf8; }}
      .nav {{ display: flex; gap: 12px; margin-bottom: 1.5rem; align-items: center; }}
      .btn {{ padding: 8px 16px; background: #1a1916; color: white; border: none; border-radius: 6px; cursor: pointer; font-size: 13px; text-decoration: none; display: inline-block; }}
      .msg {{ padding: 10px 14px; background: #dcfce7; color: #166534; border-radius: 6px; margin-bottom: 1rem; display: none; font-size: 13px; }}
      .tabs {{ display: flex; gap: 4px; margin-bottom: 1.5rem; border-bottom: 2px solid #e5e3da; }}
      .tab {{ padding: 8px 16px; cursor: pointer; font-size: 13px; font-weight: 600; color: #888; border-bottom: 2px solid transparent; margin-bottom: -2px; }}
      .tab.active {{ color: #1a1916; border-bottom-color: #1a1916; }}
      .panel {{ display: none; }}
      .panel.active {{ display: block; }}
      .search-box {{ width: 100%; padding: 10px 14px; border: 1px solid #ddd; border-radius: 8px; font-size: 13px; box-sizing: border-box; margin-bottom: 1.2rem; }}
      .section-label {{ font-size: 12px; font-weight: 700; text-transform: uppercase; letter-spacing: 0.04em; color: #888; margin: 0 0 8px; }}
      .unmapped-row {{ display: flex; align-items: center; gap: 8px; padding: 8px 12px; background: #fef3c7; border-radius: 6px; margin-bottom: 6px; font-size: 13px; }}
      .raw-sku {{ font-weight: 600; flex: 1; }}
      .seen-count {{ font-size: 11px; color: #888; white-space: nowrap; }}
      .hint {{ font-size: 12px; color: #999; margin: -4px 0 10px; }}
      .chip-pool {{ display: flex; flex-wrap: wrap; gap: 8px; min-height: 20px; }}
      .sku-chip {{ display: flex; align-items: center; gap: 6px; padding: 7px 10px; background: #fef3c7; border: 1px solid #f5d889; border-radius: 8px; font-size: 13px; cursor: pointer; user-select: none; }}
      .sku-chip.selected {{ background: #dcfce7; border-color: #166534; box-shadow: 0 0 0 1px #166534 inset; }}
      .sku-chip.selected .seen-count {{ color: #166534; }}
      .sku-chip:active {{ cursor: grabbing; }}
      .sku-chip.dragging {{ opacity: 0.4; }}
      .sku-chip .raw-sku {{ font-weight: 600; }}
      .sku-chip .seen-count {{ font-size: 10px; color: #92400e; background: rgba(255,255,255,0.5); padding: 1px 6px; border-radius: 10px; }}
      .chip-x {{ border: none; background: none; cursor: pointer; color: #92400e; font-size: 13px; padding: 0 2px; line-height: 1; opacity: 0.6; }}
      .chip-x:hover {{ opacity: 1; }}
      .staging-tray {{ border: 2px dashed #ccc8b8; border-radius: 10px; padding: 14px; margin-bottom: 1.2rem; background: #fafaf8; transition: background 0.15s, border-color 0.15s; }}
      .staging-tray.drag-over {{ background: #eef6ee; border-color: #166534; }}
      .tray-label {{ font-size: 12px; color: #999; margin: 0 0 8px; }}
      .tray-chips {{ display: flex; flex-wrap: wrap; gap: 8px; min-height: 24px; align-items: center; }}
      .tray-empty {{ font-size: 12px; color: #aaa; font-style: italic; }}
      .tray-chips .sku-chip {{ background: #dcfce7; border-color: #86efac; }}
      .tray-chips .sku-chip .seen-count {{ color: #166534; }}
      .tray-chips .chip-x {{ color: #166534; }}
      .tray-master-row {{ margin-top: 12px; padding-top: 12px; border-top: 1px solid #e5e3da; }}
      .tray-master-input-wrap {{ display: flex; align-items: center; gap: 8px; }}
      .tray-master-label {{ font-size: 13px; font-weight: 600; color: #555; }}
      .manual-map-box {{ border: 1px solid #e5e3da; border-radius: 10px; padding: 12px 14px; margin-bottom: 1.2rem; background: #fafaf8; }}
      .manual-map-input {{ padding: 7px 10px; border: 1px solid #ddd; border-radius: 6px; font-size: 13px; flex: 1; min-width: 0; }}
      #tray-master-input {{ flex: 1; max-width: 260px; padding: 7px 10px; border: 1px solid #ddd; border-radius: 6px; font-size: 13px; }}
      .master-match-hint {{ font-size: 12px; margin: 6px 0 0; padding: 5px 10px; border-radius: 6px; }}
      .master-match-hint.match {{ background: #dbeafe; color: #1e40af; }}
      .master-match-hint.nomatch {{ background: #f0efe8; color: #888; }}
      select {{ font-size: 12px; padding: 4px 6px; border-radius: 4px; border: 1px solid #ddd; max-width: 160px; }}
      .groups-grid {{ display: grid; grid-template-columns: repeat(3, 1fr); gap: 8px; align-items: start; }}
      .alias-group {{ display: flex; flex-direction: column; align-items: flex-start; gap: 6px; background: white; border: 1px solid #f0efe8; border-radius: 8px; margin-bottom: 0; padding: 8px 10px; font-size: 13px; min-width: 0; }}
      .alias-group .group-top-row {{ display: flex; align-items: center; gap: 6px; width: 100%; }}
      .alias-group.drag-over {{ outline: 2px solid #166534; outline-offset: -2px; }}
      .canonical-name {{ font-weight: 700; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; flex: 1; min-width: 0; }}
      .variant-chips {{ display: flex; flex-wrap: wrap; gap: 4px; width: 100%; }}
      .variant-chip {{ position: relative; display: inline-flex; align-items: center; max-width: 100%; padding: 4px 8px; background: #fafaf8; border: 1px solid #e5e3da; border-radius: 14px; font-size: 12px; color: #555; overflow: hidden; }}
      .variant-chip .raw-sku-text {{ overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }}
      .variant-x {{ border: none; background: none; cursor: pointer; color: #991b1b; font-size: 11px; padding: 0 0 0 5px; line-height: 1; opacity: 0; width: 0; overflow: hidden; transition: opacity 0.1s, width 0.1s; flex-shrink: 0; }}
      .variant-chip:hover .variant-x {{ opacity: 1; width: 12px; }}
      .add-here-btn {{ font-size: 11px; padding: 3px 8px; background: #1a1916; color: white; border: none; border-radius: 10px; cursor: pointer; opacity: 0.4; pointer-events: none; white-space: nowrap; flex-shrink: 0; }}
      .add-here-btn.armed {{ opacity: 1; pointer-events: auto; background: #166534; }}
      .rename-btn {{ font-size: 12px; padding: 2px 6px; background: none; color: #999; border: 1px solid #e5e3da; border-radius: 6px; cursor: pointer; flex-shrink: 0; line-height: 1.4; }}
      .rename-btn:hover {{ color: #1a1916; border-color: #bbb; background: #f5f4f0; }}
      .empty-note {{ color: #888; font-size: 13px; }}
    </style></head>
    <body>
      <div class="nav">
        <h1>⚙️ Admin</h1>
        <a href="/" class="btn">← Back to App</a>
        <a href="/admin/export-weights.csv" class="btn" style="background:#166534">⬇ Export legacy SKU weights (CSV)</a>
        <a href="/admin/logout" class="btn" style="background:#666">Logout</a>
      </div>
      <div id="msg" class="msg"></div>

      <div id="panel-aliases" class="panel active">
        <p class="sub">Duplicate Amazon listings (e.g. HF-P2Px3~, HF-P2Px3*) can be mapped to one canonical SKU. Nothing merges automatically — click SKUs below to select them, set the master SKU, then confirm.</p>
        <input type="text" class="search-box" id="alias-search" placeholder="Search SKU or canonical name..." oninput="filterAliases()">
        <datalist id="canonical-options">{datalist_html}</datalist>
        <script>window.knownCanonicals = {json.dumps(all_canonicals_for_options)};</script>

        <div id="staging-tray" class="staging-tray" ondragover="onTrayDragOver(event)" ondrop="onTrayDrop(event)" ondragleave="onTrayDragLeave(event)">
          <p class="tray-label">Selected SKUs (click chips below, or drag them here)</p>
          <div id="tray-chips" class="tray-chips"><span class="tray-empty">None selected yet</span></div>
          <div id="tray-master-row" class="tray-master-row" style="display:none">
            <div class="tray-master-input-wrap">
              <span class="tray-master-label">Master SKU:</span>
              <input type="text" id="tray-master-input" list="canonical-options" placeholder="e.g. HF-P2Px3" oninput="checkMasterMatch()">
              <button onclick="confirmTray()" style="padding:6px 14px;background:#166534;color:white;border:none;border-radius:6px;cursor:pointer;font-size:13px">Confirm group</button>
              <button onclick="clearTray()" style="padding:6px 10px;background:#888;color:white;border:none;border-radius:6px;cursor:pointer;font-size:13px">Clear</button>
            </div>
            <p id="master-match-hint" class="master-match-hint" style="display:none"></p>
          </div>
        </div>

        <div class="manual-map-box">
          <p class="tray-label">Manually map a SKU — for one you've already dismissed, or haven't seen yet</p>
          <div class="tray-master-input-wrap">
            <input type="text" id="manual-raw-input" class="manual-map-input" placeholder="Raw SKU (exact, e.g. BD6372-P4)">
            <input type="text" id="manual-canonical-input" class="manual-map-input" list="canonical-options" placeholder="Canonical SKU">
            <button onclick="manualMapSku()" style="padding:7px 14px;background:#166534;color:white;border:none;border-radius:6px;cursor:pointer;font-size:13px;flex-shrink:0">Map</button>
          </div>
        </div>

        <p class="section-label">Unmapped SKUs seen ({len(unmapped)})</p>
        <p class="hint">Click a SKU to select it (selected = green). Select 2+ that are the same product, set a master SKU above, then confirm. Click ✕ to dismiss a SKU as its own item.</p>
        <div id="unmapped-list" class="chip-pool" ondragover="onTrayDragOver(event)" ondrop="onPoolDrop(event)">
          {unmapped_html if unmapped else "<p class='empty-note'>No unmapped SKUs pending — process some batches to see new ones appear here.</p>"}
        </div>

        <p class="section-label" style="margin-top:1.5rem">Confirmed mappings ({len(grouped)} canonical SKU{'s' if len(grouped) != 1 else ''})</p>
        <div id="groups-list" class="groups-grid">
          {groups_html if grouped else "<p class='empty-note'>No confirmed mappings yet.</p>"}
        </div>
      </div>

      <script>
        function showMsg(text, ok=true) {{
          const m = document.getElementById('msg');
          m.textContent = text;
          m.style.display = 'block';
          m.style.background = ok ? '#dcfce7' : '#fee2e2';
          m.style.color = ok ? '#166534' : '#991b1b';
          setTimeout(() => m.style.display = 'none', 3000);
        }}
        (function restoreScroll() {{
          const y = sessionStorage.getItem('admin-scroll-y');
          if (y) {{ window.scrollTo(0, parseInt(y)); sessionStorage.removeItem('admin-scroll-y'); }}
        }})();
        function saveScrollAndReload() {{
          sessionStorage.setItem('admin-scroll-y', window.scrollY);
          location.reload();
        }}
        function filterAliases() {{
          const q = document.getElementById('alias-search').value.toLowerCase().trim();
          document.querySelectorAll('#unmapped-list .sku-chip').forEach(el => {{
            el.style.display = !q || el.dataset.search.includes(q) ? '' : 'none';
          }});
          document.querySelectorAll('#groups-list .alias-group').forEach(el => {{
            el.style.display = (!q || el.dataset.search.includes(q)) ? '' : 'none';
          }});
        }}
        // ── Selection tray (click-to-select, with drag-and-drop as a secondary option) ──
        let trayItems = {{}}; // key -> rawSku

        function toggleSelect(e, key, raw) {{
          if (e.target.closest('.chip-x')) return; // dismiss button handles its own click
          if (trayItems[key]) {{
            removeFromTray(key);
          }} else {{
            addToTray(key, raw);
          }}
        }}
        function onChipDragStart(e) {{
          const chip = e.target.closest('.sku-chip');
          e.dataTransfer.setData('text/plain', JSON.stringify({{ key: chip.dataset.key, raw: chip.dataset.raw }}));
          chip.classList.add('dragging');
        }}
        function onTrayDragOver(e) {{
          e.preventDefault();
          document.getElementById('staging-tray').classList.add('drag-over');
        }}
        function onTrayDragLeave(e) {{
          if (e.currentTarget === e.target) document.getElementById('staging-tray').classList.remove('drag-over');
        }}
        function onTrayDrop(e) {{
          e.preventDefault();
          document.getElementById('staging-tray').classList.remove('drag-over');
          const data = JSON.parse(e.dataTransfer.getData('text/plain'));
          addToTray(data.key, data.raw);
        }}
        function onPoolDrop(e) {{
          e.preventDefault();
          const data = JSON.parse(e.dataTransfer.getData('text/plain') || '{{}}');
          if (data.key && trayItems[data.key]) removeFromTray(data.key);
        }}
        function addToTray(key, raw) {{
          trayItems[key] = raw;
          const chip = document.getElementById('unmapped-' + key);
          if (chip) chip.classList.add('selected');
          renderTray();
        }}
        function removeFromTray(key) {{
          delete trayItems[key];
          const chip = document.getElementById('unmapped-' + key);
          if (chip) chip.classList.remove('selected');
          renderTray();
        }}
        function escapeHtml(s) {{
          const d = document.createElement('div');
          d.textContent = s;
          return d.innerHTML;
        }}
        function renderTray() {{
          const keys = Object.keys(trayItems);
          const trayChips = document.getElementById('tray-chips');
          const masterRow = document.getElementById('tray-master-row');
          trayChips.innerHTML = keys.length
            ? keys.map(k => `
              <div class="sku-chip selected" draggable="true" data-key="${{k}}" data-raw="${{escapeHtml(trayItems[k])}}" ondragstart="onChipDragStart(event)">
                <span class="raw-sku">${{escapeHtml(trayItems[k])}}</span>
                <button class="chip-x" onclick="removeFromTray('${{k}}')" title="Remove from selection" aria-label="Remove">✕</button>
              </div>`).join('')
            : '<span class="tray-empty">None selected yet</span>';
          masterRow.style.display = keys.length ? 'flex' : 'none';
          if (keys.length && !document.getElementById('tray-master-input').value) {{
            document.getElementById('tray-master-input').value = trayItems[keys[0]];
          }}
          updateArmedButtons();
          checkMasterMatch();
        }}
        function clearTray() {{
          Object.keys(trayItems).forEach(k => {{
            const chip = document.getElementById('unmapped-' + k);
            if (chip) chip.classList.remove('selected');
          }});
          trayItems = {{}};
          document.getElementById('tray-master-input').value = '';
          renderTray();
          checkMasterMatch();
        }}
        function checkMasterMatch() {{
          const val = document.getElementById('tray-master-input').value.trim();
          const hint = document.getElementById('master-match-hint');
          if (!val) {{ hint.style.display = 'none'; return; }}
          const known = window.knownCanonicals || [];
          const exact = known.find(c => c.toLowerCase() === val.toLowerCase());
          if (exact) {{
            hint.textContent = exact === val
              ? 'Will add to existing group "' + exact + '"'
              : 'Will merge into existing group "' + exact + '" (matched, ignoring letter case)';
            hint.className = 'master-match-hint match';
            hint.style.display = 'block';
          }} else {{
            hint.textContent = 'New canonical SKU — no existing group matches "' + val + '"';
            hint.className = 'master-match-hint nomatch';
            hint.style.display = 'block';
          }}
        }}
        async function confirmTray() {{
          const master = document.getElementById('tray-master-input').value.trim();
          const keys = Object.keys(trayItems);
          if (!master) {{ showMsg('✗ Enter a master SKU first', false); return; }}
          if (!keys.length) {{ showMsg('✗ Select at least one SKU first', false); return; }}
          await mapKeysToCanonical(keys, master);
          clearTray();
        }}
        async function mapKeysToCanonical(keys, master) {{
          let okCount = 0;
          let lastFragment = null;
          let resolvedCanonical = master;
          let mergedNotice = false;
          for (const key of keys) {{
            const chip = document.getElementById('unmapped-' + key);
            const raw = trayItems[key] || (chip ? chip.dataset.raw : null);
            if (!raw) continue;
            const res = await fetch('/admin/confirm-alias', {{
              method: 'POST',
              headers: {{'Content-Type': 'application/json'}},
              body: JSON.stringify({{raw_sku: raw, canonical_sku: master}})
            }});
            const data = await res.json();
            if (data.ok) {{
              okCount++;
              lastFragment = data.fragment;
              resolvedCanonical = data.canonical_sku;
              if (data.merged_into_existing) mergedNotice = true;
              if (chip) chip.remove();
            }}
          }}
          if (okCount !== keys.length) {{
            showMsg('✗ Mapped ' + okCount + '/' + keys.length + ' — check and retry', false);
          }} else if (mergedNotice) {{
            showMsg('✓ Mapped ' + okCount + ' SKU' + (okCount !== 1 ? 's' : '') + ' → existing group "' + resolvedCanonical + '" (matched an existing canonical SKU)');
          }} else {{
            showMsg('✓ Mapped ' + okCount + ' SKU' + (okCount !== 1 ? 's' : '') + ' → ' + resolvedCanonical);
          }}
          if (lastFragment) patchGroupFragment(resolvedCanonical, lastFragment);
          updateUnmappedCount();
        }}
        async function manualMapSku() {{
          const rawInput = document.getElementById('manual-raw-input');
          const canonicalInput = document.getElementById('manual-canonical-input');
          const raw = rawInput.value.trim();
          const canonical = canonicalInput.value.trim();
          if (!raw || !canonical) {{ showMsg('✗ Enter both a raw SKU and a canonical SKU', false); return; }}
          const res = await fetch('/admin/confirm-alias', {{
            method: 'POST',
            headers: {{'Content-Type': 'application/json'}},
            body: JSON.stringify({{raw_sku: raw, canonical_sku: canonical}})
          }});
          const data = await res.json();
          if (data.ok) {{
            patchGroupFragment(data.canonical_sku, data.fragment);
            // in case it was still sitting (undismissed) in the unmapped queue, clear that chip too
            const chip = Array.from(document.querySelectorAll('#unmapped-list .sku-chip')).find(c => c.dataset.raw === raw);
            if (chip) chip.remove();
            updateUnmappedCount();
            rawInput.value = ''; canonicalInput.value = '';
            if (data.merged_into_existing) {{
              showMsg('✓ Mapped "' + raw + '" → existing group "' + data.canonical_sku + '"');
            }} else {{
              showMsg('✓ Mapped "' + raw + '" → ' + data.canonical_sku);
            }}
          }} else showMsg('✗ Error: ' + data.error, false);
        }}
        async function renameCanonical(e, btn) {{
          e.preventDefault();
          e.stopPropagation();
          const groupEl = btn.closest('.alias-group');
          const oldCanonical = groupEl.dataset.canonical;
          const newCanonical = prompt('Rename "' + oldCanonical + '" to:', oldCanonical);
          if (!newCanonical || newCanonical.trim() === '' || newCanonical.trim() === oldCanonical) return;
          const res = await fetch('/admin/rename-canonical', {{
            method: 'POST',
            headers: {{'Content-Type': 'application/json'}},
            body: JSON.stringify({{old_canonical: oldCanonical, new_canonical: newCanonical.trim()}})
          }});
          const data = await res.json();
          if (data.ok) {{
            groupEl.remove();
            patchGroupFragment(data.canonical_sku, data.fragment);
            if (data.merged_into_existing) {{
              showMsg('✓ Renamed → merged into existing group "' + data.canonical_sku + '"');
            }} else {{
              showMsg('✓ Renamed to "' + data.canonical_sku + '"');
            }}
          }} else showMsg('✗ Error: ' + data.error, false);
        }}
        function patchGroupFragment(canonical, fragmentHtml) {{
          const groupsList = document.getElementById('groups-list');
          const emptyNote = groupsList.querySelector('.empty-note');
          if (emptyNote) emptyNote.remove();
          const existing = Array.from(groupsList.querySelectorAll('.alias-group')).find(
            g => (g.dataset.canonical || '').toLowerCase() === canonical.toLowerCase());
          const temp = document.createElement('div');
          temp.innerHTML = fragmentHtml.trim();
          const newGroupEl = temp.firstElementChild;
          if (existing) {{
            existing.replaceWith(newGroupEl);
          }} else {{
            groupsList.appendChild(newGroupEl);
          }}
          if (!(window.knownCanonicals || []).some(c => c.toLowerCase() === canonical.toLowerCase())) {{
            window.knownCanonicals = (window.knownCanonicals || []).concat(canonical);
            const dl = document.getElementById('canonical-options');
            const opt = document.createElement('option');
            opt.value = canonical;
            dl.appendChild(opt);
          }}
          updateArmedButtons();
          const groupCount = groupsList.querySelectorAll('.alias-group').length;
          const allLabels = document.querySelectorAll('.section-label');
          if (allLabels[1]) allLabels[1].textContent = 'Confirmed mappings (' + groupCount + ' canonical SKU' + (groupCount !== 1 ? 's' : '') + ')';
        }}
        function updateUnmappedCount() {{
          const remaining = document.querySelectorAll('#unmapped-list .sku-chip').length;
          const allLabels = document.querySelectorAll('.section-label');
          if (allLabels[0]) allLabels[0].textContent = 'Unmapped SKUs seen (' + remaining + ')';
          if (!remaining) {{
            document.getElementById('unmapped-list').innerHTML =
              "<p class='empty-note'>No unmapped SKUs pending — process some batches to see new ones appear here.</p>";
          }}
        }}
        function onGroupDragOver(e) {{
          e.preventDefault();
          e.currentTarget.classList.add('drag-over');
        }}
        function onGroupDragLeave(e) {{
          if (e.currentTarget === e.target) e.currentTarget.classList.remove('drag-over');
        }}
        async function onGroupDrop(e, groupEl) {{
          e.preventDefault();
          groupEl.classList.remove('drag-over');
          const data = JSON.parse(e.dataTransfer.getData('text/plain') || '{{}}');
          if (!data.key) return;
          const master = groupEl.dataset.canonical;
          if (trayItems[data.key]) delete trayItems[data.key];
          renderTray();
          await mapKeysToCanonical([data.key], master);
        }}
        async function addSelectedToGroup(e, btn) {{
          e.preventDefault();
          e.stopPropagation();
          const keys = Object.keys(trayItems);
          if (!keys.length) return; // button is inert (not armed) with nothing selected
          const groupEl = btn.closest('.alias-group');
          const master = groupEl.dataset.canonical;
          await mapKeysToCanonical(keys, master);
          clearTray();
        }}
        function updateArmedButtons() {{
          const armed = Object.keys(trayItems).length > 0;
          document.querySelectorAll('.add-here-btn').forEach(b => b.classList.toggle('armed', armed));
        }}
        async function dismissUnmapped(e, key) {{
          e.stopPropagation();
          const res = await fetch('/admin/dismiss-unmapped', {{
            method: 'POST',
            headers: {{'Content-Type': 'application/json'}},
            body: JSON.stringify({{normalized_key: key}})
          }});
          const data = await res.json();
          if (data.ok) {{
            document.getElementById('unmapped-' + key).remove();
            if (trayItems[key]) {{ delete trayItems[key]; renderTray(); }}
            showMsg('✓ Dismissed — won\\'t ask again');
          }} else showMsg('✗ Error: ' + data.error, false);
        }}
        async function deleteAlias(id, btn) {{
          const chip = btn.closest('.variant-chip');
          const rawSku = chip.dataset.sku;
          if (!confirm('Remove mapping for ' + rawSku + '? It will print as-is next time and be re-queued as unmapped.')) return;
          const res = await fetch('/admin/delete-alias', {{
            method: 'POST',
            headers: {{'Content-Type': 'application/json'}},
            body: JSON.stringify({{id}})
          }});
          const data = await res.json();
          if (data.ok) {{
            const group = chip.closest('.alias-group');
            chip.remove();
            // If that was the last variant in the group, remove the whole group card
            if (group && !group.querySelector('.variant-chip')) {{
              group.remove();
              const groupsList = document.getElementById('groups-list');
              if (!groupsList.querySelector('.alias-group')) {{
                groupsList.innerHTML = "<p class='empty-note'>No confirmed mappings yet.</p>";
              }}
              const groupCount = groupsList.querySelectorAll('.alias-group').length;
              const allLabels = document.querySelectorAll('.section-label');
              if (allLabels[1]) allLabels[1].textContent = 'Confirmed mappings (' + groupCount + ' canonical SKU' + (groupCount !== 1 ? 's' : '') + ')';
            }}
            showMsg('✓ Removed mapping for ' + rawSku);
          }} else showMsg('✗ Error: ' + data.error, false);
        }}
      </script>
    </body></html>'''

@app.route('/admin/rename-canonical', methods=['POST'])
@admin_required
def admin_rename_canonical():
    data = request.json
    old_canonical = data.get('old_canonical')
    new_canonical = (data.get('new_canonical') or '').strip()
    if not old_canonical or not new_canonical:
        return jsonify({'ok': False, 'error': 'Missing old_canonical or new_canonical'})
    if new_canonical == old_canonical:
        return jsonify({'ok': False, 'error': 'That is already the current name'})
    existing = find_existing_canonical(new_canonical)
    resolved_canonical = existing if (existing and existing != old_canonical) else new_canonical
    ok = rename_canonical_sku(old_canonical, new_canonical)
    if not ok:
        return jsonify({'ok': False, 'error': 'Could not rename'})
    variants = get_alias_variants_for_canonical(resolved_canonical)
    all_canonicals = sorted(get_all_aliases().keys())
    g_idx = all_canonicals.index(resolved_canonical) if resolved_canonical in all_canonicals else len(all_canonicals)
    fragment = render_group_html(g_idx, resolved_canonical, variants)
    merged_into_existing = bool(existing) and existing != old_canonical
    return jsonify({
        'ok': True, 'canonical_sku': resolved_canonical, 'fragment': fragment,
        'merged_into_existing': merged_into_existing
    })

@app.route('/admin/confirm-alias', methods=['POST'])
@admin_required
def admin_confirm_alias():
    data = request.json
    raw_sku = data.get('raw_sku')
    canonical_sku = data.get('canonical_sku')
    if not raw_sku or not canonical_sku:
        return jsonify({'ok': False, 'error': 'Missing raw_sku or canonical_sku'})
    existing = find_existing_canonical(canonical_sku)
    resolved_canonical = existing or canonical_sku
    ok = confirm_sku_alias(raw_sku, canonical_sku)
    if not ok:
        return jsonify({'ok': False, 'error': 'Could not save mapping'})
    variants = get_alias_variants_for_canonical(resolved_canonical)
    all_canonicals = sorted(get_all_aliases().keys())
    g_idx = all_canonicals.index(resolved_canonical) if resolved_canonical in all_canonicals else len(all_canonicals)
    fragment = render_group_html(g_idx, resolved_canonical, variants)
    merged_into_existing = bool(existing) and existing != canonical_sku
    return jsonify({
        'ok': True, 'canonical_sku': resolved_canonical, 'fragment': fragment,
        'variant_count': len(variants), 'merged_into_existing': merged_into_existing
    })

@app.route('/admin/dismiss-unmapped', methods=['POST'])
@admin_required
def admin_dismiss_unmapped():
    data = request.json
    normalized_key = data.get('normalized_key')
    if not normalized_key:
        return jsonify({'ok': False, 'error': 'Missing normalized_key'})
    ok = dismiss_unmapped_sku(normalized_key)
    return jsonify({'ok': ok})

@app.route('/admin/delete-alias', methods=['POST'])
@admin_required
def admin_delete_alias():
    data = request.json
    alias_id = data.get('id')
    if not alias_id:
        return jsonify({'ok': False, 'error': 'Missing id'})
    ok = delete_sku_alias(alias_id)
    return jsonify({'ok': ok})


if __name__ == '__main__':
    init_db()
    port = int(os.environ.get('PORT', 5000))
    print("\n  Label Merger running at http://localhost:" + str(port) + "\n")
    app.run(debug=False, host='0.0.0.0', port=port)

#!/usr/bin/env python3
import os, re, io, csv, json, zipfile, tempfile, threading, uuid, string, html as html_module
from pathlib import Path
from functools import wraps
from datetime import datetime
from zoneinfo import ZoneInfo
from flask import Flask, request, jsonify, send_file, render_template, session, redirect, url_for, Response
from pdf2image import convert_from_path
from pypdf import PdfReader, PdfWriter
from reportlab.pdfgen import canvas
from reportlab.graphics.barcode.qr import QrCodeWidget
from reportlab.graphics.shapes import Drawing
from reportlab.graphics import renderPDF
import pytesseract
import psycopg2
from psycopg2.extras import RealDictCursor

app = Flask(__name__)
app.secret_key = os.environ.get('ADMIN_PASSWORD', 'changeme') + '_secret'
app.config['MAX_CONTENT_LENGTH'] = 200 * 1024 * 1024
jobs = {}
jobs_lock = threading.Lock()
ADMIN_PASSWORD = os.environ.get('ADMIN_PASSWORD', 'M4Mart2026')
DATABASE_URL = os.environ.get('DATABASE_URL')
WEBSITE_URL = 'pillowfactory.co.uk'
QR_URL = 'https://' + WEBSITE_URL


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

def draw_qr_code(c, data, x, y, size):
    """Draw a QR code on the canvas, bottom-left corner at (x, y), size x size points."""
    qr = QrCodeWidget(data)
    b = qr.getBounds()
    w = b[2] - b[0]
    h = b[3] - b[1]
    d = Drawing(size, size, transform=[size / w, 0, 0, size / h, 0, 0])
    d.add(qr)
    renderPDF.draw(d, c, x, y)


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
    c.drawString(8, 8, str(page_num) + '/' + str(total_pages) + batch_id)
    c.setFont('Helvetica', 6)
    c.setFillColorRGB(0.4, 0.4, 0.4)
    c.drawString(8, 17, WEBSITE_URL)
    c.setFillColorRGB(0, 0, 0)
    draw_qr_code(c, QR_URL, page_w - 58, 8, 50)

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
    c.drawString(8, 8, str(page_num) + '/' + str(total_pages) + batch_id)
    c.setFont('Helvetica', 6)
    c.setFillColorRGB(0.4, 0.4, 0.4)
    c.drawString(8, 17, WEBSITE_URL)
    c.setFillColorRGB(0, 0, 0)
    draw_qr_code(c, QR_URL, page_w - 58, 8, 50)

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
        jobs[job_id]['download_name'] = 'labels_batch' + batch_id + '.pdf'
        jobs[job_id]['pick_list'] = pick_list


# ── ROUTES ────────────────────────────────────────────────────────────────────

@app.route('/')
def index():
    return render_template('index.html')

@app.route('/upload', methods=['POST'])
def upload():
    job_id = str(uuid.uuid4())[:8]
    tmpdir = tempfile.mkdtemp()
    pdf_files = []

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
    t = threading.Thread(target=run_job, args=(job_id, pdf_files, tmpdir))
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
    with jobs_lock:
        job = jobs.get(job_id)
    if not job or not job.get('result_path'):
        return jsonify({'error': 'Not ready'}), 404
    return send_file(job['result_path'], as_attachment=True,
                     download_name=job.get('download_name', 'merged_labels.pdf'),
                     mimetype='application/pdf')


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

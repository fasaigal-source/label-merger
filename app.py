#!/usr/bin/env python3
import os, re, io, json, zipfile, tempfile, threading, uuid, string
from pathlib import Path
from datetime import datetime, timedelta
from functools import wraps
from flask import Flask, request, jsonify, send_file, render_template, session, redirect, url_for
from pdf2image import convert_from_path
from pypdf import PdfReader, PdfWriter
from reportlab.pdfgen import canvas
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
            CREATE TABLE IF NOT EXISTS sku_weights (
                sku TEXT PRIMARY KEY,
                typical_weight REAL NOT NULL,
                weights JSONB NOT NULL DEFAULT '[]',
                count INTEGER NOT NULL DEFAULT 0,
                updated_at TIMESTAMP NOT NULL DEFAULT NOW()
            )
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


# ── SKU WEIGHT MEMORY ────────────────────────────────────────────────────────

def update_sku_weight(sku, weight_kg):
    """Update weight memory for a SKU."""
    if not sku or not weight_kg or sku in ('NOT FOUND', 'ERROR'):
        return
    try:
        conn = get_db()
        cur = conn.cursor(cursor_factory=RealDictCursor)
        cur.execute('SELECT * FROM sku_weights WHERE sku = %s', (sku,))
        row = cur.fetchone()
        if row:
            weights = row['weights']
            weights.append(weight_kg)
            weights = weights[-20:]  # Keep last 20
            from collections import Counter
            typical = Counter([round(w, 1) for w in weights]).most_common(1)[0][0]
            cur.execute('''
                UPDATE sku_weights 
                SET weights = %s, typical_weight = %s, count = %s, updated_at = NOW()
                WHERE sku = %s
            ''', (json.dumps(weights), typical, len(weights), sku))
        else:
            cur.execute('''
                INSERT INTO sku_weights (sku, typical_weight, weights, count, updated_at)
                VALUES (%s, %s, %s, 1, NOW())
            ''', (sku, weight_kg, json.dumps([weight_kg])))
        conn.commit()
        cur.close()
        conn.close()
    except Exception as e:
        print(f"SKU weight update error: {e}")

def purge_old_weights():
    """Remove SKU weight records older than 4 weeks."""
    try:
        conn = get_db()
        cur = conn.cursor()
        cutoff = datetime.now() - timedelta(weeks=4)
        cur.execute('DELETE FROM sku_weights WHERE updated_at < %s', (cutoff,))
        conn.commit()
        cur.close()
        conn.close()
    except Exception as e:
        print(f"Purge error: {e}")

def check_weight_anomaly(sku, weight_kg):
    """Returns warning string if weight suggests wrong qty, else None.
    Uses ±35% natural variation buffer, flags near-double/triple ratios."""
    if not sku or not weight_kg:
        return None
    try:
        conn = get_db()
        cur = conn.cursor(cursor_factory=RealDictCursor)
        cur.execute('SELECT * FROM sku_weights WHERE sku = %s', (sku,))
        row = cur.fetchone()
        cur.close()
        conn.close()
        if not row or row['count'] < 3:
            return None
        typical = row['typical_weight']
        if typical <= 0:
            return None
        ratio = weight_kg / typical
        # ±35% natural variation = 0.65 to 1.35 → ignore
        # Gap zone 1.35 to 1.65 → ignore (ambiguous)
        # Near double 1.65 to 2.35 → flag qty=2
        # Gap zone 2.35 to 2.65 → ignore
        # Near triple 2.65 to 3.35 → flag qty=3
        if 1.65 <= ratio <= 2.35:
            return f'WEIGHT {weight_kg}kg vs typical {typical}kg — expected qty ~2?'
        elif 2.65 <= ratio <= 3.35:
            return f'WEIGHT {weight_kg}kg vs typical {typical}kg — expected qty ~3?'
        return None
    except Exception as e:
        print(f"Weight anomaly check error: {e}")
        return None

def get_all_sku_weights():
    """Get all SKU weight records for admin page."""
    try:
        conn = get_db()
        cur = conn.cursor(cursor_factory=RealDictCursor)
        cur.execute('SELECT * FROM sku_weights ORDER BY sku')
        rows = cur.fetchall()
        cur.close()
        conn.close()
        return rows
    except Exception as e:
        print(f"Get SKU weights error: {e}")
        return []

def update_sku_weight_manual(sku, new_weight):
    """Manually set typical weight for a SKU."""
    try:
        conn = get_db()
        cur = conn.cursor()
        cur.execute('''
            UPDATE sku_weights SET typical_weight = %s, updated_at = NOW()
            WHERE sku = %s
        ''', (new_weight, sku))
        conn.commit()
        cur.close()
        conn.close()
        return True
    except Exception as e:
        print(f"Manual weight update error: {e}")
        return False

def delete_sku_weight(sku):
    """Delete a SKU weight record."""
    try:
        conn = get_db()
        cur = conn.cursor()
        cur.execute('DELETE FROM sku_weights WHERE sku = %s', (sku,))
        conn.commit()
        cur.close()
        conn.close()
        return True
    except Exception as e:
        print(f"Delete SKU weight error: {e}")
        return False


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

def merge_weight_history(from_sku, to_sku):
    """Fold from_sku's weight history into to_sku's (Option A: retroactive merge)."""
    try:
        conn = get_db()
        cur = conn.cursor(cursor_factory=RealDictCursor)
        cur.execute('SELECT * FROM sku_weights WHERE sku = %s', (from_sku,))
        old = cur.fetchone()
        if not old:
            cur.close()
            conn.close()
            return
        cur.execute('SELECT * FROM sku_weights WHERE sku = %s', (to_sku,))
        target = cur.fetchone()
        combined = (target['weights'] if target else []) + old['weights']
        combined = combined[-20:]
        from collections import Counter
        typical = Counter([round(w, 1) for w in combined]).most_common(1)[0][0]
        if target:
            cur.execute('''
                UPDATE sku_weights SET weights = %s, typical_weight = %s, count = %s, updated_at = NOW()
                WHERE sku = %s
            ''', (json.dumps(combined), typical, len(combined), to_sku))
        else:
            cur.execute('''
                INSERT INTO sku_weights (sku, typical_weight, weights, count, updated_at)
                VALUES (%s, %s, %s, %s, NOW())
            ''', (to_sku, typical, json.dumps(combined), len(combined)))
        cur.execute('DELETE FROM sku_weights WHERE sku = %s', (from_sku,))
        conn.commit()
        cur.close()
        conn.close()
    except Exception as e:
        print(f"Weight history merge error: {e}")

def confirm_sku_alias(raw_sku, canonical_sku):
    """Add a confirmed mapping, remove it from the unmapped queue, and merge weight history."""
    key = normalize_sku_key(raw_sku)
    if not key or not canonical_sku:
        return False
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
        if raw_sku != canonical_sku:
            merge_weight_history(raw_sku, canonical_sku)
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

def extract_weight_from_label(page_image):
    """Extract weight in KG from Evri label - specifically from Weight in KG field only."""
    text = pytesseract.image_to_string(page_image)
    # Must be on same line as "Weight in KG" and be a decimal number
    # Excludes dates (DD/MM/YYYY) by requiring optional decimal point pattern
    m = re.search(r'Weight\s+in\s+KG\s*[:\|]?\s*([\d]+\.[\d]+|[\d]+)\s*(?:\n|$)', text, re.IGNORECASE)
    if m:
        val = m.group(1)
        # Reject if it looks like a date component (e.g. 16 from 16/06/2026)
        # Real weights are usually between 0.1 and 30 kg
        try:
            w = float(val)
            if 0.1 <= w <= 30:
                return w
        except:
            pass
    return None


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

def extract_items_from_pdf(pdf_path, weight_overrides=None):
    pages = convert_from_path(str(pdf_path), dpi=300)
    if len(pages) < 2:
        return [], '', False, None, False

    rm_label = is_royal_mail_label(pages[0])
    label_weight = extract_weight_from_label(pages[0])

    full_text = ''
    for p in pages[1:]:
        full_text += pytesseract.image_to_string(p) + '\n'

    is_business = bool(re.search(r'Amazon\s+[Bb]usiness|Packing\s+slip|Order\s+#:', full_text))
    order_match = re.search(r'Order\s+(?:ID|#)[:\s#]*([0-9]{3}-[0-9]{7}-[0-9]{7})', full_text)
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

        # Apply weight override if provided
        if weight_overrides and sku in weight_overrides:
            label_weight = weight_overrides[sku]

        canonical_sku, was_mapped = get_canonical_sku(sku)
        item = {'sku': canonical_sku, 'qty': qty}
        if was_mapped:
            item['raw_sku'] = sku
        items.append(item)

    return items, order_id, rm_label, label_weight, qty_confident


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
    c.drawString(8, 8, str(page_num) + '/' + str(total_pages) + batch_id)

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

    if warn:
        c.setFillColorRGB(1, 0.4, 0)
        c.setFont('Helvetica-Bold', 9)
        c.drawString(8, safe_bot - 14, '⚠ CHECK QTY')
        c.setFillColorRGB(0, 0, 0)

    c.save()
    packet.seek(0)
    return packet


# ── JOB RUNNER ───────────────────────────────────────────────────────────────

def run_job(job_id, pdf_files, tmpdir, weight_overrides=None):
    def update(progress, message):
        with jobs_lock:
            jobs[job_id]['progress'] = progress
            jobs[job_id]['message'] = message

    purge_old_weights()
    batch_id = get_next_batch_id()
    total = len(pdf_files)
    update(0, 'Batch ' + batch_id + ' — reading ' + str(total) + ' order(s)...')

    extracted = []
    for i, pdf_path in enumerate(pdf_files):
        fname = Path(pdf_path).name
        update(int((i / total) * 40), 'Reading ' + str(i+1) + '/' + str(total) + ': ' + fname)
        try:
            items, order_id, rm_label, label_weight, qty_confident = extract_items_from_pdf(
                pdf_path, weight_overrides)
            if not items:
                items = [{'sku': 'NOT FOUND', 'qty': '?'}]

            weight_warning = None
            if label_weight and items:
                primary_sku = items[0]['sku']
                weight_warning = check_weight_anomaly(primary_sku, label_weight)

            needs_check = not qty_confident or bool(weight_warning)

            extracted.append({
                'path': pdf_path, 'file': fname,
                'items': items, 'order_id': order_id,
                'rm_label': rm_label, 'label_weight': label_weight,
                'qty_confident': qty_confident, 'weight_warning': weight_warning,
                'needs_check': needs_check,
                'sort_key': items[0]['sku'].upper() if items else 'ZZZZ'
            })
        except Exception as e:
            extracted.append({
                'path': pdf_path, 'file': fname,
                'items': [{'sku': 'ERROR', 'qty': '?'}],
                'order_id': '', 'rm_label': False, 'label_weight': None,
                'qty_confident': False, 'weight_warning': None, 'needs_check': False,
                'sort_key': 'ZZZZ', 'error': str(e)
            })

    update(45, 'Sorting by SKU...')
    extracted.sort(key=lambda x: (x['sort_key'], x['file']))

    writer = PdfWriter()
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

            # Update weight memory
            if entry['label_weight'] and entry['items']:
                primary_sku = entry['items'][0]['sku']
                if primary_sku not in ('NOT FOUND', 'ERROR'):
                    update_sku_weight(primary_sku, entry['label_weight'])

            warn_reason = []
            if not entry['qty_confident']:
                warn_reason.append('qty unconfirmed')
            if entry['weight_warning']:
                warn_reason.append(entry['weight_warning'])

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


# ── ROUTES ────────────────────────────────────────────────────────────────────

@app.route('/')
def index():
    return render_template('index.html')

@app.route('/upload', methods=['POST'])
def upload():
    job_id = str(uuid.uuid4())[:8]
    tmpdir = tempfile.mkdtemp()
    pdf_files = []

    # Parse weight overrides from form
    weight_overrides = {}
    overrides_raw = request.form.get('weight_overrides', '')
    if overrides_raw:
        try:
            weight_overrides = json.loads(overrides_raw)
            weight_overrides = {k: float(v) for k, v in weight_overrides.items() if v}
        except:
            pass

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
    t = threading.Thread(target=run_job, args=(job_id, pdf_files, tmpdir, weight_overrides))
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

@app.route('/admin')
@admin_required
def admin():
    rows = get_all_sku_weights()
    rows_html = ''
    for r in rows:
        weights_preview = ', '.join([str(w) for w in r['weights'][-5:]])
        rows_html += f'''
        <tr id="row-{r['sku']}">
          <td style="font-weight:600">{r['sku']}</td>
          <td>
            <input type="number" step="0.01" value="{r['typical_weight']}" 
                   id="w-{r['sku']}" style="width:80px;padding:4px;border:1px solid #ddd;border-radius:4px">
            <button onclick="saveWeight('{r['sku']}')" style="padding:4px 10px;background:#166534;color:white;border:none;border-radius:4px;cursor:pointer;margin-left:4px">Save</button>
          </td>
          <td>{r['count']}</td>
          <td style="color:#666;font-size:12px">{weights_preview}</td>
          <td>{str(r['updated_at'])[:10]}</td>
          <td>
            <button onclick="deleteSku('{r['sku']}')" style="padding:4px 10px;background:#991b1b;color:white;border:none;border-radius:4px;cursor:pointer">Delete</button>
          </td>
        </tr>'''

    unmapped = get_unmapped_skus()
    unmapped_html = ''
    all_canonicals_for_options = sorted(get_all_aliases().keys())
    datalist_html = ''.join(f'<option value="{c}">' for c in all_canonicals_for_options)
    for u in unmapped:
        unmapped_html += f'''
        <div class="sku-chip" id="unmapped-{u['normalized_key']}" draggable="true"
             data-key="{u['normalized_key']}" data-raw="{u['raw_sku']}"
             data-search="{u['raw_sku'].lower()}"
             ondragstart="onChipDragStart(event)">
          <span class="raw-sku">{u['raw_sku']}</span>
          <span class="seen-count">{u['times_seen']}×</span>
          <button class="chip-x" onclick="dismissUnmapped('{u['normalized_key']}')" title="Dismiss — this is its own item" aria-label="Dismiss">✕</button>
        </div>'''

    grouped = get_all_aliases()
    groups_html = ''
    for canonical, variants in grouped.items():
        variant_rows = ''
        for v in variants:
            variant_rows += f'''
            <div class="variant-row" data-search="{v['raw_sku'].lower()} {canonical.lower()}">
              <span class="raw-sku">{v['raw_sku']}</span>
              <span class="seen-count">seen {v['times_seen']}×, last {str(v['last_seen'])[:10]}</span>
              <button onclick="deleteAlias({v['id']}, '{v['raw_sku']}')" style="padding:4px 8px;background:#991b1b;color:white;border:none;border-radius:4px;cursor:pointer;font-size:12px">Delete</button>
            </div>'''
        groups_html += f'''
        <details class="alias-group" data-search="{canonical.lower()} {' '.join(v['raw_sku'].lower() for v in variants)}">
          <summary><span class="canonical-name">{canonical}</span><span class="variant-count">{len(variants)} variant{'s' if len(variants) != 1 else ''}</span></summary>
          <div class="variant-list">{variant_rows}</div>
        </details>'''

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
      .unmapped-row, .variant-row {{ display: flex; align-items: center; gap: 8px; padding: 8px 12px; background: #fef3c7; border-radius: 6px; margin-bottom: 6px; font-size: 13px; }}
      .variant-row {{ background: #fafaf8; border: 1px solid #f0efe8; margin-bottom: 4px; }}
      .raw-sku {{ font-weight: 600; flex: 1; }}
      .seen-count {{ font-size: 11px; color: #888; white-space: nowrap; }}
      .hint {{ font-size: 12px; color: #999; margin: -4px 0 10px; }}
      .chip-pool {{ display: flex; flex-wrap: wrap; gap: 8px; min-height: 20px; }}
      .sku-chip {{ display: flex; align-items: center; gap: 6px; padding: 7px 10px; background: #fef3c7; border: 1px solid #f5d889; border-radius: 8px; font-size: 13px; cursor: grab; user-select: none; }}
      .sku-chip:active {{ cursor: grabbing; }}
      .sku-chip.dragging {{ opacity: 0.4; }}
      .sku-chip .raw-sku {{ font-weight: 600; }}
      .sku-chip .seen-count {{ font-size: 10px; color: #92400e; background: rgba(255,255,255,0.5); padding: 1px 6px; border-radius: 10px; }}
      .chip-x {{ border: none; background: none; cursor: pointer; color: #92400e; font-size: 13px; padding: 0 2px; line-height: 1; opacity: 0.6; }}
      .chip-x:hover {{ opacity: 1; }}
      .staging-tray {{ border: 2px dashed #ccc8b8; border-radius: 10px; padding: 14px; margin-bottom: 1.2rem; background: #fafaf8; transition: background 0.15s, border-color 0.15s; }}
      .staging-tray.drag-over {{ background: #eef6ee; border-color: #166534; }}
      .tray-label {{ font-size: 12px; color: #999; margin: 0 0 8px; }}
      .tray-chips {{ display: flex; flex-wrap: wrap; gap: 8px; min-height: 24px; }}
      .tray-chips .sku-chip {{ background: #dcfce7; border-color: #86efac; }}
      .tray-chips .sku-chip .seen-count {{ color: #166534; }}
      .tray-chips .chip-x {{ color: #166534; }}
      .tray-master-row {{ display: flex; align-items: center; gap: 8px; margin-top: 12px; padding-top: 12px; border-top: 1px solid #e5e3da; }}
      .tray-master-label {{ font-size: 13px; font-weight: 600; color: #555; }}
      #tray-master-input {{ flex: 1; max-width: 260px; padding: 7px 10px; border: 1px solid #ddd; border-radius: 6px; font-size: 13px; }}
      select {{ font-size: 12px; padding: 4px 6px; border-radius: 4px; border: 1px solid #ddd; max-width: 160px; }}
      .alias-group {{ background: white; border: 1px solid #f0efe8; border-radius: 8px; margin-bottom: 6px; overflow: hidden; }}
      .alias-group summary {{ display: flex; align-items: center; gap: 10px; padding: 10px 14px; cursor: pointer; background: #fafaf8; list-style: none; font-size: 13px; }}
      .alias-group summary::-webkit-details-marker {{ display: none; }}
      .canonical-name {{ font-weight: 700; flex: 1; }}
      .variant-count {{ font-size: 11px; color: #888; }}
      .variant-list {{ padding: 8px 14px 10px; }}
      .empty-note {{ color: #888; font-size: 13px; }}
    </style></head>
    <body>
      <div class="nav">
        <h1>⚙️ Admin</h1>
        <a href="/" class="btn">← Back to App</a>
        <a href="/admin/logout" class="btn" style="background:#666">Logout</a>
      </div>
      <div id="msg" class="msg"></div>

      <div class="tabs">
        <div class="tab active" onclick="switchTab('weights')">SKU Weight Memory</div>
        <div class="tab" onclick="switchTab('aliases')">SKU Aliases</div>
      </div>

      <div id="panel-weights" class="panel active">
        <p class="sub">Weights auto-expire after 4 weeks. Edit typical weight or delete a SKU to reset its memory.</p>
        {"<p class='empty-note'>No SKU weight data yet — process some batches first.</p>" if not rows else ""}
        {"<table><thead><tr><th>SKU</th><th>Typical Weight (kg)</th><th>Seen</th><th>Recent weights</th><th>Last updated</th><th>Action</th></tr></thead><tbody>" + rows_html + "</tbody></table>" if rows else ""}
      </div>

      <div id="panel-aliases" class="panel">
        <p class="sub">Duplicate Amazon listings (e.g. HF-P2Px3~, HF-P2Px3*) can be mapped to one canonical SKU. Nothing merges automatically — drag SKUs into the tray below, set the master SKU, then confirm.</p>
        <input type="text" class="search-box" id="alias-search" placeholder="Search SKU or canonical name..." oninput="filterAliases()">
        <datalist id="canonical-options">{datalist_html}</datalist>

        <div id="staging-tray" class="staging-tray" ondragover="onTrayDragOver(event)" ondrop="onTrayDrop(event)" ondragleave="onTrayDragLeave(event)">
          <p class="tray-label">Drag SKUs here to group them</p>
          <div id="tray-chips" class="tray-chips"></div>
          <div id="tray-master-row" class="tray-master-row" style="display:none">
            <span class="tray-master-label">Master SKU:</span>
            <input type="text" id="tray-master-input" list="canonical-options" placeholder="e.g. HF-P2Px3">
            <button onclick="confirmTray()" style="padding:6px 14px;background:#166534;color:white;border:none;border-radius:6px;cursor:pointer;font-size:13px">Confirm group</button>
            <button onclick="clearTray()" style="padding:6px 10px;background:#888;color:white;border:none;border-radius:6px;cursor:pointer;font-size:13px">Clear</button>
          </div>
        </div>

        <p class="section-label">Unmapped SKUs seen ({len(unmapped)})</p>
        <p class="hint">Drag chips into the tray above to group them, or click ✕ to dismiss a SKU as its own item.</p>
        <div id="unmapped-list" class="chip-pool" ondragover="onTrayDragOver(event)" ondrop="onPoolDrop(event)">
          {unmapped_html if unmapped else "<p class='empty-note'>No unmapped SKUs pending — process some batches to see new ones appear here.</p>"}
        </div>

        <p class="section-label" style="margin-top:1.5rem">Confirmed mappings ({len(grouped)} canonical SKU{'s' if len(grouped) != 1 else ''})</p>
        <div id="groups-list">
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
        function switchTab(name) {{
          document.querySelectorAll('.tab').forEach(t => t.classList.remove('active'));
          document.querySelectorAll('.panel').forEach(p => p.classList.remove('active'));
          document.querySelector('.tab[onclick*="' + name + '"]').classList.add('active');
          document.getElementById('panel-' + name).classList.add('active');
        }}
        function filterAliases() {{
          const q = document.getElementById('alias-search').value.toLowerCase().trim();
          document.querySelectorAll('#unmapped-list .sku-chip').forEach(el => {{
            el.style.display = !q || el.dataset.search.includes(q) ? '' : 'none';
          }});
          document.querySelectorAll('#groups-list .alias-group').forEach(el => {{
            const match = !q || el.dataset.search.includes(q);
            el.style.display = match ? '' : 'none';
            if (match && q) el.open = true;
          }});
        }}
        async function saveWeight(sku) {{
          const val = document.getElementById('w-' + sku).value;
          const res = await fetch('/admin/update-weight', {{
            method: 'POST',
            headers: {{'Content-Type': 'application/json'}},
            body: JSON.stringify({{sku, weight: parseFloat(val)}})
          }});
          const data = await res.json();
          showMsg(data.ok ? '✓ Weight updated for ' + sku : '✗ Error: ' + data.error, data.ok);
        }}
        async function deleteSku(sku) {{
          if (!confirm('Delete weight history for ' + sku + '?')) return;
          const res = await fetch('/admin/delete-sku', {{
            method: 'POST',
            headers: {{'Content-Type': 'application/json'}},
            body: JSON.stringify({{sku}})
          }});
          const data = await res.json();
          if (data.ok) {{
            document.getElementById('row-' + sku).remove();
            showMsg('✓ Deleted ' + sku);
          }} else showMsg('✗ Error: ' + data.error, false);
        }}
        // ── Drag and drop staging tray ──────────────────────────────────────
        let trayItems = {{}}; // key -> rawSku

        function onChipDragStart(e) {{
          e.dataTransfer.setData('text/plain', JSON.stringify({{
            key: e.target.closest('.sku-chip').dataset.key,
            raw: e.target.closest('.sku-chip').dataset.raw
          }}));
          e.target.closest('.sku-chip').classList.add('dragging');
        }}
        function onTrayDragOver(e) {{
          e.preventDefault();
          document.getElementById('staging-tray').classList.add('drag-over');
        }}
        function onTrayDragLeave(e) {{
          if (e.target.id === 'staging-tray') document.getElementById('staging-tray').classList.remove('drag-over');
        }}
        function onTrayDrop(e) {{
          e.preventDefault();
          document.getElementById('staging-tray').classList.remove('drag-over');
          const data = JSON.parse(e.dataTransfer.getData('text/plain'));
          addToTray(data.key, data.raw);
        }}
        function onPoolDrop(e) {{
          // Dropping back on the pool removes a chip from the tray
          e.preventDefault();
          const data = JSON.parse(e.dataTransfer.getData('text/plain'));
          if (trayItems[data.key]) {{
            delete trayItems[data.key];
            renderTray();
          }}
        }}
        function addToTray(key, raw) {{
          trayItems[key] = raw;
          const chip = document.getElementById('unmapped-' + key);
          if (chip) chip.style.display = 'none';
          renderTray();
        }}
        function removeFromTray(key) {{
          delete trayItems[key];
          const chip = document.getElementById('unmapped-' + key);
          if (chip) chip.style.display = '';
          renderTray();
        }}
        function renderTray() {{
          const keys = Object.keys(trayItems);
          const trayChips = document.getElementById('tray-chips');
          const masterRow = document.getElementById('tray-master-row');
          trayChips.innerHTML = keys.map(k => `
            <div class="sku-chip" draggable="true" data-key="${{k}}" data-raw="${{trayItems[k]}}" ondragstart="onChipDragStart(event)">
              <span class="raw-sku">${{trayItems[k]}}</span>
              <button class="chip-x" onclick="removeFromTray('${{k}}')" title="Remove from group" aria-label="Remove">✕</button>
            </div>`).join('');
          masterRow.style.display = keys.length ? 'flex' : 'none';
          if (keys.length && !document.getElementById('tray-master-input').value) {{
            // Default suggestion: the most-seen raw SKU text, edit freely
            document.getElementById('tray-master-input').value = trayItems[keys[0]];
          }}
        }}
        function clearTray() {{
          Object.keys(trayItems).forEach(k => {{
            const chip = document.getElementById('unmapped-' + k);
            if (chip) chip.style.display = '';
          }});
          trayItems = {{}};
          document.getElementById('tray-master-input').value = '';
          renderTray();
        }}
        async function confirmTray() {{
          const master = document.getElementById('tray-master-input').value.trim();
          const keys = Object.keys(trayItems);
          if (!master) {{ showMsg('✗ Enter a master SKU first', false); return; }}
          if (!keys.length) {{ showMsg('✗ Drag at least one SKU into the tray', false); return; }}
          let okCount = 0;
          for (const key of keys) {{
            const res = await fetch('/admin/confirm-alias', {{
              method: 'POST',
              headers: {{'Content-Type': 'application/json'}},
              body: JSON.stringify({{raw_sku: trayItems[key], canonical_sku: master}})
            }});
            const data = await res.json();
            if (data.ok) okCount++;
          }}
          if (okCount === keys.length) {{
            showMsg('✓ Mapped ' + okCount + ' SKU' + (okCount !== 1 ? 's' : '') + ' → ' + master);
            setTimeout(() => location.reload(), 600);
          }} else {{
            showMsg('✗ Mapped ' + okCount + '/' + keys.length + ' — check and retry', false);
          }}
        }}
        async function dismissUnmapped(key) {{
          const res = await fetch('/admin/dismiss-unmapped', {{
            method: 'POST',
            headers: {{'Content-Type': 'application/json'}},
            body: JSON.stringify({{normalized_key: key}})
          }});
          const data = await res.json();
          if (data.ok) {{
            document.getElementById('unmapped-' + key).remove();
            showMsg('✓ Dismissed — won\\'t ask again');
          }} else showMsg('✗ Error: ' + data.error, false);
        }}
        async function deleteAlias(id, rawSku) {{
          if (!confirm('Remove mapping for ' + rawSku + '? It will print as-is next time and be re-queued as unmapped.')) return;
          const res = await fetch('/admin/delete-alias', {{
            method: 'POST',
            headers: {{'Content-Type': 'application/json'}},
            body: JSON.stringify({{id}})
          }});
          const data = await res.json();
          if (data.ok) {{
            showMsg('✓ Removed mapping for ' + rawSku);
            setTimeout(() => location.reload(), 600);
          }} else showMsg('✗ Error: ' + data.error, false);
        }}
      </script>
    </body></html>'''

@app.route('/admin/update-weight', methods=['POST'])
@admin_required
def admin_update_weight():
    data = request.json
    sku = data.get('sku')
    weight = data.get('weight')
    if not sku or not weight:
        return jsonify({'ok': False, 'error': 'Missing SKU or weight'})
    ok = update_sku_weight_manual(sku, weight)
    return jsonify({'ok': ok})

@app.route('/admin/delete-sku', methods=['POST'])
@admin_required
def admin_delete_sku():
    data = request.json
    sku = data.get('sku')
    if not sku:
        return jsonify({'ok': False, 'error': 'Missing SKU'})
    ok = delete_sku_weight(sku)
    return jsonify({'ok': ok})

@app.route('/admin/confirm-alias', methods=['POST'])
@admin_required
def admin_confirm_alias():
    data = request.json
    raw_sku = data.get('raw_sku')
    canonical_sku = data.get('canonical_sku')
    if not raw_sku or not canonical_sku:
        return jsonify({'ok': False, 'error': 'Missing raw_sku or canonical_sku'})
    ok = confirm_sku_alias(raw_sku, canonical_sku)
    return jsonify({'ok': ok})

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

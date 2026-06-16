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

        items.append({'sku': sku, 'qty': qty})

    return items, order_id, rm_label, label_weight, qty_confident


# ── OVERLAY FUNCTIONS ─────────────────────────────────────────────────────────

def create_evri_overlay(items, order_id, page_num, total_pages, batch_id, page_w, page_h, warn=False):
    packet = io.BytesIO()
    c = canvas.Canvas(packet, pagesize=(page_w, page_h))
    c.setFillColorRGB(0, 0, 0)

    start_y = page_h - 28
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
        c.drawString(page_w * 0.62, page_h - 28, '⚠ CHECK QTY')
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

    return f'''<!DOCTYPE html>
    <html><head><title>Admin — SKU Weights</title>
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
    </style></head>
    <body>
      <div class="nav">
        <h1>⚙️ SKU Weight Memory</h1>
        <a href="/" class="btn">← Back to App</a>
        <a href="/admin/logout" class="btn" style="background:#666">Logout</a>
      </div>
      <p class="sub">Weights auto-expire after 4 weeks. Edit typical weight or delete a SKU to reset its memory.</p>
      <div id="msg" class="msg"></div>
      {"<p style='color:#888;font-size:13px'>No SKU weight data yet — process some batches first.</p>" if not rows else ""}
      {"<table><thead><tr><th>SKU</th><th>Typical Weight (kg)</th><th>Seen</th><th>Recent weights</th><th>Last updated</th><th>Action</th></tr></thead><tbody>" + rows_html + "</tbody></table>" if rows else ""}
      <script>
        function showMsg(text, ok=true) {{
          const m = document.getElementById('msg');
          m.textContent = text;
          m.style.display = 'block';
          m.style.background = ok ? '#dcfce7' : '#fee2e2';
          m.style.color = ok ? '#166534' : '#991b1b';
          setTimeout(() => m.style.display = 'none', 3000);
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


if __name__ == '__main__':
    init_db()
    port = int(os.environ.get('PORT', 5000))
    print("\n  Label Merger running at http://localhost:" + str(port) + "\n")
    app.run(debug=False, host='0.0.0.0', port=port)

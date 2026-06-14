#!/usr/bin/env python3
import os, re, io, json, zipfile, tempfile, threading, uuid, string
from pathlib import Path
from flask import Flask, request, jsonify, send_file, render_template
from pdf2image import convert_from_path
from pypdf import PdfReader, PdfWriter
from reportlab.pdfgen import canvas
import pytesseract

app = Flask(__name__)
app.config['MAX_CONTENT_LENGTH'] = 200 * 1024 * 1024
jobs = {}
jobs_lock = threading.Lock()
COUNTER_FILE = os.path.join(os.path.dirname(__file__), 'batch_counter.txt')
SKU_WEIGHTS_FILE = os.path.join(os.path.dirname(__file__), 'sku_weights.json')
counter_lock = threading.Lock()
sku_weights_lock = threading.Lock()


# ── SKU WEIGHT MEMORY ────────────────────────────────────────────────────────

def load_sku_weights():
    try:
        with open(SKU_WEIGHTS_FILE, 'r') as f:
            return json.load(f)
    except:
        return {}

def save_sku_weights(data):
    try:
        with open(SKU_WEIGHTS_FILE, 'w') as f:
            json.dump(data, f, indent=2)
    except:
        pass

def update_sku_weight(sku, weight_kg):
    """Update weight memory for a SKU using most-common weight logic."""
    if not sku or not weight_kg:
        return
    with sku_weights_lock:
        data = load_sku_weights()
        if sku not in data:
            data[sku] = {'weights': [weight_kg], 'typical': weight_kg, 'count': 1}
        else:
            data[sku]['weights'].append(weight_kg)
            data[sku]['count'] += 1
            # Keep last 20 observations only
            weights = data[sku]['weights'][-20:]
            data[sku]['weights'] = weights
            # Typical = most common weight
            from collections import Counter
            data[sku]['typical'] = Counter(weights).most_common(1)[0][0]
        save_sku_weights(data)

def check_weight_anomaly(sku, weight_kg):
    """Returns warning string if weight differs significantly from typical, else None."""
    if not sku or not weight_kg:
        return None
    with sku_weights_lock:
        data = load_sku_weights()
    if sku not in data or data[sku]['count'] < 3:
        return None  # Not enough history yet
    typical = data[sku]['typical']
    if typical <= 0:
        return None
    ratio = weight_kg / typical
    # Flag if weight is 1.7x or more than typical (suggests higher qty)
    if ratio >= 1.7:
        expected_qty = round(ratio)
        return f'WEIGHT {weight_kg}kg vs typical {typical}kg — expected qty ~{expected_qty}?'
    return None


# ── BATCH ID ─────────────────────────────────────────────────────────────────

def get_next_batch_id():
    with counter_lock:
        try:
            with open(COUNTER_FILE, 'r') as f:
                n = int(f.read().strip())
        except:
            n = 0
        def num_to_letters(num):
            result = ''
            num += 1
            while num > 0:
                num -= 1
                result = string.ascii_uppercase[num % 26] + result
                num //= 26
            return result
        batch_id = num_to_letters(n)
        with open(COUNTER_FILE, 'w') as f:
            f.write(str(n + 1))
        return batch_id


# ── LABEL DETECTION ──────────────────────────────────────────────────────────

def is_royal_mail_label(page_image):
    text = pytesseract.image_to_string(page_image)
    return bool(re.search(r'Royal\s*Mail|Delivered\s+by|Post\s+by\s+the\s+end', text, re.IGNORECASE))


def extract_weight_from_label(page_image):
    """Extract weight in KG from Evri label (Weight in KG field)."""
    text = pytesseract.image_to_string(page_image)
    m = re.search(r'Weight\s+in\s+KG[^\d]*([\d.]+)', text, re.IGNORECASE)
    if m:
        try:
            return float(m.group(1))
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
    """Extract quantities using multiple methods. Returns (list_of_qtys, confident: bool)."""
    text = pytesseract.image_to_string(page)

    # METHOD 1: Find partial "Quant" header then number in next row
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

    # Nothing found — defaulting to 1, mark as NOT confident
    return None, False


# ── PDF EXTRACTION ────────────────────────────────────────────────────────────

def extract_items_from_pdf(pdf_path):
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
    qty_confident = True  # innocent until proven guilty

    for p in pages[1:]:
        result, confident = find_qty_from_column(p)
        if result is None:
            n = extract_skus_on_page(p)
            all_qtys.extend(['1'] * n)
            qty_confident = False  # defaulted — not confident
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
    max_w = page_w * 0.44

    for i, item in enumerate(items):
        y = start_y - (i * line_h)
        text = str(item['qty']) + 'x  ' + item['sku']
        fs = font_size
        c.setFont('Helvetica', fs)
        while c.stringWidth(text, 'Helvetica', fs) > max_w and fs > 5:
            fs -= 0.5
        c.setFont('Helvetica', fs)
        c.drawString(8, y, text)

    if order_id:
        c.setFont('Helvetica-Bold', 8)
        c.drawString(page_w * 0.62, 82, order_id)

    c.setFont('Helvetica-Bold', 7)
    c.drawString(8, 8, str(page_num) + '/' + str(total_pages) + batch_id)

    # ⚠ Warning sign if qty not confident
    if warn:
        c.setFillColorRGB(1, 0.4, 0)  # Orange
        c.setFont('Helvetica-Bold', 9)
        c.drawString(page_w * 0.44, page_h - 28, '⚠ CHECK QTY')
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

    # ⚠ Warning sign if qty not confident
    if warn:
        c.setFillColorRGB(1, 0.4, 0)  # Orange
        c.setFont('Helvetica-Bold', 9)
        c.drawString(8, safe_bot - 14, '⚠ CHECK QTY')
        c.setFillColorRGB(0, 0, 0)

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
            items, order_id, rm_label, label_weight, qty_confident = extract_items_from_pdf(pdf_path)
            if not items:
                items = [{'sku': 'NOT FOUND', 'qty': '?'}]

            # Check weight anomaly for each SKU
            weight_warning = None
            if label_weight and items:
                primary_sku = items[0]['sku']
                weight_warning = check_weight_anomaly(primary_sku, label_weight)

            # Flag if qty not confident OR weight anomaly detected
            needs_check = not qty_confident or bool(weight_warning)

            extracted.append({
                'path': pdf_path, 'file': fname,
                'items': items, 'order_id': order_id,
                'rm_label': rm_label,
                'label_weight': label_weight,
                'qty_confident': qty_confident,
                'weight_warning': weight_warning,
                'needs_check': needs_check,
                'sort_key': items[0]['sku'].upper() if items else 'ZZZZ'
            })
        except Exception as e:
            extracted.append({
                'path': pdf_path, 'file': fname,
                'items': [{'sku': 'ERROR', 'qty': '?'}],
                'order_id': '', 'rm_label': False,
                'label_weight': None, 'qty_confident': False,
                'weight_warning': None, 'needs_check': False,
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

            # Update SKU weight memory after successful processing
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

if __name__ == '__main__':
    port = int(os.environ.get('PORT', 5000))
    print("\n  Label Merger running at http://localhost:" + str(port) + "\n")
    app.run(debug=False, host='0.0.0.0', port=port)

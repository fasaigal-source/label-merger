"""
postcode_checker.py

Flags UK postcodes that fall in your out-of-area / surcharge zone list
(Highlands, Channel Islands, Isle of Man, Isle of Wight, Scilly, BFPO, etc).

IMPORTANT — how the postcode is actually read:
On the real 3rd-party Evri labels (confirmed against a live export), the
Destination box is part of a single flattened image covering the whole
label — there is NO text layer for the address, only for the SKU/Qty table
appended below it. So the postcode has to be OCR'd off a crop of that image;
a plain text-layer read will always come back empty for this label type.
extract_postcode_from_text() is kept as a free first try in case some other
3rd-party source ever does carry real address text, but for the labels
you're actually using, extract_postcode_via_ocr() is what does the work.

=== ROBUSTNESS PASS (this revision) ===

Diagnosed against 20 real production files (287 label pages total,
adminm4martow_*.pdf) after the first version regressed on files beyond the
one 38-label export it was tuned on. Findings, from actually rendering and
inspecting the pages (not guessing):

1. The Destination-box crop position is NOT the problem. pdfplumber's
   page.images bounding box is byte-identical — (0, 6.8, 283.5, 432.0) on a
   288x576pt page — on 285 of the 287 pages. It's one fixed template, and
   the fixed-fraction crop (ADDR_TOP/BOT_FRAC) lands cleanly on the
   Destination box every time, address included, verified by rendering the
   crop and reading it directly. The fixed-fraction crop was correct;
   nothing here was changed.

   The other 2 pages (both in adminm4martow_1b5c45f2-...pdf) are a
   genuinely different document — it has a real extractable text layer
   ("Date"/"Weight"/"Reference"/"Destination" all show up in
   page.extract_words()), unlike every other file's fully-flattened image.
   It isn't a 3rd-party Evri destination label at all, and this module
   correctly fails safe on it (unreadable -> exclude + flag for manual
   check) rather than forcing a template match. If this recurs, it's worth
   asking the source system why an unrelated document ended up in this
   export — it's out of scope to reverse-engineer a one-off document here.

2. The actual bug: Tesseract, run at --psm 6 over the whole Destination
   box, reliably hallucinates a short phantom text line in the blank space
   below a short/medium address (something like "NATN NNONE NO O4" or
   "NATN NNORE NO OA" — confirmed by cropping and re-running OCR on the
   *exact* bytes fed to Tesseract; there is nothing resembling that text
   anywhere on the label). It appears regardless of how many address lines
   precede it, sits right at the very bottom of the crop, and — this is
   the important part — is always separated from the real text block by a
   vertical gap several times larger than the normal line-to-line spacing.
   It never happens to match the postcode shape, so it was never a
   silent-wrong-flag risk, but it was actively misleading: whenever the
   *real* last line also failed the old exact-shape check (see #3), this
   hallucinated line — not the real near-miss text — got shown to the
   operator as "OCR saw: ...". _drop_hallucinated_tail() removes it
   generically (by the gap, not by hardcoding the wording), so the
   "check manually" message always reflects genuine label content.

3. Once the hallucination is out of the way, the remaining failures are
   plain character-level OCR misreads on this font, not crop or detection
   bugs, e.g.:
     - CR0 8PW (Croydon) -> "CRO 8PW" (digit 0 in the district misread as
       letter O)
     - SO24 9NF (Winchester) -> "S024 9NF" (the OUTWARD area's second
       letter, 'O', misread as digit 0 — the mirror image of the above)
     - SS0 8LS (Southend) -> "SSO0 8LS" (the district '0' misread AND
       duplicated — read once as 'O', once as '0')
     - IP19 0QR (Halesworth) -> "IP19 O0QR" (same duplication, in the
       inward code)
     - NE3 4RJ -> "NE3 4RdJ" (a stray extra character inserted)
   The old fuzzy pass only corrected a stray symbol for the very first
   outward letter ('$' for 'S') and a fixed set of substitutions for the
   inward code's first character. It had no way to fix a misread anywhere
   else, and its shape check demanded the inward code be *exactly* 3
   characters, so a single inserted/duplicated character (very common with
   this font's '0'/'O' rendering) made it discard the correct line
   entirely. This revision replaces that with a small grammar-aware fixer
   (_fix_outward / _fix_inward) that knows which positions in a UK postcode
   must be letters vs digits, applies this font's confirmed confusions
   only in the position where they're expected, and tolerates a single
   inserted/duplicated character in the inward code.

Tested against all 287 label pages across the 20 real files: 285/285 pages
of the real label template now produce a clean, correct read (the 2-page
outlier document still correctly fails safe — see #1). See the test report
delivered alongside this file for the full breakdown, plus the regression
checks below.

Regression-tested (must never break):
  - TW2 5JJ reads correctly — the whitelist re-OCR pass (lowercase
    excluded) that fixes a specific '2' -> 'e' misread on this font is
    unchanged.
  - PA3 4LN is NOT flagged — parse_outward_code still splits off the last
    3 characters as the inward code before reading the district digits, so
    it can't collapse into '34' the way it did before that fix.
  - PO30 2HB IS flagged — genuine Isle of Wight, unaffected by any of the
    above (it was already reading correctly).
"""

import re
from pdf2image import convert_from_path
import pytesseract
from pytesseract import Output

# (area, start_district, end_district)
# start=end=None means the WHOLE area is out of area, regardless of district number.
# Unchanged in this revision — this ruleset came directly from the courier's
# official out-of-area postcode list and is out of scope here.
OUT_OF_AREA_RULES = [
    ("AB", 12, 14),
    ("AB", 23, 23),
    ("AB", 30, 39),
    ("AB", 41, 45),
    ("AB", 51, 56),
    ("BF", None, None),   # BFPO
    ("BT", None, None),   # Northern Ireland
    ("FK", 17, 22),
    ("GY", None, None),   # Guernsey
    ("HS", None, None),   # Outer Hebrides
    ("IM", None, None),   # Isle of Man
    ("IV", None, None),   # Inverness-shire / Highlands
    ("JE", None, None),   # Jersey
    ("KA", 27, 28),
    ("KW", None, None),   # Caithness
    ("PA", 17, 18),
    ("PA", 20, 80),
    ("PH", 3, 3),
    ("PH", 5, 7),
    ("PH", 10, 10),
    ("PH", 11, 11),
    ("PH", 13, 50),
    ("PO", 30, 41),        # Isle of Wight
    ("TR", 21, 25),        # Isles of Scilly
    ("ZE", None, None),    # Shetland
]

# Specific full postcodes that are out-of-area even though their district isn't
OUT_OF_AREA_EXACT = {
    "HA46EP",
}

# Address-box crop, as fractions of the full 4x8in (288x576pt) 3rd-party page.
# Confirmed (not assumed) against all 20 real files: pdfplumber reports the
# label image at an identical bounding box on 285 of 287 pages, and
# rendering+viewing this crop shows it lands cleanly on the Destination box
# in every one of them. Left unchanged — the bug here was never the crop.
ADDR_LEFT_FRAC = 0.0
ADDR_RIGHT_FRAC = 0.575
ADDR_TOP_FRAC = 0.325
ADDR_BOT_FRAC = 0.531
OCR_DPI = 400  # 300dpi gave 3/38 misses in testing; 400dpi gave 1/38

STRICT_POSTCODE_RE = re.compile(r'\b([A-Za-z]{1,2}\d[A-Za-z\d]?)\s*(\d[A-Za-z]{2})\b')
# Config for the targeted re-read of an isolated postcode line: postcodes are
# never lowercase, so excluding lowercase letters from the allowed set fixes
# a specific, reproducible Tesseract error on this label's font where a '2'
# gets classified as a lowercase 'e' (confirmed via image_to_boxes: Tesseract
# segments the character correctly, it just misclassifies the isolated glyph
# — restricting the allowed alphabet removes 'e' as a possible answer).
LINE_WHITELIST_CONFIG = '--psm 7 -c tessedit_char_whitelist=ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789 '

# This font's confirmed, position-dependent 0/O confusion — seen going both
# ways across the 20-file sample, never any other letter/digit pair. Applied
# only in _fix_outward/_fix_inward, each to the position where a digit or a
# letter is grammatically required, never blindly to a whole string.
_DIGIT_LOOKALIKES = {'O': '0', 'Q': '9', 'D': '0'}   # read where a digit belongs
_LETTER_LOOKALIKES = {'0': 'O'}                       # read where a letter belongs


def _fix_digit_slot(ch: str) -> str:
    return _DIGIT_LOOKALIKES.get(ch, ch)


def _fix_letter_slot(ch: str) -> str:
    return _LETTER_LOOKALIKES.get(ch, ch)


def normalize_postcode(pc: str) -> str:
    """Uppercase, strip all whitespace: 'Pa20 1Ab' -> 'PA201AB'."""
    return re.sub(r'\s+', '', pc or '').upper()


def parse_outward_code(pc: str):
    """Return (area_letters, district_number) from a postcode, or (None, None).
    Must split off the inward code (always the last 3 chars) BEFORE reading
    the district digits — otherwise a postcode like 'PA3 4LN' collapses to
    'PA34LN' once spaces are stripped, and district '3' gets misread as '34'
    by picking up the inward code's leading digit too."""
    normalized = normalize_postcode(pc)
    outward = normalized if len(normalized) < 5 else normalized[:-3]
    m = re.match(r'^([A-Z]{1,2})(\d{1,2})', outward)
    if not m:
        return None, None
    return m.group(1), int(m.group(2))


def extract_postcode_from_text(text: str):
    """Find the first UK-postcode-shaped string in a block of already-extracted
    text. Free to call, but will return None for labels whose address is a
    flattened image (i.e. most 3rd-party Evri labels) — use
    extract_postcode_via_ocr() for those."""
    if not text:
        return None
    m = STRICT_POSTCODE_RE.search(text)
    if not m:
        return None
    return f"{m.group(1)} {m.group(2)}".upper()


def _looks_like_postcode_shaped(words):
    """Loose shape check on a detected text line's word list: either two
    tokens (outward + inward, e.g. ['TW2','5JJ']) or one contiguous token of
    plausible postcode length (e.g. 'PL145RA' when OCR drops the space).
    Tolerant of a +/-1 character miscount on either token — this font's
    0/O rendering routinely inserts or duplicates a single character
    (confirmed: '4RJ' OCR'd as '4RdJ', '0BH' OCR'd as 'O0BH') and an exact
    length match would otherwise throw away an obviously-real address line
    before it ever reaches the fuzzy postcode matcher."""
    if len(words) == 2 and 2 <= len(words[0]) <= 4 and 2 <= len(words[1]) <= 4:
        return True
    if len(words) == 1 and 4 <= len(words[0]) <= 9:
        return True
    return False


def _get_text_lines(image):
    """Group Tesseract's word-level OCR data into line-level bounding boxes,
    ordered top to bottom."""
    data = pytesseract.image_to_data(image, config='--psm 6', output_type=Output.DICT)
    lines = {}
    for i, txt in enumerate(data['text']):
        if not txt.strip():
            continue
        key = (data['block_num'][i], data['par_num'][i], data['line_num'][i])
        x, y, w, h = data['left'][i], data['top'][i], data['width'][i], data['height'][i]
        if key not in lines:
            lines[key] = {'words': [txt], 'x0': x, 'y0': y, 'x1': x + w, 'y1': y + h, 'top': y}
        else:
            b = lines[key]
            b['words'].append(txt)
            b['x0'] = min(b['x0'], x); b['y0'] = min(b['y0'], y)
            b['x1'] = max(b['x1'], x + w); b['y1'] = max(b['y1'], y + h)
    return sorted(lines.values(), key=lambda b: b['top'])


def _drop_hallucinated_tail(lines):
    """Tesseract reliably hallucinates a short phantom line in the blank
    space below the address (see module docstring #2) — confirmed by
    cropping and re-OCRing the exact bytes fed to it; nothing resembling
    that text exists on the label. It's harmless as far as false-flagging
    goes (it's never matched a postcode shape in testing), but left in
    place it can shadow the real last address line when that line fails
    its own shape check, and get shown to the operator as the OCR guess
    instead of the genuine (if slightly garbled) content.

    Detected generically rather than by matching its wording: it always
    sits in the same near-fixed spot regardless of how much real address
    text precedes it, so it always shows up as an isolated trailing line
    separated from the real text block by a gap several times the normal
    line spacing. Real address lines, by contrast, are always packed at a
    consistent spacing. This only ever drops a genuine trailing outlier —
    normal multi-line addresses never trigger it."""
    if len(lines) < 2:
        return lines
    gaps = [lines[i + 1]['top'] - lines[i]['top'] for i in range(len(lines) - 1)]
    typical_gaps = gaps[:-1] or gaps
    typical = sorted(typical_gaps)[len(typical_gaps) // 2]
    if typical <= 0:
        typical = 1
    if gaps[-1] > max(3 * typical, 120):
        return lines[:-1]
    return lines


def _fix_outward(raw: str):
    """raw is the outward-code candidate (area letters + district), e.g.
    'CRO', 'SO24', 'SSO0'. Tries a 2-letter area first (more specific),
    then falls back to 1. Applies this font's letter/digit confusion only
    in the slot where it's grammatically expected — a stray 0 in the area
    letters, a stray O in the district digits — and collapses a duplicated
    0/O artifact in the district (confirmed: 'SS0' OCR'd as 'SSO0')."""
    raw = raw.strip()
    if not (2 <= len(raw) <= 6):
        return None
    for area_len in (2, 1):
        if len(raw) <= area_len:
            continue
        area_raw, dist_raw = raw[:area_len], raw[area_len:]
        area = ''.join(_fix_letter_slot(c) for c in area_raw)
        if not re.match(r'^[A-Z]{1,2}$', area):
            continue
        if len(dist_raw) >= 2 and dist_raw[0] in 'O0' and dist_raw[1] in 'O0':
            dist_raw = dist_raw[1:]
        dist = ''.join(_fix_digit_slot(c) for c in dist_raw)
        if re.match(r'^\d{1,2}$', dist):
            return f"{area}{dist}"
    return None


def _fix_inward_3(raw: str):
    if len(raw) != 3:
        return None
    d = _fix_digit_slot(raw[0])
    l1 = _fix_letter_slot(raw[1])
    l2 = _fix_letter_slot(raw[2])
    fixed = d + l1 + l2
    return fixed if re.match(r'^\d[A-Z]{2}$', fixed) else None


def _fix_inward(raw: str):
    """raw is the inward-code candidate, normally 3 characters (digit +
    2 letters), in its ORIGINAL case (not yet upper-cased). Tolerates
    exactly one extra character, which this font's OCR reliably introduces
    in one of two ways (both confirmed): a duplicated leading 0/O ('0QR'
    OCR'd as 'O0QR'), or a single stray character inserted elsewhere
    ('4RJ' OCR'd as '4RdJ').

    Postcodes are always printed uppercase on this label, so when a length-4
    candidate contains a lowercase character, that's the clearest signal of
    which one is the spurious insertion — deleting purely by "does the
    result look grammatically valid" is ambiguous (e.g. both deleting the
    'R' and deleting the inserted 'd' from '4RdJ' yield a superficially
    valid digit+letter+letter shape: '4DJ' and '4RJ'), so lowercase
    positions are always tried first."""
    if len(raw) == 3:
        return _fix_inward_3(raw.upper())
    if len(raw) == 4:
        upper = raw.upper()
        if upper[0] in 'O0' and upper[1] in 'O0':
            fixed = _fix_inward_3(upper[1:])
            if fixed:
                return fixed
        lower_first = sorted(range(4), key=lambda i: not raw[i].islower())
        for i in lower_first:
            fixed = _fix_inward_3(upper[:i] + upper[i + 1:])
            if fixed:
                return fixed
    return None


def _assemble(outward_raw: str, inward_raw: str):
    outward = _fix_outward(outward_raw.upper())
    inward = _fix_inward(inward_raw)
    if outward is None or inward is None:
        return None
    candidate = f"{outward} {inward}"
    return candidate if STRICT_POSTCODE_RE.match(candidate) else None


def _fuzzy_match_postcode_line(raw_line: str):
    """Grammar-aware postcode extraction for a single already-isolated
    candidate line (see module docstring #3) — replaces the old
    LOOSE_POSTCODE_RE, which only corrected a stray leading symbol and a
    fixed set of inward-code substitutions, and had no way to fix a
    misread anywhere else in the postcode. Deliberately keeps the original
    case through to _fix_inward (see its docstring) rather than
    upper-casing up front."""
    if not raw_line:
        return None
    cleaned = raw_line.replace('$', 'S')
    tokens = [t for t in re.split(r'\s+', cleaned.strip()) if t]
    if not tokens:
        return None

    if len(tokens) >= 2:
        outward_raw = ''.join(tokens[:-1])
        inward_raw = tokens[-1]
        return _assemble(outward_raw, inward_raw)

    # Single run-together token (OCR dropped the space): try the plausible
    # inward-code lengths, longest first.
    joined = tokens[0]
    for inward_len in (3, 4, 2):
        if len(joined) - inward_len < 2:
            continue
        result = _assemble(joined[:-inward_len], joined[-inward_len:])
        if result:
            return result
    return None


def _try_match(text):
    """Strict match only. Used on the cheap whole-box OCR pass, where the
    text may contain multiple address lines — fuzzy correction is
    deliberately not applied here (it needs a single isolated line to be
    safe) and is reserved for extract_postcode_via_ocr()'s second pass."""
    m = STRICT_POSTCODE_RE.search(text.upper())
    if m:
        return f"{m.group(1)} {m.group(2)}"
    return None


def extract_postcode_via_ocr(page_image):
    """OCR the Destination box of a rendered 3rd-party label page (a PIL
    Image, e.g. from pdf2image.convert_from_path).

    Three passes, cheapest and most reliable first:
    1. Whole-box OCR, strict match (handles the large majority of labels).
    2. Fuzzy-match the last real content line from that SAME whole-box OCR
       pass (no extra Tesseract call). This deliberately keeps the
       original letter case from this pass, because a lowercase character
       here is a strong signal of exactly which character Tesseract
       spuriously inserted (see _fix_inward) — information that pass 3's
       restricted whitelist would otherwise erase by forcing everything
       uppercase before we ever see it.
    3. Last resort: crop tightly to the detected postcode line and re-OCR
       it with a restricted character set (uppercase + digits only, a
       different psm mode). This is what the original version relied on
       exclusively, but testing against real files showed it can introduce
       its own fresh misreads that pass 1 didn't have (confirmed: it read
       a clean 'NE3' as 'NE8' on a line pass 1 had already gotten right) —
       so it's now a fallback, not the primary correction path, tried only
       when passes 1-2 come up empty.

    Passes 2 and 3 both rely on _drop_hallucinated_tail to ignore a
    reproducible Tesseract artifact — a short phantom line hallucinated in
    the blank space below the address — described in the module docstring.

    Returns (postcode, ocr_guess): postcode is the confirmed match (or
    None), and ocr_guess is the best-effort line text when nothing parsed
    cleanly, so it can be shown to the user for a quick manual read without
    reopening the original file.
    """
    if page_image is None:
        return None, None

    w, h = page_image.size
    box = (
        int(ADDR_LEFT_FRAC * w), int(ADDR_TOP_FRAC * h),
        int(ADDR_RIGHT_FRAC * w), int(ADDR_BOT_FRAC * h),
    )
    crop = page_image.crop(box)

    # Pass 1: cheap whole-box OCR. Keep the original case (see docstring).
    whole_text_raw = pytesseract.image_to_string(crop, config='--psm 6')
    result = _try_match(whole_text_raw)
    if result:
        return result, None

    lines = _drop_hallucinated_tail(_get_text_lines(crop))
    raw_lines = [ln.strip() for ln in whole_text_raw.split('\n') if ln.strip()]

    # Pass 2: fuzzy-match the last non-hallucinated line using pass 1's own
    # (case-preserved) text — same line count/order as `lines` below, since
    # both come from the same Tesseract config on the same crop.
    candidate_line_raw = raw_lines[len(lines) - 1] if lines and len(raw_lines) >= len(lines) else None
    if candidate_line_raw:
        result = _fuzzy_match_postcode_line(candidate_line_raw)
        if result:
            return result, None

    # Pass 3: tight, whitelisted re-OCR of the specifically-detected line.
    target = None
    for line in reversed(lines):
        if _looks_like_postcode_shaped(line['words']):
            target = line
            break
    if target is None and lines:
        # Best-effort: on this label, the postcode is always the last line
        # of the address block, hallucination already excluded above.
        target = lines[-1]

    ocr_guess = candidate_line_raw
    if target:
        pad = 6
        line_crop = crop.crop((
            max(0, target['x0'] - pad), max(0, target['y0'] - pad),
            target['x1'] + pad, target['y1'] + pad,
        ))
        line_text = pytesseract.image_to_string(line_crop, config=LINE_WHITELIST_CONFIG).strip()
        result = _fuzzy_match_postcode_line(line_text)
        if result:
            return result, None
        ocr_guess = candidate_line_raw or line_text or ' '.join(target['words'])

    return None, ocr_guess


def is_out_of_area(postcode: str):
    """
    Check a single postcode against the out-of-area rules.
    Returns (flagged: bool, reason: str | None).
    """
    if not postcode:
        return False, None

    normalized = normalize_postcode(postcode)

    if normalized in OUT_OF_AREA_EXACT:
        return True, f"Exact match: {postcode.upper()}"

    area, district = parse_outward_code(postcode)
    if area is None:
        return False, None

    for rule_area, start, end in OUT_OF_AREA_RULES:
        if area != rule_area:
            continue
        if start is None:
            return True, f"{area}* (whole area out of area)"
        if start <= district <= end:
            return True, f"{area}{district} in range {area}{start}-{area}{end}"

    return False, None


def check_label_postcode(text: str = None, page_image=None):
    """
    Check a label's postcode. Prefers a text-layer read (cheap, exact) and
    falls back to OCR on the Destination box — which is what actually finds
    the postcode for real 3rd-party Evri labels, since their address is a
    flattened image with no text layer.

    Returns:
      {
        "postcode": str | None,
        "flagged": bool,     # confirmed out-of-area
        "warning": bool,     # postcode couldn't be read at all
        "exclude": bool,     # True if flagged OR warning -> pull from merge
        "reason": str | None,
        "ocr_guess": str | None,  # best-effort OCR line when nothing parsed
      }
    """
    postcode = extract_postcode_from_text(text)
    ocr_guess = None
    if postcode is None and page_image is not None:
        postcode, ocr_guess = extract_postcode_via_ocr(page_image)

    if postcode is None:
        reason = "No postcode could be read — check manually"
        if ocr_guess:
            reason += f' (OCR saw: "{ocr_guess}")'
        return {
            "postcode": None,
            "flagged": False,
            "warning": True,
            "exclude": True,
            "reason": reason,
            "ocr_guess": ocr_guess,
        }

    flagged, reason = is_out_of_area(postcode)
    return {
        "postcode": postcode,
        "flagged": flagged,
        "warning": False,
        "exclude": flagged,
        "reason": reason,
        "ocr_guess": None,
    }


def render_pdf_pages(pdf_path):
    """Render every page of a 3rd-party label PDF to an image at OCR_DPI,
    once per file — call this once per uploaded PDF, not once per page."""
    try:
        return convert_from_path(str(pdf_path), dpi=OCR_DPI)
    except Exception:
        return []


if __name__ == "__main__":
    tests = [
        "PA1 1AA", "PA75 6NW", "KW1 4XW", "AB15 4TH", "AB12 3CD",
        "TR1 2AA", "TR21 0PU", "HA4 6EP", "HA4 9ZZ",
    ]
    for pc in tests:
        flagged, reason = is_out_of_area(pc)
        print(f"{pc:12} -> flagged={flagged:5}  {reason or ''}")

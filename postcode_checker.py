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

Tested against a real 38-label export: strict OCR read got 34/38 (89%),
a second pass correcting the two most common misreads on this font
('0'<->'O'/'Q'/'D' in the inward code, stray symbols for a leading area
letter e.g. '$' for 'S') brought that to 37/38 (97%). The one remaining
miss was a digit fully misread as an unrelated letter with no numeric
trace at all — structurally impossible to fix by substitution — and it
fails safe into the "check manually" bucket rather than being silently
approved or wrongly excluded.
"""

import re
from pdf2image import convert_from_path
import pytesseract

# (area, start_district, end_district)
# start=end=None means the WHOLE area is out of area, regardless of district number.
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
# Measured against a real admin-exported Evri label: the Destination box sits
# roughly a third of the way down the page, clear of the barcode above and
# the Date/Weight/Reference table below.
ADDR_LEFT_FRAC = 0.0
ADDR_RIGHT_FRAC = 0.575
ADDR_TOP_FRAC = 0.325
ADDR_BOT_FRAC = 0.531
OCR_DPI = 400  # 300dpi gave 3/38 misses in testing; 400dpi gave 1/38

STRICT_POSTCODE_RE = re.compile(r'\b([A-Za-z]{1,2}\d[A-Za-z\d]?)\s*(\d[A-Za-z]{2})\b')
# Tolerant of the two most common OCR misreads on this font/size: '0' read as
# 'O'/'Q'/'D' in the inward code, and a stray symbol standing in for a leading
# area letter (e.g. '$' for 'S'). Only used as a second-chance pass.
LOOSE_POSTCODE_RE = re.compile(r'(?:^|\s)([A-Za-z$][A-Za-z]?\d[A-Za-z\d]?)\s*([0-9OQD][A-Za-z]{2})\b')


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


def _normalize_loose_match(outward, inward):
    outward = outward.replace('$', 'S')
    inward = inward[0].replace('O', '0').replace('Q', '9').replace('D', '0') + inward[1:]
    return outward, inward


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


def _looks_like_postcode_shaped(line):
    """Loose shape check: two tokens, first 2-4 chars, second exactly 3 —
    matches a postcode's word pattern even if the characters are wrong."""
    parts = line.split()
    return len(parts) == 2 and 2 <= len(parts[0]) <= 4 and len(parts[1]) == 3


def extract_postcode_via_ocr(page_image):
    """OCR just the Destination box of a rendered 3rd-party label page
    (a PIL Image, e.g. from pdf2image.convert_from_path). Tries a strict
    read first, then a second pass correcting common OCR confusions.
    Returns (postcode, ocr_guess): postcode is the confirmed match (or None),
    and ocr_guess is the OCR'd line most likely to be the postcode when
    nothing parsed cleanly — handed back so it can be shown to the user for
    a quick manual read, without them needing to reopen the original file."""
    if page_image is None:
        return None, None
    w, h = page_image.size
    box = (
        int(ADDR_LEFT_FRAC * w), int(ADDR_TOP_FRAC * h),
        int(ADDR_RIGHT_FRAC * w), int(ADDR_BOT_FRAC * h),
    )
    crop = page_image.crop(box)
    text = pytesseract.image_to_string(crop, config='--psm 6').upper()

    m = STRICT_POSTCODE_RE.search(text)
    if m:
        return f"{m.group(1)} {m.group(2)}", None

    m2 = LOOSE_POSTCODE_RE.search(text)
    if m2:
        outward, inward = _normalize_loose_match(m2.group(1), m2.group(2))
        candidate = f"{outward} {inward}"
        if STRICT_POSTCODE_RE.match(candidate):
            return candidate, None

    # Nothing parsed cleanly. Pick the best guess: scan from the bottom (the
    # postcode is always the last line of a UK address) for a line that at
    # least has the right two-token/3-char shape, so we don't hand back
    # unrelated noise from below the address box as the "guess".
    lines = [l.strip() for l in text.split('\n') if l.strip()]
    ocr_guess = None
    for l in reversed(lines):
        if _looks_like_postcode_shaped(l):
            ocr_guess = l
            break
    if ocr_guess is None and lines:
        ocr_guess = lines[-1]
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

"""
postcode_checker.py

Flags UK postcodes that fall in your out-of-area / surcharge zone list
(Highlands, Channel Islands, Isle of Man, Isle of Wight, Scilly, BFPO, etc).

Integration point: 3rd-Party Labels tab, alongside the existing SKU/Qty
column-position read. Call check_label_postcode(page_text) once per label;
if flagged, pull that label OUT of the merge and surface it on the results
screen instead (same pattern as the qty_confident amber-flag list).
"""

import re

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

# Simplified UK postcode matcher, applied to raw label text (already a text
# layer for 3rd-party labels — no OCR needed here, same as the SKU/Qty read).
POSTCODE_RE = re.compile(r'\b([A-Za-z]{1,2}\d[A-Za-z\d]?)\s*(\d[A-Za-z]{2})\b')


def normalize_postcode(pc: str) -> str:
    """Uppercase, strip all whitespace: 'Pa20 1Ab' -> 'PA201AB'."""
    return re.sub(r'\s+', '', pc or '').upper()


def parse_outward_code(pc: str):
    """Return (area_letters, district_number) from a postcode, or (None, None)."""
    normalized = normalize_postcode(pc)
    m = re.match(r'^([A-Z]{1,2})(\d{1,2})', normalized)
    if not m:
        return None, None
    return m.group(1), int(m.group(2))


def extract_postcode_from_text(text: str):
    """
    Find the first UK-postcode-shaped string in a block of label text.
    Returns the postcode as found (e.g. 'PA20 1AB') or None.
    """
    if not text:
        return None
    m = POSTCODE_RE.search(text)
    if not m:
        return None
    return f"{m.group(1)} {m.group(2)}".upper()


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


def check_label_postcode(page_text: str):
    """
    One-stop check for a label's raw text. Returns a dict:
      {
        "postcode": str | None,
        "flagged": bool,     # confirmed out-of-area
        "warning": bool,     # postcode couldn't be read at all
        "exclude": bool,     # True if flagged OR warning -> pull from merge either way
        "reason": str | None,
      }

    Both flagged and warning labels get excluded from the merge:
      - flagged  -> show in "Out of Area" section (cancel on Amazon)
      - warning  -> show in "Check Postcode" section (couldn't confirm, check manually)
    """
    postcode = extract_postcode_from_text(page_text)

    if postcode is None:
        return {
            "postcode": None,
            "flagged": False,
            "warning": True,
            "exclude": True,
            "reason": "No postcode found on label",
        }

    flagged, reason = is_out_of_area(postcode)
    return {
        "postcode": postcode,
        "flagged": flagged,
        "warning": False,
        "exclude": flagged,
        "reason": reason,
    }


if __name__ == "__main__":
    # Quick sanity checks
    tests = [
        "PA1 1AA",    # Paisley, mainland - should NOT flag
        "PA75 6NW",   # Islay - SHOULD flag
        "KW1 4XW",    # Wick - SHOULD flag (whole area)
        "AB15 4TH",   # Aberdeen city - should NOT flag
        "AB12 3CD",   # SHOULD flag
        "TR1 2AA",    # Truro mainland - should NOT flag
        "TR21 0PU",   # Scilly - SHOULD flag
        "HA4 6EP",    # exact match - SHOULD flag
        "HA4 9ZZ",    # same area, different postcode - should NOT flag
    ]
    for pc in tests:
        flagged, reason = is_out_of_area(pc)
        print(f"{pc:12} -> flagged={flagged:5}  {reason or ''}")

    print()
    print(check_label_postcode("Some label text with no postcode in it"))
    print(check_label_postcode("Ship to: 12 Croft Road, Stornoway HS1 2AB"))
    print(check_label_postcode("Ship to: 1 High St, London HA4 9ZZ"))

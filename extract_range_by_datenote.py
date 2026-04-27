#!/usr/bin/env python3
"""
Extract an inclusive page range from a PDF based on two textual markers.

Typical use case:
  Your LaTeX source contains markers like \\datenote{2025-01-10}
  and \\datenote{2025-02-03}. If the resulting PDF contains searchable
  text with these dates, this script finds the first page containing the
  begin marker and the first page containing the end marker, then writes
  those pages to a new PDF.

Examples:
  python extract_range_by_datenote.py input.pdf output.pdf \
      --begin 2025-01-10 --end 2025-02-03

  # match literal macro text if that text appears in the PDF
  python extract_range_by_datenote.py input.pdf output.pdf \
      --begin r'\\datenote\\{2025-01-10\\}' --end r'\\datenote\\{2025-02-03\\}' --regex
"""

import argparse
import re
import sys
from pathlib import Path

try:
    import fitz  # PyMuPDF
except ImportError as exc:
    raise SystemExit(
        "This script requires PyMuPDF. Install it with: pip install pymupdf"
    ) from exc

try:
    from pypdf import PdfReader, PdfWriter
except ImportError as exc:
    raise SystemExit(
        "This script requires pypdf. Install it with: pip install pypdf"
    ) from exc


def normalize_text(text: str) -> str:
    """Light normalization to make matching more robust."""
    text = text.replace("\u00a0", " ")
    text = re.sub(r"[ \t]+", " ", text)
    return text


def page_texts(pdf_path: Path) -> list[str]:
    doc = fitz.open(pdf_path)
    try:
        return [normalize_text(page.get_text("text")) for page in doc]
    finally:
        doc.close()



def find_marker_page(
    texts: list[str],
    marker: str,
    *,
    use_regex: bool,
    ignore_case: bool,
) -> int:
    flags = re.IGNORECASE if ignore_case else 0

    for i, text in enumerate(texts):
        if use_regex:
            if re.search(marker, text, flags=flags):
                return i
        else:
            haystack = text.lower() if ignore_case else text
            needle = marker.lower() if ignore_case else marker
            if needle in haystack:
                return i

    raise ValueError(f"Marker not found in PDF text: {marker!r}")



def extract_pages(input_pdf: Path, output_pdf: Path, start_idx: int, end_idx: int) -> None:
    reader = PdfReader(str(input_pdf))
    writer = PdfWriter()

    for i in range(start_idx, end_idx + 1):
        writer.add_page(reader.pages[i])

    output_pdf.parent.mkdir(parents=True, exist_ok=True)
    with output_pdf.open("wb") as f:
        writer.write(f)



def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Extract pages between two textual markers in a PDF."
    )
    parser.add_argument("input_pdf", type=Path, help="Source PDF")
    parser.add_argument("output_pdf", type=Path, help="Output PDF")
    parser.add_argument(
        "--begin",
        required=True,
        help="Text or regex for the begin marker",
    )
    parser.add_argument(
        "--end",
        required=True,
        help="Text or regex for the end marker",
    )
    parser.add_argument(
        "--regex",
        action="store_true",
        help="Interpret --begin and --end as regular expressions",
    )
    parser.add_argument(
        "--ignore-case",
        action="store_true",
        help="Case-insensitive matching",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Print page numbers and a short status message",
    )
    return parser



def main() -> int:
    parser = build_parser()
    args = parser.parse_args()

    if not args.input_pdf.exists():
        print(f"Input PDF does not exist: {args.input_pdf}", file=sys.stderr)
        return 2

    texts = page_texts(args.input_pdf)

    try:
        start_idx = find_marker_page(
            texts,
            args.begin,
            use_regex=args.regex,
            ignore_case=args.ignore_case,
        )
        end_idx = find_marker_page(
            texts,
            args.end,
            use_regex=args.regex,
            ignore_case=args.ignore_case,
        )
    except ValueError as e:
        print(str(e), file=sys.stderr)
        return 1

    if start_idx >= end_idx:
        print(
            f"Begin marker occurs after end marker: begin page {start_idx + 1}, "
            f"end page {end_idx + 1}",
            file=sys.stderr,
        )
        return 1

    end_idx = end_idx - 1

    extract_pages(args.input_pdf, args.output_pdf, start_idx, end_idx)

    if args.verbose:
        print(
            f"Extracted pages {start_idx + 1}-{end_idx + 1} "
            f"from {args.input_pdf} to {args.output_pdf}"
        )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

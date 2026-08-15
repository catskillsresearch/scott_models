#!/usr/bin/env python3
"""Extract a PDF into a human-verifiable Markdown draft under sources/.

The original Scott-domain papers are scanned or have unreliable text layers.
This script produces a *draft* transcription with explicit page markers and
`[? …]` flags on suspicious tokens. A human must compare each page to the PDF
and update verification_status in the YAML front matter.

Usage:
    python3 scripts/pdf_to_source_md.py ScottContinLatt1972.pdf
    python3 scripts/pdf_to_source_md.py --all
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOURCES = ROOT / "sources"

# Canonical sequence for the three Scott historical sources (1972, 1981, 1982).
CATALOG: dict[str, dict[str, str]] = {
    "ScottContinLatt1972.pdf": {
        "md": "ScottContinLatt1972.md",
        "title": "Continuous Lattices",
        "author": "Dana Scott",
        "year": "1972",
        "citation_key": "Sco72",
        "bib": (
            "Scott, D. Continuous lattices. In: Toposes, Algebraic Geometry and "
            "Logic (F. W. Lawvere, ed.), LNM 274, Springer, 1972, pp. 97–136."
        ),
        "alias": "PRG-7 (Oxford Technical Monograph, 1971; textually identical to LNM 274)",
    },
    "PRG19.pdf": {
        "md": "PRG19.md",
        "title": "Lectures on a Mathematical Theory of Computation",
        "author": "Dana Scott",
        "year": "1981",
        "citation_key": "Sco81",
        "bib": (
            "Scott, D. Lectures on a Mathematical Theory of Computation. "
            "Technical Monograph PRG-19, Oxford University Computing Laboratory, May 1981."
        ),
        "alias": "The PRG-19 blue pamphlet (neighborhood systems)",
    },
    "Domains_for_Denotational_Semantics.pdf": {
        "md": "Domains_for_Denotational_Semantics.md",
        "title": "Domains for Denotational Semantics",
        "author": "Dana Scott",
        "year": "1982",
        "citation_key": "Sco82",
        "bib": (
            "Scott, D. Domains for Denotational Semantics. "
            "ICALP 1982, LNCS 140, pp. 577–613."
        ),
        "alias": "Information systems presentation (ICALP 1982)",
    },
}

# Tokens that often indicate OCR corruption in these sources.
SUSPICIOUS = re.compile(
    r"(?<![A-Za-z])"
    r"(oontinuous|Zattioes|lattiae|Proeosition|injeative|k-A|F--|~--|\[\-\-|"
    r"turnstile|ConA\.|DirSup|feebly|spaae|m a t h|t h e o r y|a n d)"
    r"(?![A-Za-z])",
    re.IGNORECASE,
)

# Likely section headings in Scott papers.
SECTION = re.compile(
    r"^(\d+\.?\s+[A-Z][A-Za-z ,\-']+|"
    r"DEFINITION|THEOREM|PROPOSITION|LEMMA|COROLLARY|ABSTRACT|CONTENTS|REFERENCES)\b",
    re.MULTILINE,
)


@dataclass
class PageText:
    number: int
    text: str
    method: str  # "pdftotext" | "ocr"


def pdf_page_count(pdf: Path) -> int:
    out = subprocess.check_output(
        ["pdfinfo", str(pdf)], text=True, stderr=subprocess.DEVNULL
    )
    for line in out.splitlines():
        if line.startswith("Pages:"):
            return int(line.split(":")[1].strip())
    raise RuntimeError(f"Could not read page count for {pdf}")


def extract_page_pdftotext(pdf: Path, page: int) -> str:
    return subprocess.check_output(
        ["pdftotext", "-f", str(page), "-l", str(page), "-layout", str(pdf), "-"],
        text=True,
        stderr=subprocess.DEVNULL,
    )


def extract_page_ocr(pdf: Path, page: int, tmp: Path) -> str:
    prefix = tmp / f"p{page}"
    subprocess.run(
        ["pdftoppm", "-f", str(page), "-l", str(page), "-r", "300", "-png", str(pdf), str(prefix)],
        check=True,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    img = Path(f"{prefix}-{page:02d}.png")
    if not img.exists():
        # pdftoppm naming varies
        candidates = list(tmp.glob(f"p{page}-*.png"))
        if not candidates:
            return ""
        img = candidates[0]
    return subprocess.check_output(
        ["tesseract", str(img), "stdout", "-l", "eng", "--psm", "1"],
        text=True,
        stderr=subprocess.DEVNULL,
    )


def page_has_text(text: str) -> bool:
    stripped = re.sub(r"\s+", "", text)
    return len(stripped) > 40


def extract_all_pages(pdf: Path, force_ocr: bool) -> tuple[list[PageText], str]:
    n = pdf_page_count(pdf)
    pages: list[PageText] = []
    ocr_pages = 0

    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir)
        for p in range(1, n + 1):
            if force_ocr:
                text = extract_page_ocr(pdf, p, tmp)
                method = "ocr"
                ocr_pages += 1
            else:
                text = extract_page_pdftotext(pdf, p)
                if not page_has_text(text):
                    text = extract_page_ocr(pdf, p, tmp)
                    method = "ocr"
                    ocr_pages += 1
                else:
                    method = "pdftotext"
            pages.append(PageText(p, text.rstrip(), method))

    if ocr_pages == n:
        extraction = "ocr (all pages)"
    elif ocr_pages:
        extraction = f"pdftotext + ocr ({ocr_pages}/{n} pages OCR)"
    else:
        extraction = "pdftotext"
    return pages, extraction


def flag_suspicious(line: str) -> str:
    def repl(m: re.Match[str]) -> str:
        return f"[?{m.group(0)}]"
    return SUSPICIOUS.sub(repl, line)


def normalize_line(line: str) -> str:
    # Collapse internal runs of spaces but keep intentional layout somewhat.
    line = line.rstrip()
    if not line.strip():
        return ""
    return flag_suspicious(line)


def format_page(page: PageText) -> str:
    lines = [normalize_line(ln) for ln in page.text.splitlines()]
    body = "\n".join(ln for ln in lines if ln is not None)
    return f"\n<!-- page {page.number} ({page.method}) -->\n\n{body}\n"


def build_checklist(pages: list[PageText]) -> list[str]:
    """Heuristic section checklist from heading-like lines."""
    items: list[str] = []
    seen: set[str] = set()
    for pg in pages:
        for line in pg.text.splitlines():
            s = line.strip()
            if len(s) < 4 or len(s) > 80:
                continue
            if SECTION.match(s):
                key = s[:60]
                if key not in seen:
                    seen.add(key)
                    items.append(f"- [ ] p.{pg.number}: {s}")
    return items[:40]  # cap for readability


def render_md(pdf: Path, meta: dict[str, str], pages: list[PageText], extraction: str) -> str:
    checklist = build_checklist(pages)
    checklist_block = "\n".join(checklist) if checklist else "- [ ] Full document (no section headings detected automatically)"

    front = f"""---
source_pdf: {pdf.name}
title: "{meta['title']}"
author: {meta['author']}
year: {meta['year']}
citation_key: {meta['citation_key']}
alias: "{meta['alias']}"
bibliography: "{meta['bib']}"
pages: {len(pages)}
extraction_method: "{extraction}"
verification_status: draft
verified_by: null
verified_date: null
---

# {meta['title']}

**Author:** {meta['author']} ({meta['year']})  
**Source file:** `{pdf.name}`  
**Also known as:** {meta['alias']}

> **Human verification required.** This file is a machine-generated *draft*.
> Compare each `<!-- page N -->` block to the PDF. Correct OCR errors, restore
> mathematical notation, and check off items below. When done, set
> `verification_status: verified` in the YAML front matter and record your name
> and date.

## Bibliography

{meta['bib']}

## Verification checklist

{checklist_block}

---

## Transcription

"""
    body = "".join(format_page(p) for p in pages)
    return front + body


def write_transcription(pdf: Path, force_ocr: bool = False) -> Path:
    if pdf.name not in CATALOG:
        raise SystemExit(f"Unknown PDF {pdf.name}. Add it to CATALOG in this script.")
    meta = CATALOG[pdf.name]
    out = SOURCES / meta["md"]
    pages, extraction = extract_all_pages(pdf, force_ocr)
    md = render_md(pdf, meta, pages, extraction)
    out.write_text(md, encoding="utf-8")
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pdf", nargs="?", help="PDF filename in repo root")
    parser.add_argument("--all", action="store_true", help="Process all catalogued PDFs")
    parser.add_argument("--ocr", action="store_true", help="Force OCR for every page")
    args = parser.parse_args()

    if args.all:
        pdfs = [ROOT / name for name in CATALOG]
    elif args.pdf:
        pdfs = [ROOT / Path(args.pdf).name]
    else:
        parser.print_help()
        sys.exit(1)

    SOURCES.mkdir(exist_ok=True)
    for pdf in pdfs:
        if not pdf.exists():
            print(f"SKIP (missing): {pdf.name}", file=sys.stderr)
            continue
        out = write_transcription(pdf, force_ocr=args.ocr)
        n = len(out.read_text(encoding="utf-8").splitlines())
        print(f"Wrote {out.relative_to(ROOT)} ({n} lines)")


if __name__ == "__main__":
    main()

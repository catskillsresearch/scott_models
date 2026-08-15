#!/usr/bin/env python3
"""Clean a source transcription: drop book page numbers, normalize spaces, reflow paragraphs."""

from __future__ import annotations

import argparse
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# LNM printed page numbers (97–136) on their own line.
BOOK_PAGE = re.compile(r"^\s*(9[7-9]|1[0-3][0-9])\s*$")

# Page boundary comments from pdf_to_source_md.py (optional removal).
PAGE_COMMENT = re.compile(r"^\s*<!-- page \d+.*-->\s*$")

# Standalone subscript digits split by pdftotext (e.g. T0 with 0 on next line).
LONE_SUBSCRIPT = re.compile(r"^\s*([0-9])\s*$")

HEADING = re.compile(
    r"^(ABSTRACT|CONTENTS|REFERENCES|BY|"
    r"CONTINUOUS|LATTICES|"
    r"\d+[.,]?\s+[A-Z].*|"
    r"\d+\.\d+\s+(Proposition|Definition|Theorem|Lemma|Corollary)|"
    r"Definition\.|Proof:|Remark\.|"
    r"l\s*\.\s*\d+\s|"
    r"Scott,\s+D\.)",
    re.IGNORECASE,
)


def normalize_spaces(s: str) -> str:
    return re.sub(r" +", " ", s.strip())


def is_book_page(line: str) -> bool:
    return bool(BOOK_PAGE.match(line))


def is_heading(line: str) -> bool:
    s = normalize_spaces(line)
    if not s:
        return False
    if HEADING.match(s):
        return True
    # Short all-caps lines (title fragments).
    letters = re.sub(r"[^A-Za-z]", "", s)
    if letters and letters.isupper() and len(s) < 60:
        return True
    return False


def should_break_paragraph(prev: str, nxt: str) -> bool:
    if not prev or not nxt:
        return True
    if is_heading(nxt):
        return True
    # Colon mid-sentence (next line continues lowercase).
    if prev.rstrip().endswith(":") and nxt and nxt[0].islower():
        return False
    # Previous ends a sentence or block.
    if re.search(r"[.!?]\s*$", prev):
        return True
    if prev.rstrip().endswith(":") and nxt and nxt[0].isupper():
        return True
    # Contents list items.
    if re.match(r"^\d+\.\s+\S", nxt) and len(nxt) < 80:
        return True
    return False


def join_pair(buf: str, line: str) -> str:
    if buf.endswith("-"):
        if line and line[0].islower():
            return buf[:-1] + line  # circum- + stance
        return buf + line  # Church- + Curry
    return buf + " " + line


def join_lines(lines: list[str]) -> list[str]:
    out: list[str] = []
    buf = ""

    def flush() -> None:
        nonlocal buf
        if buf:
            out.append(buf)
            buf = ""

    for raw in lines:
        if PAGE_COMMENT.match(raw):
            continue
        if is_book_page(raw):
            continue

        line = normalize_spaces(raw)
        if not line:
            flush()
            continue

        # Reattach lone subscript digit (pdftotext splits T₀ across lines).
        m = LONE_SUBSCRIPT.match(raw)
        if m and buf:
            d = m.group(1)
            if re.search(r"T\s*$", buf):
                buf = re.sub(r"T\s*$", f"T{d}", buf)
                continue
            if re.search(r"T\s+-", buf):
                buf = re.sub(r"T\s+-", f"T{d} -", buf)
                continue

        if not buf:
            buf = line
            continue

        if should_break_paragraph(buf, line):
            flush()
            buf = line
            continue

        buf = join_pair(buf, line)

    flush()
    return out


def postprocess(paragraphs: list[str]) -> list[str]:
    out: list[str] = []
    i = 0
    while i < len(paragraphs):
        p = paragraphs[i]
        # Merge title lines: CONTINUOUS + LATTICES -> one line.
        if (
            i + 1 < len(paragraphs)
            and p.isupper()
            and paragraphs[i + 1].isupper()
            and len(p.split()) <= 2
            and len(paragraphs[i + 1].split()) <= 2
        ):
            out.append(f"{p} {paragraphs[i + 1]}")
            i += 2
            continue
        # Common pdftotext glitches.
        p = re.sub(r"\bT spaces\b", "T0 spaces", p)
        p = re.sub(r"\bby 0 defining\b", "by defining", p)
        p = re.sub(r"\bone--1\b", "one-1", p)
        p = re.sub(r"\bDas 1\b", "D as a", p)
        p = re.sub(r"\bas a a\b", "as a", p)
        out.append(p)
        i += 1
    return out


def clean_body(text: str) -> str:
    lines = text.splitlines()
    merged = join_lines(lines)
    merged = postprocess(merged)
    return "\n\n".join(merged) + "\n"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("md", type=Path, help="Markdown file under sources/")
    args = ap.parse_args()
    path = args.md if args.md.is_absolute() else ROOT / "sources" / args.md.name
    content = path.read_text(encoding="utf-8")
    marker = "## Transcription\n"
    if marker not in content:
        raise SystemExit(f"No {marker!r} section in {path}")
    head, body = content.split(marker, 1)
    cleaned = clean_body(body)
    path.write_text(head + marker + "\n\n" + cleaned, encoding="utf-8")
    print(f"Cleaned {path.name}: {len(body.splitlines())} -> {len(cleaned.splitlines())} lines")


if __name__ == "__main__":
    main()

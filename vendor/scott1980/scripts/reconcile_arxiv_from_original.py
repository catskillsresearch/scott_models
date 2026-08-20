#!/usr/bin/env python3
"""Rebuild arxiv.md inventory from arxiv_original.md goal-list tables."""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

LECTURE_HEADERS = {
    1: "### Lecture I: Domains by Neighborhoods",
    2: "### Lecture II: Approximable Mappings",
    3: "### Lecture III: Domain Constructs",
    4: "### Lecture IV: Fixed Points and Recursion",
    5: "### Lecture V: Typed λ-Calculus",
    6: "### Lecture VI: Domain Equations",
    7: "### Lecture VII: Computability in Effectively Given Domains",
    8: "### Lecture VIII: Retracts of the Universal Domain",
}

LECTURE_INTROS = {
    7: (
        "\nLecture VII establishes the recursion-theoretic foundations of domain theory.\n"
    ),
    8: (
        "\nLecture VIII covers retractions, projections, and the construction of the "
        "universal domain $U$. Formalization for these items is deferred; they are "
        "cataloged below in the same structured format as the rest of the monograph.\n"
    ),
}

CURRENT_LECTURE = 0


def normalize_header(name: str) -> str:
    name = name.strip().strip("*").strip()
    name = re.sub(r"^Def\b", "Definition", name)
    name = re.sub(r"^Prop\b", "Proposition", name)
    name = re.sub(r"^Thm\b", "Theorem", name)
    name = re.sub(r"^\*Table\b", "Table", name)
    if name.startswith("Examples "):
        name = name.replace("Examples ", "Example ", 1)
    return name


def parse_table_line(line: str) -> dict | None:
    if not (line.startswith("| **") or line.startswith("| *")):
        return None
    core = line.strip()
    if not core.startswith("|") or not core.endswith("|"):
        return None
    parts = [p.strip() for p in core[1:-1].split("|", 4)]
    if len(parts) != 5:
        return None
    name, kind, col3, col4, status_col = parts
    name = name.strip("*").strip()
    if name.startswith("Scott ") or name == "Item":
        return None
    # Lectures I–III: col3 = vision lines, col4 = lean target, col5 = status.
    # Lectures IV+: col3 = PRG line ref, col4 = statement, col5 = lean/status blob.
    if re.fullmatch(r"\d+[–-]\d+|\d+", col3):
        statement = col4
        lean_col = col4
        lean_blob = status_col
    else:
        statement = col3
        lean_col = col4
        lean_blob = status_col
    return {
        "name": name,
        "header": normalize_header(name),
        "kind": kind,
        "statement": statement,
        "lean_col": lean_col,
        "lean_blob": lean_blob,
    }


def parse_all_rows(text: str) -> list[dict]:
    rows: list[dict] = []
    current_lec = 1
    for line in text.splitlines():
        if line.startswith("### 1.2.VIII"):
            current_lec = 8
        elif line.startswith("### 1.2.VII"):
            current_lec = 7
        elif line.startswith("### 1.2.VI"):
            current_lec = 6
        elif line.startswith("### 1.2.V"):
            current_lec = 5
        elif line.startswith("### 1.2.IV"):
            current_lec = 4
        elif line.startswith("### 1.2.III"):
            current_lec = 3
        elif line.startswith("### 1.2.II"):
            current_lec = 2
        elif line.startswith("### 1.2 Lecture I"):
            current_lec = 1
        row = parse_table_line(line)
        if row:
            row["lecture"] = current_lec
            rows.append(row)
    return rows


def extract_overlay_keys(title: str) -> list[str]:
    """Pull inventory header keys from a §1.5 subsection title."""
    keys: list[str] = []
    title = title.split("—")[0].strip()
    head_re = re.compile(
        r"(Definition|Theorem|Example|Exercise|Factoid|Proposition|Lemma|Table)\s+"
        r"([\d.]+[A-Za-z-]*(?:\s*\([^)]*\))?(?:\s+order)?)"
    )
    for piece in re.split(r"\s*/\s*", title):
        piece = piece.strip()
        m = head_re.match(piece)
        if m:
            kind, ident = m.group(1), m.group(2).strip()
            ident = re.sub(r"^([\d.]+)\s+order$", r"\1 (order)", ident)
            keys.append(normalize_header(f"{kind} {ident}"))
        fm = re.search(r"Factoids?\s+([\d.A-Za-z,\s]+)", piece)
        if fm:
            for fid in re.findall(r"[\d.]+[A-Za-z]*", fm.group(1)):
                keys.append(normalize_header(f"Factoid {fid}"))
    return list(dict.fromkeys(keys))


def parse_section15(text: str) -> dict[str, str]:
    """Map normalized item headers → supplemental proof notes from §1.5."""
    overlays: dict[str, list[str]] = {}
    if "### 1.5 Selected proof notes" not in text:
        return {}
    sec = text.split("### 1.5 Selected proof notes", 1)[1]
    sec = sec.split("\n### 1.", 1)[0]
    chunks = re.split(r"^#### ", sec, flags=re.M)
    for chunk in chunks[1:]:
        title, _, body = chunk.partition("\n")
        body = body.strip()
        if not body:
            continue
        for key in extract_overlay_keys(title):
            overlays.setdefault(key, []).append(body)
    return {k: "\n\n".join(v) for k, v in overlays.items()}


def _lean_path(path: str) -> str:
    if path.startswith("Scott1980/"):
        return f"`{path}`"
    return f"`Scott1980/Neighborhood/{path}`"


def extract_lean_file(lean_blob: str, lean_col: str, statement: str, lecture: int = 0) -> str:
    for src in (lean_blob, lean_col, statement):
        m = re.search(r"`(Scott1980/[^`]+\.lean)`", src)
        if m:
            return f"`{m.group(1)}`"
        m = re.search(r"—\s*`([^`]+\.lean)`", src)
        if m:
            return _lean_path(m.group(1))
        m = re.search(
            r"`((?:Theorem|Definition|Proposition|Exercise|Example|Factoid)"
            r"[A-Za-z0-9]*\.lean)`",
            src,
        )
        if m:
            return _lean_path(m.group(1))
        m = re.search(r"\(`([^`]+\.lean)`\)", src)
        if m:
            return _lean_path(m.group(1))
    for src in (lean_blob, lean_col, statement):
        m = re.search(r"`([^`]+\.lean)`", src)
        if m:
            return _lean_path(m.group(1))
    if lean_blob.strip() in ("—", "-", ""):
        if lecture >= 8:
            return "— (Formalization deferred)"
        return "— (not yet started)"
    if "NeighborhoodSystem" in statement or "interUpTo" in statement:
        return "`Scott1980/Neighborhood/Basic.lean`"
    return "— (see proof notes)"


def status_for_item(header: str, lean_blob: str) -> str:
    blob = lean_blob.strip()
    m = re.search(
        r"(?:Definition|Theorem|Proposition|Lemma|Example|Exercise|Table|Factoid)\s+(\d+)\.(\d+|[A-Za-z])",
        header,
    )
    lec_num = int(m.group(1)) if m else 0
    item_tail = m.group(2) if m else ""
    item_num = int(item_tail) if item_tail.isdigit() else 0

    if blob in ("—", "-", ""):
        return "Deferred" if lec_num >= 8 else "Not Yet"

    if lec_num > 7 or (lec_num == 7 and item_num > 22):
        return "Deferred" if lec_num >= 8 else "Not Yet"

    if lec_num == 7 and item_num == 22:
        return (
            "Partial — algebraic core, regular-event layer, and DFA/NFA recognition Pass; "
            "effectively-given decider (C9–C10), language equivalence (C7b), infinite-word "
            "equations still open"
        )

    if re.search(r"\*\*Pass\*\*|\bPass\b", blob):
        if re.search(r"Still open|BLOCKED|not mechanised|deferred|C9|C10|C7b", blob, re.I):
            return "Partial — see proof notes for completed vs open obligations"
        return "Pass"

    return "Not Yet"


def math_target(row: dict) -> str:
    stmt = row["statement"].strip()
    return stmt or f"Scott PRG-19 {row['kind'].lower()}: {row['header']}."


def proof_notes(row: dict, overlay: str | None) -> str:
    parts: list[str] = []
    lean_col = row["lean_col"].strip()
    blob = row["lean_blob"].strip()

    cleaned = re.sub(r"^\*\*Pass\*\*\s*(\([^)]*\))?\s*—?\s*", "", blob)
    cleaned = re.sub(r"^Pass\s*(\([^)]*\))?\s*—?\s*", "", cleaned)

    if cleaned and cleaned not in ("**Pass**", "Pass", "—"):
        parts.append(cleaned)
    elif lean_col and lean_col not in ("**Pass**", "Pass", "—"):
        parts.append(lean_col)

    if overlay:
        parts.append(overlay)

    if not parts:
        if blob in ("—", "-", ""):
            return "Transcribed in `sources/PRG19.md`; formalization not yet started."
        return blob or lean_col
    return "\n\n".join(parts)


def entry_block(row: dict, overlay: str | None) -> str:
    header = row["header"]
    lean = extract_lean_file(row["lean_blob"], row["lean_col"], row["statement"], row["lecture"])
    status = status_for_item(header, row["lean_blob"])
    field = "Lean File" if lean.startswith("`") or lean.startswith("—") else "Lean Target"
    lines = [
        f"#### {header}",
        f"* **Mathematical Target:** {math_target(row)}",
        f"* **{field}:** {lean}",
        f"* **Proof Notes:** {proof_notes(row, overlay)}",
        f"* **Status:** {status}",
        "",
    ]
    return "\n".join(lines)


def extract_lecture_mermaid(arxiv_text: str, lecture_header: str) -> str:
    idx = arxiv_text.find(lecture_header)
    if idx == -1:
        return ""
    rest = arxiv_text[idx + len(lecture_header) :]
    m = re.search(r"```mermaid\n.*?\n```", rest, re.S)
    return ("\n" + m.group(0) + "\n") if m else ""


def main() -> None:
    orig = (ROOT / "arxiv_original.md").read_text()
    current = (ROOT / "arxiv.md").read_text()
    rows = parse_all_rows(orig)
    overlays = parse_section15(orig)

    first_lecture = current.find("### Lecture I:")
    build_idx = current.find("\n## Build\n")
    if first_lecture == -1 or build_idx == -1:
        raise SystemExit("Could not locate narrative boundaries in arxiv.md")
    prefix = current[:first_lecture].rstrip() + "\n\n"
    suffix = current[build_idx:]

    by_lecture: dict[int, list[dict]] = {i: [] for i in range(1, 9)}
    for row in rows:
        by_lecture[row["lecture"]].append(row)

    body_parts: list[str] = []
    for lec in range(1, 9):
        header = LECTURE_HEADERS[lec]
        body_parts.append(header)
        body_parts.append(extract_lecture_mermaid(current, header))
        if lec in LECTURE_INTROS:
            body_parts.append(LECTURE_INTROS[lec])
        for row in by_lecture[lec]:
            body_parts.append(entry_block(row, overlays.get(row["header"])))
        body_parts.append("---")
        body_parts.append("")

    out = prefix + "\n".join(body_parts).rstrip() + "\n" + suffix
    (ROOT / "arxiv.md").write_text(out)
    print(f"Wrote arxiv.md with {len(rows)} items; {len(overlays)} §1.5 overlays")


if __name__ == "__main__":
    main()

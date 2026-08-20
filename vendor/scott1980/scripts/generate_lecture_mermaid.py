#!/usr/bin/env python3
"""Generate Mermaid dependency diagrams for arxiv.md.

1. Per-lecture module graphs under each ``### Lecture …`` header.
2. A chapter-level inclusion hierarchy under the Introduction
   (``### Chapter inclusion hierarchy (Lean imports)``).

Primary edge source: `import Scott1980.Neighborhood.*` in each module.
Cross-lecture imports in per-lecture graphs appear as dashed edges from a compact
``LectNcore`` stub. Node labels combine Scott inventory titles (from arxiv.md)
with the Lean filename.

Run: python3 scripts/generate_lecture_mermaid.py [--write]
With --write, patches arxiv.md in place.
"""

from __future__ import annotations

import argparse
import re
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
NEIGH = ROOT / "Scott1980" / "Neighborhood"
ARXIV = ROOT / "arxiv.md"
SCOTT1980 = ROOT / "Scott1980.lean"

ROMAN = ("I", "II", "III", "IV", "V", "VI", "VII", "VIII")

# Wired import order → lecture boundaries (indices into the order list).
LECTURE_SPLITS = (0, 24, 36, 56, 79, 98, 129, 162)


def wired_order() -> list[str]:
    mods: list[str] = []
    for line in SCOTT1980.read_text(encoding="utf-8").splitlines():
        if ".Neighborhood." in line:
            mods.append(line.split(".")[-1])
    return mods


def parse_imports() -> dict[str, list[str]]:
    out: dict[str, list[str]] = {}
    for path in NEIGH.glob("*.lean"):
        imps: list[str] = []
        for line in path.read_text(encoding="utf-8").splitlines():
            if line.startswith("import Scott1980.Neighborhood."):
                imps.append(line.split(".")[-1])
            elif line.strip() and not line.startswith("/-") and not line.startswith("import"):
                if imps:
                    break
        out[path.stem] = imps
    return out


def parse_module_headers() -> dict[str, str]:
    headers: dict[str, str] = {}
    for path in NEIGH.glob("*.lean"):
        m = re.search(r"^# (.+?) \(Scott", path.read_text(encoding="utf-8"), re.MULTILINE)
        headers[path.stem] = m.group(1) if m else path.stem
    return headers


def parse_arxiv_labels() -> dict[str, list[str]]:
    """Map Lean module stem → Scott inventory row titles (may be many per file)."""
    text = ARXIV.read_text(encoding="utf-8")
    mod_labels: dict[str, list[str]] = defaultdict(list)
    for m in re.finditer(r"^#### (.+?)\n", text, re.MULTILINE):
        label = m.group(1)
        chunk = text[m.end() : m.end() + 700]
        lf = re.search(r"\* \*\*Lean File:\*\* `([^`]*)`", chunk)
        if not lf:
            continue
        raw = lf.group(1)
        if not raw.endswith(".lean"):
            continue
        mod = Path(raw).stem.split("/")[-1]
        if label not in mod_labels[mod]:
            mod_labels[mod].append(label)
    return mod_labels


def mermaid_id(name: str) -> str:
    out = re.sub(r"[^A-Za-z0-9_]", "_", name)
    if out and out[0].isdigit():
        out = "M_" + out
    return out or "node"


def node_label(mod: str, mod_labels: dict[str, list[str]], headers: dict[str, str]) -> str:
    labels = mod_labels.get(mod, [])
    if labels:
        if len(labels) == 1:
            title = labels[0]
        elif len(labels) <= 3:
            title = "<br/>".join(labels)
        else:
            title = labels[0] + f"<br/>(+{len(labels) - 1} items)"
    else:
        title = headers.get(mod, mod)
    title = title.replace('"', "'")
    return f"{title}<br/><i>{mod}.lean</i>"


def cluster_key(mod: str) -> str | None:
    """Merge dense families in Lecture VIII (and similar) for readability."""
    if mod.startswith("Theorem88") and mod != "Theorem88":
        return "Thm88chain"
    if mod.startswith("Exercise812"):
        return "Ex812"
    if mod.startswith("Exercise825"):
        return "Ex825"
    if mod in {
        "RationalPrimrec",
        "RecursiveCross",
        "IntervalPrimrec",
        "UComputablePresentation",
        "SplitU",
        "DAtomDecidable",
        "LevelSetPrimrec",
        "MinLevel",
        "SplitV",
        "VDiff",
        "UBisection2",
    }:
        return "Lect8helpers"
    return None


def build_lecture_diagram(
    lecture_idx: int,
    order: list[str],
    splits: tuple[int, ...],
    imports: dict[str, list[str]],
    mod_labels: dict[str, list[str]],
    headers: dict[str, str],
    mod_to_lecture: dict[str, int],
    *,
    cluster: bool,
) -> str:
    start, end = splits[lecture_idx], splits[lecture_idx + 1]
    mods = order[start:end]
    mod_set = set(mods)

    # Optional clustering (Lecture VIII).
    display_mod: dict[str, str] = {m: m for m in mods}
    if cluster and len(mods) > 28:
        groups: dict[str, list[str]] = defaultdict(list)
        for m in mods:
            key = cluster_key(m) or m
            groups[key].append(m)
        for key, members in groups.items():
            if len(members) > 1 and key != members[0]:
                for m in members:
                    display_mod[m] = key

    display_nodes = sorted(set(display_mod.values()), key=lambda x: (order.index(x) if x in mod_set else 9999, x))

    edges: set[tuple[str, str]] = set()
    external: dict[int, set[str]] = defaultdict(set)
    for mod in mods:
        src = display_mod[mod]
        for dep in imports.get(mod, []):
            if dep in mod_set:
                dst = display_mod[dep]
                if src != dst:
                    edges.add((dst, src))
            elif dep in mod_to_lecture and mod_to_lecture[dep] < lecture_idx:
                external[lecture_idx].add(dep)

    lines = ["flowchart LR"]

    # Prior-lecture stubs.
    by_prior: dict[int, list[str]] = defaultdict(list)
    for dep in external[lecture_idx]:
        by_prior[mod_to_lecture[dep]].append(dep)
    for pli in sorted(by_prior):
        stub = f"L{pli + 1}core"
        sample = ", ".join(sorted(by_prior[pli])[:5])
        if len(by_prior[pli]) > 5:
            sample += ", …"
        lines.append(
            f'  {stub}["Lect {ROMAN[pli]} imports<br/><i>{sample}</i>"]'
        )

    for node in display_nodes:
        if node in {"Thm88chain", "Ex812", "Ex825", "Lect8helpers"}:
            members = [m for m in mods if display_mod[m] == node]
            if node == "Thm88chain":
                title = "Theorem 8.8 pipeline"
            elif node == "Ex812":
                title = "Exercise 8.12 cluster"
            elif node == "Ex825":
                title = "Exercise 8.25 cluster"
            else:
                title = "Presentation helpers"
            lbl = f"{title}<br/><i>{len(members)} modules</i>"
        else:
            lbl = node_label(node, mod_labels, headers)
        lines.append(f'  {mermaid_id(node)}["{lbl}"]')

    for pli in sorted(by_prior):
        stub = f"L{pli + 1}core"
        emitted: set[tuple[str, str]] = set()
        for mod in mods:
            for dep in imports.get(mod, []):
                if dep in by_prior[pli]:
                    edge = (stub, mermaid_id(display_mod[mod]))
                    if edge in emitted:
                        continue
                    emitted.add(edge)
                    lines.append(f"  {stub} -.-> {mermaid_id(display_mod[mod])}")

    for a, b in sorted(edges):
        lines.append(f"  {mermaid_id(a)} --> {mermaid_id(b)}")

    # Lecture I: conceptual edges inside Basic.lean (proof-note order), since imports
    # cannot distinguish co-located definitions.
    if lecture_idx == 0 and "Basic" in display_nodes:
        b = mermaid_id("Basic")
        extras = [
            ("Basic_concept_D11", "Def 1.1"),
            ("Basic_concept_D16", "Def 1.6 · filters"),
            ("Basic_concept_D17", "Def 1.7 · principal"),
            ("Basic_concept_D19", "Def 1.9 · tokens"),
            ("Basic_concept_T11c", "Thm 1.1c"),
            ("Basic_concept_F14a", "Factoid 1.4a"),
        ]
        for nid, txt in extras:
            lines.append(f'  {nid}["{txt}<br/><i>in Basic.lean</i>"]')
        lines.extend(
            [
                f"  {b} --> Basic_concept_D11",
                "  Basic_concept_D11 --> Basic_concept_T11c",
                "  Basic_concept_D11 --> Basic_concept_F14a",
                "  Basic_concept_D11 --> Basic_concept_D16",
                "  Basic_concept_D16 --> Basic_concept_D17",
                "  Basic_concept_D17 --> Basic_concept_D19",
                "  Basic_concept_F14a -.-> Example12",
                "  Basic_concept_F14a -.-> Example13",
                "  Basic_concept_F14a -.-> Example14",
            ]
        )

    return "\n".join(lines)


def lecture_headers() -> list[str]:
    text = ARXIV.read_text(encoding="utf-8")
    return [m.group(1) for m in re.finditer(r"^### (Lecture [IVX]+:[^\n]+)\n", text, re.MULTILINE)]


CHAPTER_HIERARCHY_HEADER = "Chapter inclusion hierarchy (Lean imports)"


def build_chapter_hierarchy(
    order: list[str],
    splits: tuple[int, ...],
    imports: dict[str, list[str]],
    mod_to_lecture: dict[str, int],
) -> str:
    """One node per lecture; edge A→B if some B-module directly imports an A-module."""
    counts = [splits[i + 1] - splits[i] for i in range(8)]
    edge_weight: dict[tuple[int, int], int] = defaultdict(int)
    for dst_mod, imps in imports.items():
        if dst_mod not in mod_to_lecture:
            continue
        dli = mod_to_lecture[dst_mod]
        for src_mod in imps:
            if src_mod not in mod_to_lecture:
                continue
            sli = mod_to_lecture[src_mod]
            if sli < dli:
                edge_weight[(sli, dli)] += 1

    lines = [
        "flowchart TB",
        "  %% Node = lecture where modules are newly introduced;",
        "  %% edge A --> B = some B-module directly imports a module from A.",
    ]
    for i in range(8):
        lines.append(
            f'  L{i + 1}["Lecture {ROMAN[i]}<br/><i>{counts[i]} modules introduced</i>"]'
        )
    for (s, d), w in sorted(edge_weight.items()):
        lines.append(f"  L{s + 1} -->|{w} imports| L{d + 1}")
    return "\n".join(lines)


def patch_arxiv(diagrams: dict[str, str], chapter_diagram: str) -> None:
    text = ARXIV.read_text(encoding="utf-8")
    for header, diagram in diagrams.items():
        block = f"```mermaid\n{diagram}\n```"
        pattern = (
            rf"(^### {re.escape(header)}\n\n)"
            rf"(?:```mermaid\n.*?\n```\n\n)?"
        )
        repl = rf"\1{block}\n\n"
        new_text, n = re.subn(pattern, repl, text, count=1, flags=re.DOTALL | re.MULTILINE)
        if n == 0:
            raise RuntimeError(f"could not locate section header: {header!r}")
        text = new_text

    chapter_block = (
        f"### {CHAPTER_HIERARCHY_HEADER}\n\n"
        "Each node is a lecture (Scott chapter) at the point its Lean modules are "
        "first introduced. An edge $A \\to B$ means some module belonging to lecture "
        "$B$ has a direct `import` of a module belonging to lecture $A$ (transitive "
        "imports through intermediate lectures are *not* drawn). Edge labels count "
        "those direct import sites. This is the dependency picture relevant to "
        "splitting the monograph into separate arXiv papers.\n\n"
        f"```mermaid\n{chapter_diagram}\n```\n"
    )
    chapter_pattern = (
        rf"(^### {re.escape(CHAPTER_HIERARCHY_HEADER)}\n\n)"
        rf"(?:.*?\n)?"
        rf"(?:```mermaid\n.*?\n```\n)"
    )
    if re.search(rf"^### {re.escape(CHAPTER_HIERARCHY_HEADER)}\n", text, re.MULTILINE):
        new_text, n = re.subn(
            chapter_pattern,
            chapter_block + "\n",
            text,
            count=1,
            flags=re.DOTALL | re.MULTILINE,
        )
        if n == 0:
            raise RuntimeError("could not refresh chapter hierarchy block")
        text = new_text
    else:
        # Insert before the Methodology section (end of Introduction).
        marker = "\n---\n\n## Methodology\n"
        if marker not in text:
            raise RuntimeError("missing Methodology marker for chapter hierarchy insert")
        text = text.replace(marker, "\n\n" + chapter_block + "\n" + marker, 1)

    ARXIV.write_text(text)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true", help="patch arxiv.md in place")
    args = parser.parse_args()

    order = wired_order()
    splits = (*LECTURE_SPLITS, len(order))
    imports = parse_imports()
    headers = parse_module_headers()
    mod_labels = parse_arxiv_labels()
    mod_to_lecture = {}
    for li in range(8):
        for mod in order[splits[li] : splits[li + 1]]:
            mod_to_lecture[mod] = li

    headers_list = lecture_headers()
    if len(headers_list) != 8:
        raise SystemExit(f"expected 8 lecture headers, found {len(headers_list)}")

    diagrams: dict[str, str] = {}
    for i, header in enumerate(headers_list):
        cluster = i >= 7  # cluster only Lecture VIII
        diagrams[header] = build_lecture_diagram(
            i, order, splits, imports, mod_labels, headers, mod_to_lecture, cluster=cluster
        )
        print(f"{header}: {len(diagrams[header].splitlines())} lines")

    chapter_diagram = build_chapter_hierarchy(order, splits, imports, mod_to_lecture)
    print(f"{CHAPTER_HIERARCHY_HEADER}: {len(chapter_diagram.splitlines())} lines")

    if args.write:
        patch_arxiv(diagrams, chapter_diagram)
        print(f"patched {ARXIV}")
    else:
        print(f"\n=== {CHAPTER_HIERARCHY_HEADER} ===\n{chapter_diagram}\n")
        for header, diagram in diagrams.items():
            print(f"\n=== {header} ===\n{diagram}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

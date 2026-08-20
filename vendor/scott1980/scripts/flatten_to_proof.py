#!/usr/bin/env python3
"""Flatten every Scott1980 Lean module into a single proof.lean.

Internal `import Scott1980.*` lines are dropped (the bodies are concatenated in
dependency order). External/Mathlib imports are hoisted to the top of the file.
"""

from __future__ import annotations

from collections import defaultdict, deque
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "proof.lean"

COPYRIGHT = """\
/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980

This file is a generated concatenation of every Lean 4 module under
`Scott1980/`, in import-dependency order, with Mathlib imports hoisted and
internal `import Scott1980.*` lines removed. Regenerate with:

    python3 scripts/flatten_to_proof.py
-/
"""


def module_to_rel(mod: str) -> str:
    return mod.replace(".", "/") + ".lean"


def lean_files_from_root() -> list[str]:
    """Library modules in `Scott1980.lean` listing order (not dependency order)."""
    files: list[str] = []
    for line in (ROOT / "Scott1980.lean").read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line.startswith("import Scott1980."):
            continue
        files.append(module_to_rel(line.removeprefix("import ").strip()))
    return files


def split_header(text: str) -> tuple[list[str], str]:
    """Return (import modules, body after copyright + imports)."""
    lines = text.splitlines()
    i = 0
    if lines and lines[0].strip() == "/-":
        for j in range(1, len(lines)):
            if lines[j].strip() == "-/":
                i = j + 1
                break
    while i < len(lines) and lines[i].strip() == "":
        i += 1
    imports: list[str] = []
    while i < len(lines):
        s = lines[i].strip()
        if s.startswith("import "):
            imports.append(s.removeprefix("import ").strip())
            i += 1
        elif s == "":
            i += 1
        else:
            break
    body = "\n".join(lines[i:]).rstrip() + "\n"
    return imports, body


def topo_sort(files: list[str], deps: dict[str, set[str]]) -> list[str]:
    """Kahn sort; among ready nodes, keep the Scott1980.lean listing order."""
    index = {f: i for i, f in enumerate(files)}
    incoming: dict[str, set[str]] = {f: set(deps[f]) for f in files}
    outgoing: dict[str, set[str]] = defaultdict(set)
    for f, ds in incoming.items():
        for d in ds:
            outgoing[d].add(f)
    ready = deque(sorted((f for f in files if not incoming[f]), key=lambda f: index[f]))
    ordered: list[str] = []
    while ready:
        f = ready.popleft()
        ordered.append(f)
        for g in sorted(outgoing[f], key=lambda x: index[x]):
            incoming[g].discard(f)
            if not incoming[g]:
                ready.append(g)
        ready = deque(sorted(ready, key=lambda x: index[x]))
    leftover = [f for f in files if f not in ordered]
    if leftover:
        raise SystemExit(f"import cycle or missing dep among: {leftover}")
    return ordered


def main() -> None:
    files = lean_files_from_root()
    on_disk = {str(p.relative_to(ROOT)) for p in (ROOT / "Scott1980").rglob("*.lean")}
    missing = [f for f in files if f not in on_disk]
    extra = sorted(on_disk - set(files))
    if missing:
        raise SystemExit(f"listed but missing on disk: {missing}")
    if extra:
        raise SystemExit(f"on disk but not in Scott1980.lean: {extra}")

    mathlib: list[str] = []
    seen_mathlib: set[str] = set()
    bodies: dict[str, str] = {}
    deps: dict[str, set[str]] = {}

    for rel in files:
        imports, body = split_header((ROOT / rel).read_text(encoding="utf-8"))
        bodies[rel] = body
        internal: set[str] = set()
        for mod in imports:
            if mod.startswith("Scott1980."):
                dep = module_to_rel(mod)
                if dep not in on_disk:
                    raise SystemExit(f"{rel} imports missing module {mod}")
                internal.add(dep)
            else:
                if mod not in seen_mathlib:
                    seen_mathlib.add(mod)
                    mathlib.append(mod)
        deps[rel] = internal

    ordered = topo_sort(files, deps)

    chunks: list[str] = [COPYRIGHT, ""]
    for mod in mathlib:
        chunks.append(f"import {mod}\n")
    chunks.append("\n")
    chunks.append(
        "/-!\n"
        "# Scott 1981 (PRG-19) — complete Lean 4 formalization (flattened)\n"
        "\n"
        f"Concatenation of {len(ordered)} modules ({sum(len(bodies[f].splitlines()) for f in ordered)} "
        "source lines after stripping headers/imports).\n"
        "-/\n\n"
    )
    for rel in ordered:
        chunks.append(f"/- === {rel} === -/\n\n")
        chunks.append(bodies[rel])
        if not bodies[rel].endswith("\n"):
            chunks.append("\n")
        chunks.append("\n")

    OUT.write_text("".join(chunks), encoding="utf-8")
    nlines = sum(1 for _ in OUT.open(encoding="utf-8"))
    print(f"wrote {OUT} ({len(ordered)} modules, {nlines} lines, {len(mathlib)} imports)")


if __name__ == "__main__":
    main()

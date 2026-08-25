#!/usr/bin/env python3
"""Flatten ScottModels plus the vendor modules those bridges import."""

from __future__ import annotations

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
VENDOR = {
    "Scott1972": ROOT / "vendor/scott1972",
    "Scott1980": ROOT / "vendor/scott1980",
    "Scott1982": ROOT / "vendor/scott1982",
}
SM = ROOT / "ScottModels"
OUT = ROOT / "everything.lean"

IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.]+)\s*$")
COPYRIGHT_RE = re.compile(r"^/-\nCopyright.*?\n-/\n+", re.DOTALL)
PRIVATE_NAMED_RE = re.compile(
    r"^private\s+(?:noncomputable\s+)?"
    r"(?:theorem|def|lemma|instance|abbrev|structure|inductive|class)\s+"
    r"([A-Za-z0-9_']+)"
)
PRIVATE_ANON_INST_RE = re.compile(r"^([ \t]*)private instance :", re.MULTILINE)

ENTRIES = [
    "ScottModels.NeighborhoodToInfoSys",
    "ScottModels.InfoSysToNeighborhood",
    "ScottModels.ContinuousLatticeToNeighborhood",
    "ScottModels.InfoSysToIdealCompletion",
    "ScottModels.IdealCompletionToContinuousLattice",
    "ScottModels.PresentationDomains",
    "ScottModels.InfoSysConstructions",
    "ScottModels.ScottMapBridge",
    "ScottModels.SexDomainEquation",
    "ScottModels.WorkedExampleSExpr",
]


def lean_path(mod: str) -> Path | None:
    if mod.startswith("ScottModels."):
        return SM / (mod.split(".", 1)[1].replace(".", "/") + ".lean")
    for pkg, base in VENDOR.items():
        if mod == pkg:
            return base / f"{pkg}.lean"
        if mod.startswith(pkg + "."):
            return base / (mod.replace(".", "/") + ".lean")
    return None


def imports_of(path: Path) -> list[str]:
    out = []
    for line in path.read_text(encoding="utf-8").splitlines():
        m = IMPORT_RE.match(line.strip())
        if m:
            out.append(m.group(1))
    return out


def is_local(mod: str) -> bool:
    return mod.startswith(("Scott1972", "Scott1980", "Scott1982", "ScottModels"))


def walk() -> list[str]:
    seen: set[str] = set()
    order: list[str] = []

    def visit(mod: str) -> None:
        if mod in seen or not is_local(mod):
            return
        path = lean_path(mod)
        if path is None or not path.exists():
            raise SystemExit(f"missing module {mod} -> {path}")
        seen.add(mod)
        for imp in imports_of(path):
            visit(imp)
        order.append(mod)

    for e in ENTRIES:
        visit(e)
    return order


def module_slug(mod: str) -> str:
    return mod.rsplit(".", 1)[-1]


def uniquify_privates(text: str, slug: str) -> str:
    """Private names are per-module; flattening makes duplicates clash."""
    n = 0

    def name_anon(match: re.Match[str]) -> str:
        nonlocal n
        n += 1
        return f"{match.group(1)}private instance {slug}_privInst{n} :"

    text = PRIVATE_ANON_INST_RE.sub(name_anon, text)
    names = []
    for line in text.splitlines():
        m = PRIVATE_NAMED_RE.match(line.strip())
        if m:
            names.append(m.group(1))
    for name in sorted(set(names), key=len, reverse=True):
        text = re.sub(rf"\b{re.escape(name)}\b", f"{slug}_{name}", text)
    return text


def strip_body(text: str, mod: str) -> str:
    text = COPYRIGHT_RE.sub("", text, count=1)
    kept = []
    for line in text.splitlines():
        if IMPORT_RE.match(line.strip()):
            continue
        kept.append(line)
    while kept and not kept[0].strip():
        kept.pop(0)
    return uniquify_privates("\n".join(kept).rstrip() + "\n", module_slug(mod))


def section_title(mod: str) -> str:
    if mod.startswith("Scott1980"):
        return f"Vendor 1980 — {mod}"
    if mod.startswith("Scott1982"):
        return f"Vendor 1982 — {mod}"
    if mod.startswith("Scott1972"):
        return f"Vendor 1972 — {mod}"
    return f"Bridge — {mod}"


def main() -> None:
    order = walk()
    vendor = [m for m in order if not m.startswith("ScottModels")]
    bridges = [m for m in order if m.startswith("ScottModels")]
    mathlib = sorted({
        imp
        for m in order
        for imp in imports_of(lean_path(m))
        if not is_local(imp)
    })

    parts = [
        "/-\n"
        "Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.\n"
        "Released under Apache 2.0 license as described in the file LICENSE.\n"
        "Authors: Lars Warren Ericson.\n"
        "Github:  https://github.com/catskillsresearch/scott_models\n"
        "-/\n\n"
    ]
    for imp in mathlib:
        parts.append(f"import {imp}\n")
    parts.append(
        "\n"
        "/-!\n"
        "# Single-file ScottModels\n"
        "\n"
        "Self-contained flatten of the bridge theorems in `ScottModels/` together\n"
        "with the transitive vendor modules they import (`vendor/scott1972`,\n"
        "`vendor/scott1980`, `vendor/scott1982`). Mathlib stays imported.\n"
        "Regenerate with `python3 scripts/generate_everything.py`.\n"
        "-/\n\n"
        "set_option linter.unusedSectionVars false\n"
        "set_option linter.unusedSimpArgs false\n"
        "set_option linter.unusedVariables false\n\n"
    )

    parts.append("/-! ## Vendor dependencies -/\n\n")
    for mod in vendor:
        path = lean_path(mod)
        parts.append(f"-- {section_title(mod)} (from {path.relative_to(ROOT)})\n\n")
        parts.append(strip_body(path.read_text(encoding="utf-8"), mod))
        parts.append("\n")

    parts.append("/-! ## Bridge theorems -/\n\n")
    for mod in bridges:
        path = lean_path(mod)
        parts.append(f"-- {section_title(mod)} (from {path.relative_to(ROOT)})\n\n")
        parts.append(strip_body(path.read_text(encoding="utf-8"), mod))
        parts.append("\n")

    OUT.write_text("".join(parts), encoding="utf-8")
    lines = OUT.read_text(encoding="utf-8").count("\n")
    print(f"wrote {OUT.relative_to(ROOT)} ({lines} lines; "
          f"{len(vendor)} vendor modules, {len(bridges)} bridge modules)")


if __name__ == "__main__":
    main()

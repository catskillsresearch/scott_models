# LRSODInCIC (standalone)

Thought exercise: L/R/S/O/D axiom layers embedded in Lean 4's CIC — no Mathlib, no scott1972/1980/1982.

| File | Role |
|---|---|
| `LRSODInCIC.md` | Paper (axioms, CIC, translation) — the source of truth |
| `LRSODInCIC.lean` | Deep embedding, plus a Sierpiński-space witness for D1–D4 |
| `build_pdf.py` | `LRSODInCIC.md` → `LRSODInCIC.tex` → `LRSODInCIC.pdf`, with the Lean file inlined as an appendix |
| `LRSODInCIC.pdf` | Built paper, committed as the readable deliverable |

Check the Lean:

```bash
cd LRSODInCIC
lake build
```

Build the paper (needs `pandoc` and `latexmk`; reuses the glyph table in
`../scripts/tex_preamble_arxiv.tex`, so every non-ASCII character is a declared
LaTeX symbol rather than a font lookup):

```bash
python3 build_pdf.py
```

`LRSODInCIC.tex` is generated and git-ignored; `LRSODInCIC.pdf` is committed, matching how
`arxiv.tex` and `arxiv.pdf` are handled at the repo root. The appendix pulls in
`LRSODInCIC.lean` with `\lstinputlisting` at compile time, so the listing cannot drift
from the file `lake build` checks.

Open `LRSODInCIC.lean` in Cursor; the Lean server uses **this** package's `lakefile.toml`, not the parent `ScottModels` workspace.

# CARDB (standalone)

Thought exercise: the number of distinct topological bases of a finite set of
size \(N\) — Mathlib only, no scott1972/1980/1982.

| File | Role |
|---|---|
| `CARDB.md` | Paper (identity, fiber lemma, small-\(N\) table) — the source of truth |
| `CARDB.lean` | Sorry-free formalization of the sum identity |
| `build_pdf.py` | `CARDB.md` → `CARDB.tex` → `CARDB.pdf`, with the Lean file inlined as an appendix |
| `CARDB.pdf` | Built paper, committed as the readable deliverable |

Check the Lean:

```bash
cd CARDB
lake build
```

Build the paper (needs `pandoc` and `latexmk`; reuses the glyph table in
`../scripts/tex_preamble_arxiv.tex`):

```bash
python3 build_pdf.py
```

`CARDB.tex` is generated and git-ignored; `CARDB.pdf` is the committed
deliverable, matching `LRSODInCIC/` and the repo-root `arxiv.pdf`. The title
page lists the author, Catskills Research Company, and
<https://github.com/catskillsresearch/scott_models/tree/main/CARDB>.
The appendix pulls in `CARDB.lean` with `\lstinputlisting` at compile time.

Open `CARDB.lean` in Cursor; the Lean server uses **this** package's
`lakefile.toml`, not the parent `ScottModels` workspace.

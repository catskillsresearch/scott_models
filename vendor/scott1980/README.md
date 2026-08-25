[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/scott1980/build.yml?label=Lean%204)](https://github.com/catskillsresearch/scott1980/actions/workflows/build.yml)
# scott1980

Lean 4 formalization of Dana Scott's **1980 Oxford lectures**, published May
**1981** as PRG-19 *Lectures on a Mathematical Theory of Computation*
(neighborhood systems / filter domains). Author: Lars Warren Ericson.

Standalone package — no dependency on the 1972 formalization. Part IV equivalence
theorems live in [`scott_models`](../scott_models). This repo is packaged for
[Palomar](https://palomar-registry.org/about) on its own (see `PROVENANCE.md`).
The principal sourced Palomar result is the first sentence of Theorem 8.8
(`theorem_8_8 : D ⊴ U`). Comparator also selects two new formal corollaries:
Example 1.5's `P4_embeds` and Exercise 7.22's `Ssys_embeds`. Scott defines
those systems but does not separately state the embeddings. His other two
Theorem 8.8 sentences and the rest of the book are not Comparator targets.

Scott assumes from the outset that the master token set `Δ` is non-empty.
`NeighborhoodSystem.master_nonempty` records that assumption structurally.

Original Lean and author-written docs are Apache-2.0. Scott's monograph
`sources/PRG19.pdf` and its transcription `sources/PRG19.md` are **not**
under that license; see `NOTICE` and `sources/README.md`.

## Files (Palomar)

| File | Role |
|---|---|
| `arxiv.md` | Formalization narrative and theorem inventory |
| `sources/PRG19.md` | Transcribed source text (Scott PRG-19) |
| `Scott1980/` | Sorry-free formalization of the lectures |
| `Challenge.lean` | Palomar statements: the principal `D ⊴ U` theorem plus `P4_embeds` and `Ssys_embeds` |
| `Solution.lean` | Palomar solution module: imports `Scott1980/*` proofs |
| `comparator.json` | Comparator config for the three embedding results and their definitions |
| `formalization.yaml` | Palomar / formalization.yaml v0.4 metadata |
| `PROVENANCE.md` | Standalone Palomar submission; relation to siblings |
| `NOTICE` | Apache-2.0 carve-out for Scott's PRG-19 PDF and transcription |

## Build

```bash
lake exe cache get
lake build
```

`lake build` typechecks `Scott1980`, `Challenge.lean`, and `Solution.lean`. Before a
Palomar submission, run:

```bash
bash scripts/palomar_preflight.sh
```

Pinned: Lean / mathlib **v4.33.0** (`lean-toolchain`).

### LLM / single-file export

To ship the entire library as one Lean file (for tools without local repo access):

```bash
python3 scripts/flatten_to_proof.py   # writes proof.lean (gitignored)
```

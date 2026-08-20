# Provenance

[`catskillsresearch/domain_theory`](https://github.com/catskillsresearch/domain_theory)
(public, Apache-2.0) preceded this work. It was archived as the
per-paper split progressed, because each paper’s Lean outgrew a single
tree:

| Remote | Presentation |
| --- | --- |
| [`scott1972`](https://github.com/catskillsresearch/scott1972) | Continuous lattices |
| [`scott1980`](https://github.com/catskillsresearch/scott1980) | Neighbourhood systems (PRG-19) |
| [`scott1982`](https://github.com/catskillsresearch/scott1982) | Information systems |
| [`scott_models`](https://github.com/catskillsresearch/scott_models) | The bridges (this repo) |

This Palomar snapshot copies the three paper repos into `vendor/` so a
preservation fork of `scott_models` contains the complete development.
The three remotes remain the per-paper homes. Frozen SHAs and copy date
are in `vendor/FROZEN.txt`. This is a convenience archive of the author’s
own split, not a republication of someone else’s formalization. The
archived `domain_theory` tree is historical and is not vendored; the
split remotes are the sources of truth.

[`Lean Pool` `DomainTheory`](https://github.com/Vilin97/lean-pool/tree/main/LeanPool/DomainTheory)
is a public downstream ingest of `domain_theory` (their
`candidates/provenance.jsonl` records `repo: catskillsresearch/domain_theory`,
authors Catskills Research Company). Apache-2.0 permitted that copy. It
holds an earlier ContinuousLattice + Neighborhood + short InfoSys slice
and does not have full `scott1982` or these bridges. This SHA is the
complete source to copy.

Brian Milnes’s
[`ScottLean4/Ericson`](https://github.com/briangmilnes/ScottLean4/tree/main/Ericson)
documents the four remotes and clones them with a script; the Lean is
git-ignored there. That is a known local reference checkout, not a
published second formalization.

[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/scott_models/build.yml?label=Lean%204)](https://github.com/catskillsresearch/scott_models/actions/workflows/build.yml)
# scott_models

Equivalence theorems relating the 1972 continuous-lattice, 1980 neighborhood-system,
and 1982 information-system presentations of Scott domain theory.

The **Palomar statement of record** is the small family of presentation-bridge
isos (`neighborhoodSystem_to_infoSys`, `infoSys_to_neighborhoodSystem` /
`InfoSysToNeighborhood.domainOrderIso`, `presentation_domains_equiv` :
`D ≃o RoundInfoSysElement`), not a dump of the three source papers. The
sibling repositories remain the per-paper developments:

- [`scott1972`](https://github.com/catskillsresearch/scott1972) — continuous lattices
- [`scott1980`](https://github.com/catskillsresearch/scott1980) — neighbourhood systems (PRG-19)
- [`scott1982`](https://github.com/catskillsresearch/scott1982) — information systems

Lake pins those repos at explicit git SHAs in `lakefile.toml`. The paper of
record for the bridges is `view.pdf` (source `arxiv.md`).

## Build

```bash
lake exe cache get
lake build
```

`lake build` typechecks `ScottModels`, `Challenge`, and `Solution`.
`Challenge.lean` imports only Mathlib and leaves the compared declarations
as `sorry`. `Solution.lean` re-exports the sorry-free `ScottModels/` proofs.

Narrative inventory: `arxiv.md`. Palomar metadata: `comparator.json`,
`formalization.yaml`. Session resume: `HANDOFF.md`.

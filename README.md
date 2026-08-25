[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/scott_models/build.yml?label=Lean%204)](https://github.com/catskillsresearch/scott_models/actions/workflows/build.yml)
[![Palomar](https://img.shields.io/badge/Palomar-2026--08--25--000003-0f766e.svg)](https://palomar-registry.org/entry?id=PALOMAR-2026-08-25-000003&version=1)

# scott_models

Equivalence theorems relating the 1972 continuous-lattice, 1980 neighborhood-system,
and 1982 information-system presentations of Scott domain theory.

The **Palomar statement of record** is the family of presentation-bridge
isos (`neighborhoodSystem_to_infoSys`, `infoSys_to_neighborhoodSystem` /
`InfoSysToNeighborhood.domainOrderIso`, `presentation_domains_equiv` :
`D ≃o RoundInfoSysElement`) together with the S-expression instance
`T ≅ A + (T × T)` as `|T| ≃o |A + (T × T)|` (`sexNeighborhoodIso`,
`sexIdealIso`, `sexDomainEquationIso`), not a dump of the three source
papers.

[`domain_theory`](https://github.com/catskillsresearch/domain_theory)
preceded this work and was archived as the per-paper split progressed
into [`scott1972`](https://github.com/catskillsresearch/scott1972),
[`scott1980`](https://github.com/catskillsresearch/scott1980),
[`scott1982`](https://github.com/catskillsresearch/scott1982), and this
bridges package. This snapshot copies those three paper trees into
`vendor/` (frozen SHAs and local patches in `vendor/FROZEN.txt`) so one
Palomar SHA has the complete development; the remotes remain the
per-paper homes. See `PROVENANCE.md`. The paper of record for the bridges is `view.pdf`
(source `arxiv.md`).

## Build

```bash
lake exe cache get
lake build
```

`lake build` typechecks `ScottModels`, `Challenge`, and `Solution`.
`Challenge.lean` imports only Mathlib and leaves the compared declarations
as `sorry`. `Solution.lean` re-exports the sorry-free `ScottModels/` proofs.

Narrative inventory: `arxiv.md`. Palomar metadata: `comparator.json`,
`formalization.yaml`. Split / vendor story: `PROVENANCE.md`.
Session resume: `HANDOFF.md`.

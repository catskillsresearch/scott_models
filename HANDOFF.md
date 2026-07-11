# Handoff — scott_models (Part IV: equivalence of the three presentations)

Bridge theorems relating Scott's **1972** continuous-lattice, **1980** neighbourhood-system,
and **1982** information-system presentations. Lean library: `ScottModels`. Inventory: `arxiv.md`.

Sibling packages (Lake path deps; treat as **finished** sources of truth — do not trust stale
status prose elsewhere):

| Package | Path | Role |
| --- | --- | --- |
| `scott1972` | `../scott1972` | Continuous lattices (`IsContinuousLattice`, Thm 2.12, …) |
| `scott1980` | `../scott1980` | Neighbourhood systems + approximable maps (PRG-19) |
| `scott1982` | `../scott1982` | Information systems through Factoid 8.4 / domain equations |

Source MD transcriptions live in each sibling's `sources/` directory. Per-paper proof structure
lives in each sibling's `arxiv.md`.

## Resume Protocol (read this first)

1. Read this `HANDOFF.md`.
2. Read `arxiv.md` in **this** repo (short blueprint: planned bridge theorems + status).
3. For dependency lemmas, **Grep** the relevant sibling `arxiv.md` / Lean module — do not rely on
   copied status dumps in this repo.
4. Build: `lake build ScottModels` (filter: `| grep -vE 'LEAN_PATH|trace:' | tail`).
5. Follow `.cursor/rules/handoff-discipline.mdc`.

## Current status (2026-07-11)

- `neighborhoodSystem_to_infoSys` **Pass** (`NeighborhoodToInfoSys.lean`).
- `infoSys_to_neighborhoodSystem` **Pass** (`InfoSysToNeighborhood.lean`).
- `continuousLattice_to_neighborhoodSystem` **Pass** (`ContinuousLatticeToNeighborhood.lean`):
  `↟a` neighbourhoods + `domainEmbedding : D ↪o |𝒟|` with retract `ofFilter_toFilter`.
  Full `|𝒟| ≃o D` deferred (round-ideal / HARD). Axioms ⊆ `{propext, Quot.sound}`.
- `infoSys_to_idealCompletion` **Pass** (`InfoSysToIdealCompletion.lean`):
  `|A| ≃o Order.Ideal (FiniteElement A)` via Factoids 4.4–4.5.
- `idealCompletion_to_continuousLattice` **Pass** (`IdealCompletionToContinuousLattice.lean`):
  algebraic complete lattice ⇒ `IsContinuousLattice` (classical `≪`).
- `presentation_domains_equiv` **Partial** (`PresentationDomains.lean`): 1980↔1982↔ideal
  triangle; CL corner still embedding-only.
- Remaining: close CL↔Nbhd to full iso; `infoSys_constructions_equiv`.

## On finishing a bridge theorem

1. `lake build ScottModels` green, zero `sorry`; axiom audit ⊆ `{propext, Quot.sound}` unless
   classical frontier (call out choice in the proof note).
2. Append a dated checkpoint below; update Resume / status lines above.
3. Update the theorem's row in this repo's `arxiv.md`.
4. Wire new modules into `ScottModels.lean`.

---

## Checkpoints

### 2026-07-11 — status hygiene

- Deleted stale PRG-19 `HANDOFF.md` dump (copied from `domain_theory` / `scott1980`).
- Removed unrelated `NEXT.md` and obsolete `system_prompt.md` (`domain_theory` InfoSys prompt).
- Retargeted `.cursor/rules/handoff-discipline.mdc` to this Part IV package.
- Confirmed `../scott1982` Lean root imports Def 2.1 through Factoid 8.4 / `DomainEquation`
  (zero `sorry` in `Scott1982/`); treat the 1982 package as complete for Part IV work.

### 2026-07-11 — `neighborhoodSystem_to_infoSys`

- New `ScottModels/NeighborhoodToInfoSys.lean`: `NbhdBasis ι α` packages a neighbourhood
  system with a decidable exhaustive coding of `𝒟`; `toInfoSys` takes neighbourhood codes as
  tokens, `Con` = `interOf u ∈ 𝒟`, `Ent` = intersection ⊆ target; `domainOrderIso` identifies
  filters with InfoSys elements.
- Constructive: `#print axioms` ⊆ `{propext, Quot.sound}` (avoided `by_cases` / classical `em`
  in `ent_con`).
- Wired through `ScottModels.lean`; `arxiv.md` row marked Pass.

### 2026-07-11 — `infoSys_to_neighborhoodSystem`

- New `ScottModels/InfoSysToNeighborhood.lean`: Scott §4 basic opens `[u]` as a
  `NeighborhoodSystem` on `|A|`; `toFilter` / `ofFilter` give `domainOrderIso`.
- Constructive: `#print axioms` ⊆ `{propext, Quot.sound}` (removed `simp` on
  `basicOpen_empty` / `funion` which pulled `Classical.choice`).
- Completes the constructive **1980 ↔ 1982** presentation bridge (with
  `neighborhoodSystem_to_infoSys`).

### 2026-07-11 — `continuousLattice_to_neighborhoodSystem`

- New `ScottModels/ContinuousLatticeToNeighborhood.lean`: `wayBelowUp a = {z | a ≪ z}`
  as `NeighborhoodSystem` on token set `D`; principal filters `toFilter`; under
  `IsContinuousLattice`, retract `ofFilter` (`sSup` of codes in the filter) and
  `domainEmbedding : D ↪o |𝒟|`.
- Does **not** claim full `|𝒟| ≃o D` (needs roundness / `a ≪ ⊔approx`).
- `#print axioms` on named decls ⊆ `{propext, Quot.sound}`.
- Wired through `ScottModels.lean` / `Equivalence.lean`; `arxiv.md` Pass.

### 2026-07-11 — `infoSys_to_idealCompletion`

- New `ScottModels/InfoSysToIdealCompletion.lean`: `FiniteElement A` = closures of
  consistent finsets; `toIdeal` / `ofIdeal` give `domainOrderIso : |A| ≃o Ideal (FiniteElement A)`.
- Uses 1982 Factoids 4.4–4.5 (`directedSup`, `eq_directedSup_finiteApproximants`,
  `compact_closure`).
- `#print axioms` ⊆ `{propext, Quot.sound}`.
- Wired through `ScottModels.lean` / `Equivalence.lean`; `arxiv.md` Pass.

### 2026-07-11 — `idealCompletion_to_continuousLattice`

- New `ScottModels/IdealCompletionToContinuousLattice.lean`: `IsCompactElement`,
  `IsAlgebraicLattice`, proof `IsAlgebraicLattice ⇒ IsContinuousLattice` (compacts are
  way-below via Scott-open `Ici`).
- Classical frontier: depends on 1972 topological `≪` / `ScottOpen`.
- Wired through `ScottModels.lean` / `Equivalence.lean`; `arxiv.md` Pass.

### 2026-07-11 — `presentation_domains_equiv` (partial)

- New `ScottModels/PresentationDomains.lean`: `neighborhood_ideal_iso`,
  `nbhdBasis_ideal_iso` composing 1980↔1982↔ideal completion.
- Full three-presentation equiv blocked on `|𝒟| ≃o D` for the 1972 corner.
- Wired into `ScottModels.lean`.

# Handoff — scott_models (equivalence of the three presentations)

Bridge theorems relating Scott's **1972** continuous-lattice, **1980** neighbourhood-system,
and **1982** information-system presentations. Lean library: `ScottModels`. Inventory: `arxiv.md`.

Sibling packages (in-tree `vendor/` copies of the author’s remotes; treat as
**finished** sources of truth — do not trust stale status prose elsewhere):

| Package | Path | Role |
| --- | --- | --- |
| `scott1972` | `vendor/scott1972` | Continuous lattices (`IsContinuousLattice`, Thm 2.12, …) |
| `scott1980` | `vendor/scott1980` | Neighbourhood systems + approximable maps (PRG-19) |
| `scott1982` | `vendor/scott1982` | Information systems through Factoid 8.4 / domain equations |

Source MD transcriptions live in each sibling's `sources/` directory. Per-paper proof structure
lives in each sibling's `arxiv.md`.

## Resume Protocol (read this first)

1. Read this `HANDOFF.md`.
2. Read `arxiv.md` in **this** repo (this article: bridges, proof notes, constructivity).
3. For dependency lemmas, **Grep** the relevant sibling `arxiv.md` / Lean module — do not rely on
   copied status dumps in this repo.
4. Build: `lake build ScottModels` (filter: `| grep -vE 'LEAN_PATH|trace:' | tail`).
   Standalone Mizar translation: `lake build Yellow17` (root `Yellow17.lean`, not imported by ScottModels).
5. Palomar type check (green `lake build` is not enough): from repo root,
   `bash scripts/compare_challenge_solution_types.sh`.
   It `#check`s every `comparator.json` name from Challenge and from Solution
   with `pp.all` / `pp.explicit` and diffs. A non-empty diff means Palomar
   Comparator will fail (instance-name / instance-path mismatch), as on cardb.
   Every compared `inst*` declaration must be an **explicitly named** instance
   in `Challenge.lean` (Verso will not render an anchor for `instance : T`).
6. Follow `.cursor/rules/handoff-discipline.mdc`.

## Current status (2026-08-25)

- `neighborhoodSystem_to_infoSys` **Pass** (`NeighborhoodToInfoSys.lean`).
- `infoSys_to_neighborhoodSystem` **Pass** (`InfoSysToNeighborhood.lean`).
- `continuousLattice_to_neighborhoodSystem` **Pass** (`ContinuousLatticeToNeighborhood.lean`):
  `↟a` neighbourhoods; **`D ≃o RoundFilter`** via `domainOrderIso` (roundness required —
  arbitrary filters properly contain principal ones). Axioms ⊆ `{propext, Quot.sound}`.
- `infoSys_to_idealCompletion` **Pass** (`InfoSysToIdealCompletion.lean`).
- `idealCompletion_to_continuousLattice` **Pass** (`IdealCompletionToContinuousLattice.lean`).
- `presentation_domains_equiv` **Pass** (`PresentationDomains.lean`):
  `D ≃o RoundFilter ≃o RoundInfoSysElement` (+ ideal subtype form); InfoSys triangle
  remains constructive. Raw `|𝒟|` / full `|A|` properly larger.
- `infoSys_constructions_equiv` **Pass** (`InfoSysConstructions.lean` +
  `ScottMapBridge.lean`): 1982 product/sum/function-space domain isos;
  `ApproximableMap ≃o ScottContinuous` (Factoid 4.6); `ScottMap` conjugates along
  round-filter / round-InfoSys presentation.
- Blueprint rows all Pass. Out of scope (documented): identifying
  `ApproximableMap` on `wayBelowNbhdBasis` with `ScottMap` via roundness.
- Palomar compared family also includes the Factoid 8.1 instance
  `sexNeighborhoodIso`, `sexIdealIso`, `sexDomainEquationIso`.
- Palomar automated review on `f0d6af25a06008457d399562ef6e26c11616ac51`
  (2026-08-25): no problems identified. Registered as
  [PALOMAR-2026-08-25-000003](https://palomar-registry.org/entry?id=PALOMAR-2026-08-25-000003&version=1)
  v1.
- Standalone `Yellow17` (Mizar `YELLOW_17` Tychonoff translation) is green;
  not part of the ScottModels bridge article.

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
- Retargeted `.cursor/rules/handoff-discipline.mdc` to this package.
- Confirmed `../scott1982` Lean root imports Def 2.1 through Factoid 8.4 / `DomainEquation`
  (zero `sorry` in `Scott1982/`); treat the 1982 package as complete for this article’s work.

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

### 2026-07-11 — round filters close CL → Nbhd iso

- Upgraded `ContinuousLatticeToNeighborhood.lean`: `IsRound`, `RoundFilter`,
  `domainOrderIso : D ≃o RoundFilter`. Documented why raw `|𝒟|` is too big
  (`{↟a | a ≤ x}` vs `{↟a | a ≪ x}`).
- `toFilter_ofFilter` for round filters; interpolation ⇒ principal filters are round.
- `presentation_domains_equiv` still Partial (glue round corner to 1980/1982 domains).
- Axioms ⊆ `{propext, Quot.sound}`.

### 2026-07-11 — constructions: product domain iso

- New `ScottModels/InfoSysConstructions.lean`: `productDomainIso` /
  `infoSys_product_domain_equiv : |A| × |B| ≃o |A×B|` from 1982 `pairElements` /
  `fstMap`/`sndMap` (under `InfoSys.ApproximableMap` namespace).
- Axioms ⊆ `{propext, Quot.sound}`. Sum / function space still open.
- Wired into `ScottModels.lean`; `arxiv.md` constructions → Partial.

### 2026-07-11 — constructions: separated-sum domain iso

- Extended `InfoSysConstructions.lean`: `sumDomainIso` /
  `infoSys_sum_domain_equiv : WithBot (|A| ⊕ |B|) ≃o |A+B|` via `inl`/`inr`
  classify/assemble; trichotomy classical (`Classical.choice` in footprint).
- Product remains choice-free. Function space still open.

### 2026-07-11 — constructions: function-space domain iso

- Extended `InfoSysConstructions.lean`: `functionSpaceDomainIso` /
  `infoSys_function_space_domain_equiv : ApproximableMap A B ≃o |A→B|` packaging
  Thm 7.2 `approxMap_toElement` / `element_toApproxMap` with `Le` as `PartialOrder`.
- Axioms ⊆ `{propext, Quot.sound}`. 1982 construction triangle complete at domain level.

### 2026-07-11 — `presentation_domains_equiv` (round glue)

- Extended `PresentationDomains.lean`: `wayBelowNbhdBasis` codes the `↟`-system;
  `roundFilter_infoSys_iso : RoundFilter ≃o RoundInfoSysElement`;
  `presentation_domains_equiv : D ≃o RoundInfoSysElement` and ideal subtype form.
- Constructive: `#print axioms` ⊆ `{propext, Quot.sound}`.
- `arxiv.md` / `Equivalence.lean` → Pass.

### 2026-07-11 — `infoSys_constructions_equiv` (ScottMap bridge)

- New `ScottModels/ScottMapBridge.lean`:
  `approximableMap_scottContinuous_equiv` (Factoid 4.6 OrderIso);
  `scottMap_roundFilter_iso` / `scottMap_roundInfoSys_iso` conjugating
  `ScottMap` along the round presentation; `infoSys_constructions_equiv` packaging.
- Separated sum remains classical; Factoid 4.6 ⊆ `{propext, Quot.sound}`;
  ScottMap conjugation inherits `Classical.choice` from 1972 Scott topology.
- All blueprint rows Pass.

### 2026-07-11 — `arxiv.md` as this article’s paper

- Rewrote `arxiv.md` from terse status table into a paper narrative: abstract,
  introduction, catalog, per-bridge proof notes (§3.1–3.7), constructivity table,
  scope of “equivalence”, reproducibility, references.
- Resume Protocol now treats `arxiv.md` as the durable proof document (not a stub blueprint).

### 2026-07-11 — arXiv TeX / dist package

- Ported scott1982 pipeline: `scripts/build_arxiv_tex.{sh,py}`, `build_arxiv_pdf.sh`,
  `package_arxiv_submit.sh`, `ai_model_cards.py`, `tex_preamble_arxiv.tex`, `.latexmkrc`.
- `arxiv.md`: Lean Code appendix (GitHub links), AI reference markers, build commands.
- Built `arxiv.tex` (9-page PDF), `dist/arxiv_submit.zip` (figures + listings + 00README.json).
- Generated artifacts gitignored (`arxiv.tex`, `figures/`, `lean-listings/`, `dist/`).

### 2026-07-11 — worked example: S-expressions

- New `ScottModels/WorkedExampleSExpr.lean`: `treeSystem` over Factoid 2.4 atoms;
  neighbourhood / ideal isos; `sexDomainEquationIso`; `idMap` via Factoid 4.6.
- `arxiv.md` §5 filled; wired into `ScottModels.lean`.

### 2026-07-11 — §5 year tags; paper wording

- `arxiv.md` §5: split out **§5.4 Continuous lattices (1972)**; renumber domain equation / morphisms to 5.5–5.6.
- Replaced monograph-part labels with “this article” / “this package” in `arxiv.md`, README, Lean module docs, AI model cards.

### 2026-07-11 — §5 overview + equivalence narrative

- Rewrote §5: Overview (goal = same S-expr domain in 1972/1980/1982); per-paradigm
  presentations; dedicated §5.5 instance equivalences with transitivity; §5.6 extras.

### 2026-08-19 — Palomar packaging (bridges, not the three papers)

- Added root `Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`.
- Compared family: `neighborhoodSystem_to_infoSys`, `infoSys_to_neighborhoodSystem`,
  `InfoSysToNeighborhood.domainOrderIso`, `presentation_domains_equiv`
  (`D ≃o RoundInfoSysElement`). Supporting holes only as Comparator needs them.
- `lakefile.toml`: sibling requires were git+SHA, then retargeted to
  in-tree `vendor/` path deps (same frozen SHAs).
  Pins: scott1972 `36bf01f99f00fcb78b999052212372ba026521ba`,
  scott1980 `f6cbc2d62a636ab24e60d185f80c0f61daf73fe1`,
  scott1982 `7ed95c16db5be1131f79af84cdf29ba18f07646a`.
- Paper of record for Palomar metadata: `view.pdf`. `arxiv.md` is the math source.
- Did not register; did not re-prove; did not vendor the siblings; not LRSOD.

### 2026-08-19 — Palomar `pp.all` type diff

- Recipe: `bash scripts/compare_challenge_solution_types.sh` (also Resume Protocol §5).
- Named instances `instPartialOrderElement` already matched. The script caught a
  **different** instance-path bug: `presentation_domains_equiv`'s `D ≃o _`
  elaborated `CompleteSemilatticeInf.toPartialOrder` in Challenge vs the longer
  `ConditionallyCompleteLattice` chain in Solution. Fixed by importing
  `Mathlib.Order.ConditionallyCompleteLattice.Basic` in `Challenge.lean`.
- Re-run the script before submitting; a non-empty diff fails Palomar even if
  `lake build` is green.

### 2026-08-24 — re-vendor sibling paper repos

- Copied latest `../scott1972|1980|1982` into `vendor/` (no `.git` / `.lake`);
  updated `vendor/FROZEN.txt` at frozen SHAs (2026-08-24).
- `scott1980`: `NeighborhoodSystem` now requires `master_nonempty`; bridge
  `toNeighborhoodSystem` in `InfoSysToNeighborhood` and
  `ContinuousLatticeToNeighborhood` updated.
- `scott1982`: upstream `Factoid81` at the frozen SHA is Scott-faithful only;
  restored the bridge patch (`TreeEntPayload` kernel disjuncts,
  `TreeCon_insert_bot`) in `vendor/scott1982/Scott1982/Factoid81.lean` for
  `SexDomainEquation.lean` (noted in `FROZEN.txt`).
- `scott1972`: universe annotations on `IsContinuousLattice` / `WayBelow` /
  `ScottOpen`; `Challenge.lean` + compare-script normalize aligned.
- `lake build ScottModels Challenge Solution` green; compare script OK.

---

- Copied `../scott1972|1980|1982` into `vendor/` at the frozen HEADs (no `.git` /
  `.lake`). `lakefile.toml` path deps are in-tree. `PROVENANCE.md` + YAML +
  README record the domain_theory split, the remotes, and the Lean Pool
  downstream ingest. Brian’s Ericson/ clone is a PROVENANCE sentence only.

### 2026-08-19 — Palomar: S-expression instance (Factoid 8.1)

- Compared family now also includes `sexNeighborhoodIso`, `sexIdealIso`,
  and `sexDomainEquationIso` (`WithBot (|A| ⊕ (|T| × |T|)) ≃o |A + (T × T)|`).
- Challenge restates `TreeToken` / `SumToken` / `IsProdToken` / `ProdToken`
  and holes `treeSystem`, `treeRhs`, `lowerBoundSystem`, `FiniteElement`.
- `Solution.lean` imports `ScottModels.WorkedExampleSExpr`.
- `sexDomainEquationIso` axioms include `Classical.choice` (1982 sum
  trichotomy). Carrier isos remain `{propext, Quot.sound}`.

### 2026-08-19 — Palomar browser-check: theorems + original-proof sources

- `theorem_names` now lists `exists_presentation_domains_equiv` and the
  three `exists_sex*` theorems (`Nonempty` of each compared `OrderIso`).
- With an `original-proof` source, other `sources[]` relationships are
  `background` (Scott 1972 / PRG-19 / ICALP / folklore), not `adapts` /
  `independently-proves`.

### 2026-08-19 — Palomar registry card

- Shortened `formalization.yaml` `project.description` to the public
  blurb (bridges + round corner + S-expression equation). Vendor / AI /
  sorry detail stays in limitations and automation.

### 2026-08-20 — Palomar landrun: no path-dep writes under vendor/

- Comparator `safeLakeBuild` landrun is `--rwx` only on the project
  `.lake/` (plus `/dev`). Path requires tried to write
  `vendor/scott19xx/.lake` → four `permission denied (error code: 13)`.
- `lakefile.toml` now compiles `vendor/` as this package's `lean_lib`s
  (`srcDir`). Manifest no longer lists the three path packages.
- Confirmed `lake build Challenge Solution` with vendor dirs `a-w`.

### 2026-08-20 — Palomar: universe names on `exists_presentation_domains_equiv`

- Comparator compares `ConstantVal` including `levelParams`. Challenge
  had `.{u_1}`, Solution `.{u_4}` because PresentationDomains still had
  `{α, ι, β : Type*}` in scope. Both sides now use `universe u` /
  `{D : Type u}` for the continuous-lattice section.

### 2026-08-20 — Palomar: `instDecidableEqTreeToken`

- Comparator walked the generated `deriving DecidableEq` instance and
  required identical `ConstantInfo` (universe names + body). Replaced
  deriving with a handwritten `instDecidableEqTreeToken` on `{α : Type u}`
  in Challenge and `vendor/scott1982`. Listed that instance (and the
  sum/product ones) in `definition_names`.

### 2026-08-20 — Palomar: `IsContinuousLattice` definition hole

- Comparator walked `IsContinuousLattice` (used in
  `exists_presentation_domains_equiv`) and compared the full constant,
  including the elaborated body. Challenge imports
  ConditionallyCompleteLattice so `IsLUB` / `≪` instance paths differ
  from `vendor/scott1972`. Types already match; listed
  `IsContinuousLattice`, `WayBelow`, and `ScottOpen` as definition
  holes.

### 2026-08-20 — Palomar review: `|T| ≃o |A + (T × T)|`

- Editorial request: the compared `sexDomainEquationIso` was only the
  generic `WithBot (|A| ⊕ (|T| × |T|)) ≃o SexRhs.Element`, not the
  S-expression fixed-point equation.
- `TreeEnt` now matches official product `ent_bot` on the two encodings
  of `(Δ,Δ)` (`pairL bot` / `pairR bot`), so closed tree elements are
  saturated for `ker(treeUnfold)`.
- Compared declaration is now
  `sexDomainEquationIso : SexSys.Element ≃o SexRhs.Element`
  (`treeDomainIso` via image/preimage of `treeUnfold`). Unfolding
  lemmas: `sexDomainEquationIso_unfold` / `_fold`. The old semantic
  factor is the uncompared `sexRhsSemanticIso`.
- Axioms of the compared iso: `{propext, Quot.sound}` (no sum
  trichotomy).
- `arxiv.md` §5 / catalog / module map now state the compared iso as
  `SexSys.Element ≃o SexRhs.Element`; `SexDomainEquation.lean` is wired
  into `ScottModels.lean` and the Lean Code appendix. Rebuild
  `arxiv.pdf` / `view.pdf` with `bash scripts/build_arxiv_pdf.sh`.

### 2026-08-20 — Palomar metadata: drop `original-proof`

- Review: mechanical verification passed; provenance conflicted because
  `original-proof` sat next to an account that the equivalence was
  already known.
- `formalization.yaml`: removed `original-proof`. `view.pdf` is `notes`
  / `other` (write-up of this formalization). Folklore three-presentation
  equivalence is `independently-proves`. Scott 1972 / PRG-19 / ICALP
  stay `background`.
- First-Lean-treatment language is only in `limitations` as a search
  note, not a provenance claim. `arxiv.md` §1 says the same.

### 2026-08-24 — Lean 4.33 standalone-vendor and bridge compatibility

- Verified each vendored package independently with its own Lake project:
  `vendor/scott1972` (962 jobs), `vendor/scott1980` (3275 jobs), and
  `vendor/scott1982` (1118 jobs) all build green under Lean 4.33.0.
- Refreshed the stale `vendor/scott1982/lake-manifest.json` from Mathlib
  v4.33.0. Compatibility patches replace brittle reduction/simp proofs in
  `Proposition23`, `Theorem72`, `Factoid82`, `Fixpoint`, and `Factoid77`;
  the last uses explicit transports between Mathlib's categorical tensor
  object and Scott's concrete product system.
- Adapted bridges only after the standalone builds: explicit master-set
  transport in `InfoSysToNeighborhood`, robust classify/assemble proofs in
  `InfoSysConstructions`, explicit basis-element typing in
  `PresentationDomains`, and an explicit `if_neg` proof in
  `SexDomainEquation`.
- `lake build ScottModels Challenge Solution` is green; no `sorry` occurs
  under `ScottModels/`; the Palomar comparator reports matching types.
- Axiom audit note: Mathlib 4.33's `Finset.instSetLike` and
  `Finset.instPartialOrder` depend on `Classical.choice`, so every
  InfoSys-facing declaration now inherits
  `{propext, Classical.choice, Quot.sound}` at the kernel level. The
  product/function/presentation compatibility proofs do not themselves
  select witnesses; `arxiv.md` §4 distinguishes this inherited instance
  frontier from genuine classical classification.

### 2026-08-24 — strip vendored Palomar kits

- Removed `comparator.json`, Challenge/Solution, formalization.yaml,
  and Palomar preflight scripts from `vendor/scott1972|1980|1982` so
  Palomar sees one Comparator config (root). Sibling kits stay on remotes.
- Lakefiles default to the paper libs only; vendored CI runs `lake build`.

### 2026-08-25 — Comparator closure universe mismatch

- Palomar rejected definition hole `Scott1982.InfoSys.closure`: Challenge used
  level parameter `u`, while the independently elaborated target uses `u_1`.
- Isolated the Challenge closure hole in a `universe u_1` section, matching the
  target `DefinitionVal` type, level parameters, and safety.
- Removed universe-name normalization from the local comparison script:
  Comparator compares level parameter names exactly. Full preflight is green
  with exact Challenge/Solution output.

### 2026-08-25 — Challenge `NeighborhoodSystem` missing `master_nonempty`

- Palomar rejected `Scott1980.Neighborhood.NeighborhoodSystem.mk`: Challenge
  still had the pre-re-vendor 5-field constructor, while the 1980 target now
  requires `master_nonempty`.
- Challenge structure now matches `vendor/scott1980` field order.
- Local compare script also `#print`s walked structure constructors.

### 2026-08-25 — explicit names for compared instances

- Palomar Verso needs compiler-backed anchors on every comparator.json
  declaration. Named the previously anonymous Challenge instances
  `instPartialOrderElement` (1980 and 1982), `instDecidableEqSumToken`,
  and `instDecidableEqProdToken`. The same names are now explicit in the
  vendored 1980/1982 sources. `comparator.json` names are unchanged.

### 2026-08-25 — Palomar provenance: vendor revisions

- `formalization.yaml` still listed the 2026-08-19 pins (`36bf01f…`,
  `f6cbc2d…`, `7ed95c1…`). Related-formalization IDs now match
  `vendor/FROZEN.txt`: scott1972 `278ba174…`, scott1980 `ef6c0567…`,
  scott1982 `d3221eec…`.
- Each sibling note now records the in-tree modifications (Palomar-kit
  strip on all three; named 1980 instance; 1982 Factoid 8.1 bridge
  patch, Lean 4.33 compatibility, and named Comparator instances).
- Preflight checks that those `/tree/<rev>` URLs match `FROZEN.txt`.

### 2026-08-25 — Palomar automated review passed

- Submission SHA `f0d6af25a06008457d399562ef6e26c11616ac51`: reviewer
  reported no problems. Named-instance anchors and vendor-revision
  provenance were the last requested fixes; both are on this commit.
- No repository change is required for that review. Next action is
  registration if the author wants a public Palomar entry.

### 2026-08-25 — `arxiv.md` finished-product pass

- Abstract / §3 / §5 axiom claims now match Mathlib 4.33 audits: only
  `D ≃o RoundFilter` is `{propext, Quot.sound}`; InfoSys-facing isos
  inherit `Classical.choice` through `Finset`.
- Intro no longer treats the Lean gap as open. Catalog marks compared vs
  library rows. Build pin is Lean / mathlib v4.33.0 with frozen vendor
  SHAs. Palomar Verso-anchor packaging chatter removed from the paper.

### 2026-08-25 — rebuild `arxiv.pdf` / `view.pdf`

- Regenerated the TeX appendix and compiled `arxiv.pdf` (57 pages, all
  fonts embedded). `view.pdf` is a copy of that file.

### 2026-08-25 — `everything.lean`

- Single-file flatten of the ten `ScottModels/` bridge modules plus the
  31 vendor modules in their import closure. Headline bridges sit at
  the end. Regenerate with `python3 scripts/generate_everything.py`.
  `lake build everything` is green (not a default Lake target).

### 2026-08-25 — Palomar registry citation

- `arxiv.md` §2 and References record registration
  `PALOMAR-2026-08-25-000003` v1 and the compared claim Palomar verified.

### 2026-08-25 — rebuild PDFs after Palomar citation

- Regenerated `arxiv.pdf` / `view.pdf` (57 pages, all fonts embedded).

### 2026-08-25 — `Yellow17` (Mizar `YELLOW_17`)

Standalone root translation of Bartłomiej Skorulski, *The Tichonov Theorem*
(`yellow17.miz`). Not wired into `ScottModels` / `arxiv.md`.

- File: `Yellow17.lean`. Lake target: `[[lean_lib]] name = "Yellow17"` (not a
  default target).
- Representation: dependent products `∀ i, X i`, `Function.eval`,
  `Function.update`, cylinders `eval i ⁻¹' U` (not Mizar set-coded
  `product` / `proj` / `+*`).
- `Th1`–`Th13`: typed projection / cylinder / update lemmas.
- `Th14`–`Th15`: `isCompact_iff_finite_subcover`, `isCompact_generateFrom`.
- `Th16`–`Th18`: `cylinderSubbasis` generates `Pi.topologicalSpace`.
- `Th19`–`Th22`: cylinder-subbasis finite-subcover combinatorics.
- Headlines: `yellow17_tychonoff_sets` (`isCompact_univ_pi`),
  `yellow17_tychonoff` / `yellow17_tychonoff'` (`Pi.compactSpace`).
- `lake build Yellow17` green, zero `sorry`.
- Axiom audit of the three headlines:
  `{propext, Classical.choice, Quot.sound}` (classical compactness /
  Tychonoff; choice is expected).

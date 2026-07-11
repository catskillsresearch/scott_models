# Equivalence of Scott's Three Presentations of Domain Theory

---

## Abstract

Dana Scott developed three presentations of the same class of domains: **continuous
lattices** (1972), **neighbourhood systems** (PRG-19 / 1980–81), and **information
systems** (1982). Each sibling formalization — [`scott1972`](https://github.com/catskillsresearch/scott1972),
[`scott1980`](https://github.com/catskillsresearch/scott1980),
[`scott1982`](https://github.com/catskillsresearch/scott1982) — treats one presentation
in isolation. This package (`ScottModels`) supplies the **bridge theorems**: order
isomorphisms and constructivity audits showing that the three presentations determine
the same domains (up to isomorphism), including products, separated sums, and function
spaces at the information-system level, with a transport of 1972 Scott maps along the
round presentation.

The Lean development is sorry-free. The **1980 ↔ 1982** bridges and the round continuous
lattice corner target `#print axioms ⊆ {propext, Quot.sound}`. Classical choice appears
where Scott's 1972 topology is unavoidable (algebraic ⇒ continuous; ScottMap conjugation)
and in the trichotomy for separated sums.

---

## 1. Introduction

Scott notes in the 1982 ICALP paper that neighbourhood systems and information systems
are equivalent “in a precise sense.” The mathematical folklore is stronger still: all
three presentations carve out the same class of domains, related by ideal completion
and the Scott topology. Until the bridges are checked in a proof assistant, that claim
lives in the gap between three separately formalized libraries.

This article closes that gap. We do **not** re-prove Scott's internal theorems; we import
the finished sibling packages and build cross-presentation maps:

| Presentation | Lean package | Characteristic object |
| --- | --- | --- |
| Continuous lattices **[Sco72]** | `scott1972` | `IsContinuousLattice D`, way-below `≪`, `ScottMap` |
| Neighbourhood systems **[Sco81]** | `scott1980` | `NeighborhoodSystem`, filters as domain elements |
| Information systems **[Sco82]** | `scott1982` | `InfoSys`, elements as consistent closed token sets |

The main subtlety is that a naïve reading of “domains = filters of neighbourhoods”
overstates the continuous-lattice corner: for a continuous lattice `D`, the filter
`{↟a | a ≤ x}` has retract `x` but properly contains the principal round filter
`{↟a | a ≪ x}`. The correct identification is **`D ≃o RoundFilter`**, not raw `|𝒟|`.

```mermaid
flowchart LR
  CL["1972<br/>IsContinuousLattice"]
  NB["1980<br/>NeighborhoodSystem"]
  INF["1982<br/>InfoSys"]
  ALG["Ideal completion<br/>algebraic dcpo"]

  CL -->|"round ↟-filters"| NB
  NB -->|"NbhdBasis coding"| INF
  INF -->|"basic opens [u]"| NB
  INF --> ALG
  ALG -->|"compacts ⇒ ≪"| CL
  CL -->|"presentation_domains_equiv"| INF
```

---

## 2. Catalog of bridge theorems

| Theorem | Direction | Lean module |
| --- | --- | --- |
| `continuousLattice_to_neighborhoodSystem` | 1972 → 1980 | `ContinuousLatticeToNeighborhood.lean` |
| `neighborhoodSystem_to_infoSys` | 1980 → 1982 | `NeighborhoodToInfoSys.lean` |
| `infoSys_to_neighborhoodSystem` | 1982 → 1980 | `InfoSysToNeighborhood.lean` |
| `infoSys_to_idealCompletion` | 1982 → algebraic | `InfoSysToIdealCompletion.lean` |
| `idealCompletion_to_continuousLattice` | algebraic → 1972 | `IdealCompletionToContinuousLattice.lean` |
| `presentation_domains_equiv` | three-way | `PresentationDomains.lean` |
| `infoSys_constructions_equiv` | constructions | `InfoSysConstructions.lean`, `ScottMapBridge.lean` |

The sibling packages are **finished dependencies**, not work items of this paper:
[`scott1972`](https://github.com/catskillsresearch/scott1972),
[`scott1980`](https://github.com/catskillsresearch/scott1980), and
[`scott1982`](https://github.com/catskillsresearch/scott1982) (information systems through
Factoid 8.4 / domain equations). This package only builds the bridges above.

<!-- mermaid-caption: Lean module map -->
```mermaid
flowchart TD
  CLN["ContinuousLatticeToNeighborhood"]
  N2I["NeighborhoodToInfoSys"]
  I2N["InfoSysToNeighborhood"]
  I2Id["InfoSysToIdealCompletion"]
  Id2CL["IdealCompletionToContinuousLattice"]
  PD["PresentationDomains"]
  IC["InfoSysConstructions"]
  SMB["ScottMapBridge"]
  Eq["Equivalence"]

  CLN --> PD
  N2I --> PD
  I2N --> PD
  I2Id --> PD
  Id2CL --> PD
  IC --> SMB
  PD --> SMB
  CLN --> Eq
  N2I --> Eq
  I2N --> Eq
  I2Id --> Eq
  Id2CL --> Eq
  PD --> Eq
  IC --> Eq
  SMB --> Eq
```

---

## 3. Proof notes

### 3.1 Continuous lattices → neighbourhood systems

**Claim.** For a continuous lattice `D`, the sets `↟a = {z | a ≪ z}` form a
`NeighborhoodSystem` on token type `D`, and under `IsContinuousLattice` one has an order
isomorphism `D ≃o RoundFilter`.

**Construction.** `wayBelowUp a` is upward closed; `↟⊥ = univ`;
`↟a ∩ ↟b = ↟(a ⊔ b)` (interpolation / directedness of way-below). Principal filters
`toFilter x = {↟a | a ≪ x}` are round: membership of `↟a` yields, by interpolation in a
continuous lattice, some `b` with `a ≪ b ≪ x`, hence `↟b ∈ toFilter x`.

**Why raw `|𝒟|` fails.** The larger filter `{↟a | a ≤ x}` still has `ofFilter = x`
(supremum of codes), but is not equal to `toFilter x` whenever there are elements
way-below strictly below `x`. Roundness (`↟a ∈ f ⇒ ∃ b, a ≪ b ∧ ↟b ∈ f`) cuts exactly
to the image of `toFilter`.

**Axioms.** `domainOrderIso : D ≃o RoundFilter` audits to `{propext, Quot.sound}`.

### 3.2 Neighbourhood systems → information systems

**Claim.** A neighbourhood system equipped with a decidable exhaustive coding
`NbhdBasis ι α` of its neighbourhood family `𝒟` induces an `InfoSys` on tokens `ι`
with `|𝒟| ≃o` the InfoSys domain.

**Construction.** Tokens are neighbourhood indices. Consistency of a finite `u ⊆ ι` is
membership of `⋂_{i∈u} nbhd i` in `𝒟` (empty intersection = master set `Δ`). Entailment
`u ⊢ j` means the intersection is a neighbourhood contained in `nbhd j`. Filters of the
neighbourhood system correspond to InfoSys elements via the coding.

**Constructivity.** `DecidableEq ι` is required so `InfoSys` can use the choice-free
`Finset` prelude from `scott1982`. The proof of `ent_con` avoids classical `by_cases` /
`em`. Axioms ⊆ `{propext, Quot.sound}`.

### 3.3 Information systems → neighbourhood systems

**Claim.** For an information system `A`, the basic opens `[u] = {x ∈ |A| | ↑u ⊆ x}`
(`u ∈ Con`) form a `NeighborhoodSystem` on `|A|`, and filters recover elements:
`|A| ≃o` the filter domain.

**Proof note.** Scott’s Factoid 4.6 supplies the basic-open vocabulary. The Lean proof
initially pulled `Classical.choice` through `simp` on `basicOpen_empty` / finset unions;
those simps were removed so the footprint stays `{propext, Quot.sound}`. Together with
§3.2 this is the constructive **1980 ↔ 1982** equivalence under coding.

### 3.4 Information systems → ideal completion

**Claim.** `|A| ≃o Ideal (FiniteElement A)`, where finite elements are closures `ū` of
consistent finsets (`Factoid 3.5`).

**Construction.** `toIdeal x` is the ideal of finite approximants of `x`; `ofIdeal`
takes directed suprema of finite elements (1982 Factoids 4.4–4.5:
`directedSup`, `eq_directedSup_finiteApproximants`, `compact_closure`). Axioms ⊆
`{propext, Quot.sound}`.

### 3.5 Algebraic complete lattices → continuous lattices

**Claim.** If every element of a complete lattice is the directed supremum of compact
elements below it (`IsAlgebraicLattice`), then `IsContinuousLattice` holds.

**Proof note.** Order-theoretic compactness implies `Set.Ici k` is Scott-open, hence
`k ≪ y` whenever `k ≤ y`. Algebraicity then yields `y = ⊔{k compact | k ≤ y} ⊆ ⊔{x | x ≪ y}`.
This is the **classical frontier**: Scott’s `≪` is defined topologically in `scott1972`,
so the footprint inherits that classicality even though the order argument is elementary.

### 3.6 Three-presentation equivalence (`presentation_domains_equiv`)

**Claim.** Under `IsContinuousLattice D` and `DecidableEq D`,
```
D ≃o RoundFilter ≃o RoundInfoSysElement
```
where `RoundInfoSysElement` is the subtype of elements of the InfoSys coded by
`wayBelowNbhdBasis` (tokens = elements of `D`, neighbourhoods = `↟a`) that correspond
to round filters. An extended form routes through the ideal-completion subtype.

**Glue.** `wayBelowNbhdBasis` packages the `↟`-system as an `NbhdBasis`;
`roundFilter_infoSys_iso` transports roundness along `NbhdBasis.domainOrderIso`;
`presentation_domains_equiv` is the composite with `continuousLattice_roundFilter_iso`.

**What is not claimed.** Raw `|𝒟|` and the full InfoSys domain `|A|` remain properly
larger than `D`. The equivalence is on the **round** corner that matches continuous
lattice points.

**Axioms.** ⊆ `{propext, Quot.sound}`.

### 3.7 Constructions (`infoSys_constructions_equiv`)

#### Products

`|A| × |B| ≃o |A × B|` via 1982 `pairElements` / `fstMap` / `sndMap` (Prop 6.2).
Choice-free; axioms ⊆ `{propext, Quot.sound}`.

#### Separated sums

`WithBot (|A| ⊕ |B|) ≃o |A + B|` via `inl` / `inr` classify-and-assemble (Prop 6.4).
Trichotomy on token polarity uses classical case-split (`Classical.choice` in the
footprint).

#### Function spaces

`ApproximableMap A B ≃o |A → B|` packages Theorem 7.2
(`approxMap_toElement` / `element_toApproxMap`) with pointwise `Le` as `PartialOrder`.
Axioms ⊆ `{propext, Quot.sound}`.

#### Factoid 4.6 bridge

`ApproximableMap A B ≃o ScottContinuous A B` via `toScottContinuous` /
`ofScottContinuous`, using Prop 5.3(v) (`rel_iff_closure_le`) and
`closure_le_element` for the round-trip on relations. Constructive:
`{propext, Quot.sound}`.

#### ScottMap conjugation

A 1972 `ScottMap D E` conjugates along any pair of order isomorphisms
`ιD : D ≃o D'`, `ιE : E ≃o E'` to a pointwise-ordered map `D' → E'`. Specializing to
`continuousLattice_roundFilter_iso` / `presentation_domains_equiv` yields
`scottMap_roundFilter_iso` and `scottMap_roundInfoSys_iso`. The conjugation itself is
order-theoretic; the footprint includes `Classical.choice` because `ScottMap` is defined
via Scott continuity in `scott1972`.

**Out of scope (documented).** Identifying `ApproximableMap` on the coded `↟`-InfoSys
with `ScottMap D E` (needs roundness preservation of approximable maps), and relating
`wayBelow(D × E)` to the InfoSys product of factors (cylinder basis).

---

## 4. Constructivity summary

| Bridge | Footprint | Notes |
| --- | --- | --- |
| Nbhd ↔ InfoSys (both directions) | `{propext, Quot.sound}` | Decidable coding; avoid classical `simp` traps |
| CL ↔ RoundFilter | `{propext, Quot.sound}` | Roundness is order-theoretic |
| InfoSys ↔ Ideal | `{propext, Quot.sound}` | Factoids 4.4–4.5 |
| Algebraic ⇒ CL | classical | 1972 topological `≪` |
| Product / function space (1982) | `{propext, Quot.sound}` | |
| Separated sum (1982) | + `Classical.choice` | Token polarity trichotomy |
| Factoid 4.6 ApproxMap ↔ ScottContinuous | `{propext, Quot.sound}` | |
| ScottMap conjugation | + `Classical.choice` | Via 1972 `ScottMap` |

Target discipline (from the 1982 package): prefer constructive proofs wherever Scott’s
1982 text emphasizes constructivity; call out classical frontiers explicitly rather than
hiding choice in automation.

---

## 5. What “equivalence” means here

We prove **order isomorphisms of domains** (and of the named construction objects), not
a 2-categorical equivalence of the full categories of continuous lattices /
neighbourhood systems / information systems with all morphisms. Morphisms are linked
where the sibling packages already supply them:

- approximable maps ↔ Scott-continuous maps on `|A|` (Factoid 4.6);
- Scott maps of continuous lattices ↔ their conjugates on the round presentation.

A full functorial equivalence (preserving products, exponentials, and inverse limits
simultaneously across all three presentations) would require additional coherence
theorems beyond this Part IV catalog.

---

## 6. Reproducibility

```bash
lake exe cache get
lake build ScottModels
```

Sibling packages `scott1972`, `scott1980`, `scott1982` are Lake path dependencies
(`lakefile.toml`). Session state and resume protocol live in `HANDOFF.md`; this file is
the durable inventory and proof narrative.

Axiom audits: `#print axioms` on the blueprint-facing names
(`presentation_domains_equiv`, `infoSys_product_domain_equiv`,
`approximableMap_scottContinuous_equiv`, `scottMap_roundInfoSys_iso`, …).

Acknowledgments (Dana Scott, AI tool cards, artifact URL) are injected before References
when building `arxiv.tex` via `scripts/ai_model_cards.py` — they are not kept in this file.

Build the arXiv PDF / submission zip (GitHub-link Lean Code appendix, modelled on scott1982):

```bash
bash scripts/build_arxiv_tex.sh      # arxiv.md → arxiv.tex + figures/
bash scripts/build_arxiv_pdf.sh      # compile PDF + package dist/arxiv_submit.zip
# or: bash scripts/package_arxiv_submit.sh
```

---

## References

- **[Sco72]** Dana Scott. *Continuous Lattices*. In F. W. Lawvere (ed.), *Toposes, Algebraic
  Geometry and Logic*, LNM 274, Springer, 1972.
- **[Sco81]** Dana Scott. *Lectures on a Mathematical Theory of Computation*. Technical
  Monograph PRG-19, Oxford University Computing Laboratory, 1981 (neighbourhood systems).
- **[Sco82]** Dana Scott. *Domains for Denotational Semantics*. ICALP 1982, LNCS 140,
  Springer, 1982.
- **[AJ94]** S. Abramsky and A. Jung. *Domain Theory*. In *Handbook of Logic in Computer
  Science*, Vol. 3, Oxford University Press, 1994.
- **[GHKLMS03]** G. Gierz et al. *Continuous Lattices and Domains*. Cambridge University
  Press, 2003.
- **[SR72]** Companion Lean formalization: [`scott1972`](https://github.com/catskillsresearch/scott1972).
- **[ER80]** Companion Lean formalization: [`scott1980`](https://github.com/catskillsresearch/scott1980).
- **[SR82]** Companion Lean formalization: [`scott1982`](https://github.com/catskillsresearch/scott1982).
- **[COPE24]** Committee on Publication Ethics (COPE). *Authorship and AI tools: COPE position statement*. 2024. <https://publicationethics.org/guidance/cope-position/authorship-and-ai-tools>
<!-- AI_MODEL_REFERENCES -->
<!-- /AI_MODEL_REFERENCES -->

---

## Lean Code

All Lean 4 modules in the [scott_models](https://github.com/catskillsresearch/scott_models)
repository are listed below as GitHub links (sources stay on GitHub; nothing is inlined
in the arXiv PDF). Order matches
[`ScottModels.lean`](https://github.com/catskillsresearch/scott_models/blob/main/ScottModels.lean).

### Root

* [ScottModels.lean](https://github.com/catskillsresearch/scott_models/blob/main/ScottModels.lean)

### Library (import order)

* [NeighborhoodToInfoSys.lean](https://github.com/catskillsresearch/scott_models/blob/main/ScottModels/NeighborhoodToInfoSys.lean)
* [InfoSysToNeighborhood.lean](https://github.com/catskillsresearch/scott_models/blob/main/ScottModels/InfoSysToNeighborhood.lean)
* [ContinuousLatticeToNeighborhood.lean](https://github.com/catskillsresearch/scott_models/blob/main/ScottModels/ContinuousLatticeToNeighborhood.lean)
* [InfoSysToIdealCompletion.lean](https://github.com/catskillsresearch/scott_models/blob/main/ScottModels/InfoSysToIdealCompletion.lean)
* [IdealCompletionToContinuousLattice.lean](https://github.com/catskillsresearch/scott_models/blob/main/ScottModels/IdealCompletionToContinuousLattice.lean)
* [PresentationDomains.lean](https://github.com/catskillsresearch/scott_models/blob/main/ScottModels/PresentationDomains.lean)
* [InfoSysConstructions.lean](https://github.com/catskillsresearch/scott_models/blob/main/ScottModels/InfoSysConstructions.lean)
* [ScottMapBridge.lean](https://github.com/catskillsresearch/scott_models/blob/main/ScottModels/ScottMapBridge.lean)
* [Equivalence.lean](https://github.com/catskillsresearch/scott_models/blob/main/ScottModels/Equivalence.lean)

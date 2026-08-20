/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Theorem85
import Scott1980.Neighborhood.FunctionSpace
import Scott1980.Neighborhood.Exercise213
import Scott1980.Neighborhood.Proposition611

/-!
# Lecture VIII — Theorem 8.6 (Scott 1981, PRG-19): the `sub` combinator

**Theorem 8.6.** For any domain `E` define `sub : (E → E) → (E → E)` by the formula

`X sub(f) Z` iff `∃Y ∈ E. X ⊆ Y, f Y ⊆ Z`,

for all `X, Z ∈ E` and all `f : E → E`. Then the range of `sub` consists exactly of the finitary
projections on `E`, and moreover `sub` itself is a finitary projection on `(E → E)`. If `E` is
effectively given, then `sub` is computable.

## What is formalized here

Scott's formula for `sub(f)` is *literally* Proposition 8.2's `retractionOfSubsystem`, applied to
Theorem 8.5's subdomain `D = fixedNbhd f = {Y ∈ E ∣ Y f Y}` (which, recall, is a genuine subsystem
`D ◁ E` for *any* `f`, no hypotheses needed). This module formalizes the per-token map
`sub : ApproximableMap E E → ApproximableMap E E` and its order-theoretic content at that level,
**Theorem 8.6's clause 1 in full**:

* **`sub f ≤ f`** (`sub_le`) — Scott's "`X ⊆ Y, f Y ⊆ Z` always implies `X f Z`", a bare
  monotonicity calculation, valid for *any* `f`.
* **`sub` is idempotent, exactly: `sub (sub f) = sub f`** (`sub_sub`) — sharper than Scott's stated
  inclusion `sub(f) ⊆ sub(sub(f))`: unwinding `fixedNbhd (sub f)` shows it has *the same*
  neighbourhoods as `fixedNbhd f` (`Y ⊆ Y' ⊆ Y` forces `Y = Y'`), so `sub (sub f)` and `sub f` are
  built from literally the same subsystem and hence are equal, not just related by `≤`.
* **`sub` is monotone** (`sub_mono`) — immediate from `fixedNbhd`'s definition.
* **`range(sub) = finitary projections`, both directions** (`sub_eq_self_iff_isFinitaryProjection`):
  the easy half `sub f = f → IsFinitaryProjection f` (`isFinitaryProjection_of_sub_eq_self`) is
  immediate substitution into `Subsystem.isFinitaryProjection_retractionOfSubsystem`; the converse
  `IsFinitaryProjection f → sub f = f` (`sub_eq_self_of_isFinitaryProjection`) is now unblocked by
  Theorem 8.5's hard direction (`formula_of_isFinitaryProjection`): `sub_le` gives `⊇` for free, and
  `⊆` unwinds `X f Z` via `rel_iff_mem_principal` into `Z ∈ f(↑X)`, then rewrites via Theorem 8.5's
  formula into exactly `sub_rel`'s defining shape.
* **`sub f` is *always* a finitary projection**, for any `f` (`isFinitaryProjection_sub`) —
  `sub (sub f) = sub f` plus the above.

**Theorem 8.6's clause 2, in full (in `namespace Sub8_6`):** `sub` packaged as a genuine
`ApproximableMap (funSpace E E) (funSpace E E)` (`subApprox`), realizing Scott's remark that
"the correspondence `f ↦ sub(f)` preserves directed unions of `f`'s, thus `sub` is itself
approximable", and shown to be a **finitary projection** on `(E → E)`
(`isFinitaryProjection_subApprox`):
`subApprox` is built via Exercise 2.13's `ofContinuous`, using a new general domain-theory bridge
`continuous_of_monotone_iSupDirected` (`Exercise213.lean`: monotone + directed-sup-preserving ⟹
topologically continuous, proved directly from algebraicity) applied to `subFilter`, `sub`
transported along `funSpaceEquiv`. `subFilter`'s directed-sup-preservation
(`subFilter_iSupDirected`) needs no consistency argument at all: directed unions of *filters*
correspond, under `toApproxMap`, to the raw union of the underlying maps' *relations*
(`toApproxMap_rel_iSupDirected`, immediate from `mem_iSupDirected`), and `sub`'s formula is a
*positive* existential in `f`'s relation, hence commutes with such unions by pure logic
(`sub_toApproxMap_iSupDirected`). `IsRetraction subApprox`/`subApprox ≤ idMap` then drop out of
`sub_sub`/`sub_le` respectively (`isProjection_subApprox`).

**`IsFinitary subApprox`** (`isFinitary_subApprox`) turned out *not* to need the universal-domain
machinery after all: `finitaryProjectionSubsystemEquiv` upgrades Theorem 8.6(a)'s bijection
`f ↦ fixedNbhd f` / `D ↦ retractionOfSubsystem D` between `{f ∣ sub f = f}` and the subsystems
`{D ∣ D ◁ E}` into a genuine **order-isomorphism** (round trips `fixedNbhd_retractionOfSubsystem`
and `sub`'s own defining equation; order via `retractionOfSubsystem_rel`'s witness clause plus
`Subsystem.subsystem_iff_subset_of_common`). Composed with `Fix(subApprox) ≃o {f ∣ sub f = f}`
(`subApproxFixIso`, via `toApproxMap`/`toFilter`) and **Lecture VI's Proposition 6.11**
(`subsystemReprIso`: the subsystems of `E` already form a genuine domain), this gives the witness
for `IsFinitary subApprox` directly, with no new "domain of subsystems" construction needed.

**Not formalized (deferred):**

* **Clause 3 (computability)** — needs `E` effectively given (Def 7.1 machinery); a separate,
  not-yet-formalized prerequisite.

Everything proved here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`), *except*
`isFinitary_subApprox`/`isFinitaryProjection_subApprox`, which pick up `Classical.choice` solely
through Proposition 6.11's `subsystemReprIso` (itself inheriting it from Exercise 2.22's `reprIso`,
the documented "for set theorists" exercise) — the same, already-accepted, provenance as every
other domain-representation result in this project (Ex 3.25/3.27, Prop 6.11 itself).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

/-- **Theorem 8.6's combinator `sub(f)` (Scott 1981, PRG-19), per token `f`.** Scott's formula
`X sub(f) Z ↔ ∃Y ∈ E, X⊆Y ∧ f.rel Y Y ∧ Y⊆Z` is literally `retractionOfSubsystem` applied to
`fixedNbhd f = {Y ∈ E ∣ Y f Y}` (Theorem 8.5's subsystem, built for *any* `f`). -/
def sub (f : ApproximableMap E E) : ApproximableMap E E :=
  Subsystem.retractionOfSubsystem (fixedNbhd_subsystem f)

@[simp] theorem sub_rel {f : ApproximableMap E E} {X Z : Set α} :
    (sub f).rel X Z ↔ E.mem X ∧ E.mem Z ∧ ∃ Y, (E.mem Y ∧ f.rel Y Y) ∧ X ⊆ Y ∧ Y ⊆ Z :=
  Subsystem.retractionOfSubsystem_rel (fixedNbhd_subsystem f)

/-- `fixedNbhd (sub f) = fixedNbhd f`: `Y (sub f) Y ↔ Y f Y`, since a witness `Y ⊆ Y' ⊆ Y` forces
`Y' = Y`. This is the key computation behind `sub`'s idempotency (`sub_sub`). -/
theorem fixedNbhd_sub (f : ApproximableMap E E) : fixedNbhd (sub f) = fixedNbhd f := by
  apply NeighborhoodSystem.ext
  · intro Y
    constructor
    · intro hmem
      have hr : (sub f).rel Y Y := hmem.2
      obtain ⟨hYE, -, Y', hY', hYY', hY'Y⟩ := sub_rel.mp hr
      obtain ⟨hY'E, hY'f⟩ := hY'
      have hYY'eq : Y' = Y := Set.Subset.antisymm hY'Y hYY'
      exact ⟨hYE, hYY'eq ▸ hY'f⟩
    · intro hmem
      obtain ⟨hYE, hYf⟩ := hmem
      refine ⟨hYE, sub_rel.mpr ⟨hYE, hYE, Y, ⟨hYE, hYf⟩, subset_rfl, subset_rfl⟩⟩
  · rfl

/-- **`sub f ≤ f`, unconditionally (Scott 1981, PRG-19).** "`X ⊆ Y, f Y ⊆ Z` always implies
`X f Z`" — a bare narrow-input/widen-output monotonicity calculation, needing nothing about `f`. -/
theorem sub_le (f : ApproximableMap E E) : sub f ≤ f := by
  rintro X Z hr
  obtain ⟨hX, hZ, Y, ⟨hYE, hYf⟩, hXY, hYZ⟩ := sub_rel.mp hr
  have h1 : f.rel X Y := f.mono hYf hXY subset_rfl hX hYE
  exact f.mono h1 subset_rfl hYZ hX hZ

/-- **`sub` is monotone.** `f ≤ g → sub f ≤ sub g`: immediate from `fixedNbhd`'s definition, since
`f.rel Y Y → g.rel Y Y` whenever `f ≤ g`. -/
theorem sub_mono {f g : ApproximableMap E E} (h : f ≤ g) : sub f ≤ sub g := by
  rintro X Z hr
  obtain ⟨hX, hZ, Y, ⟨hYE, hYf⟩, hXY, hYZ⟩ := sub_rel.mp hr
  exact sub_rel.mpr ⟨hX, hZ, Y, ⟨hYE, h Y Y hYf⟩, hXY, hYZ⟩

/-- **`sub` is idempotent: `sub (sub f) = sub f`** (sharper than Scott's stated `sub(f) ⊆
sub(sub(f))`, Theorem 8.6's projection clause for `sub` itself). Both sides are
`retractionOfSubsystem` of the *same* subsystem `fixedNbhd f` (`fixedNbhd_sub`), so they coincide
as maps, not merely as an inclusion. -/
theorem sub_sub (f : ApproximableMap E E) : sub (sub f) = sub f := by
  unfold sub
  congr 1
  exact fixedNbhd_sub f

/-- **The easy half of Theorem 8.6's range characterization.** If `f` is a fixed point of `sub`,
then `f` is a finitary projection: `sub f = f` says exactly that `f` *is*
`retractionOfSubsystem (fixedNbhd_subsystem f)`, and Definition 8.3's corollary of Proposition 8.2
finishes immediately. (The converse — every finitary projection is a fixed point of `sub` — is
Theorem 8.5's harder direction; see the module docstring.) -/
theorem isFinitaryProjection_of_sub_eq_self {f : ApproximableMap E E} (h : sub f = f) :
    IsFinitaryProjection f := by
  rw [← h]
  exact Subsystem.isFinitaryProjection_retractionOfSubsystem (fixedNbhd_subsystem f)

/-- **The hard half of Theorem 8.6's range characterization, now unblocked by Theorem 8.5.** Every
finitary projection is a fixed point of `sub`: `⊇` is `sub_le`; `⊆` unwinds `X f Z` via
`rel_iff_mem_principal` into `Z ∈ f(↑X)`, and Theorem 8.5's formula
(`formula_of_isFinitaryProjection`) rewrites this as exactly `sub_rel`'s defining formula. -/
theorem sub_eq_self_of_isFinitaryProjection {f : ApproximableMap E E}
    (h : IsFinitaryProjection f) : sub f = f := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · exact sub_le f X Z
  · intro hXZ
    have hX : E.mem X := f.rel_dom hXZ
    have hZ : E.mem Z := f.rel_cod hXZ
    have hmem : (f.toElementMap (E.principal hX)).mem Z := (f.rel_iff_mem_principal hX).mp hXZ
    obtain ⟨-, W, hW, hWZ, hWf⟩ := (formula_of_isFinitaryProjection h (E.principal hX)).mp hmem
    obtain ⟨hWE, hXW⟩ := (E.mem_principal hX).mp hW
    exact sub_rel.mpr ⟨hX, hZ, W, ⟨hWE, hWf⟩, hXW, hWZ⟩

/-- **Theorem 8.6's range characterization, in full.** `sub f = f ↔ f` is a finitary projection. -/
theorem sub_eq_self_iff_isFinitaryProjection {f : ApproximableMap E E} :
    sub f = f ↔ IsFinitaryProjection f :=
  ⟨isFinitaryProjection_of_sub_eq_self, sub_eq_self_of_isFinitaryProjection⟩

/-- **`sub` is itself a finitary projection on `E → E`'s range** (Theorem 8.6's remark that `sub`
restricted to its own range is the identity, i.e. `sub` "is" a projection onto the finitary
projections): applying `sub` twice is the same as once (`sub_sub`), and every `sub f` is already a
fixed point of `sub` (feed `isFinitaryProjection_of_sub_eq_self (sub_sub f)` back through
`sub_eq_self_iff_isFinitaryProjection`) — i.e. `sub f` is *always* a finitary projection, for any
`f`, needing no hypothesis on `f` at all. -/
theorem isFinitaryProjection_sub (f : ApproximableMap E E) : IsFinitaryProjection (sub f) :=
  isFinitaryProjection_of_sub_eq_self (sub_sub f)

/-! ## The finitary-projections-on-`E` ↔ subsystems-of-`E` order-isomorphism

Needed below for `Sub8_6.isFinitary_subApprox` (Theorem 8.6(b)(ii)): the bijection `f ↦ fixedNbhd f`
/ `D ↦ retractionOfSubsystem D` between `{f ∣ sub f = f}` (the finitary projections) and
`{D ∣ D ◁ E}` (the subsystems) that already underlies `sub`'s definition is in fact an
order-isomorphism. Composed with Proposition 6.11's `subsystemReprIso` (the subsystems of `E`
already form a genuine domain, from Lecture VI), this gives Theorem 8.6(b)(ii)'s witness directly —
no new "domain of subsystems" construction is needed here. -/

/-- `fixedNbhd (retractionOfSubsystem h) = D`: the round trip recovering a subsystem `D` from the
retraction it induces. `Y (retractionOfSubsystem h) Y ↔ ∃W∈D, Y⊆W⊆Y`, and `Y⊆W⊆Y` forces `W=Y`, so
this says exactly `D.mem Y` (using `E.mem Y` for free from `D ⊆ E`). -/
theorem fixedNbhd_retractionOfSubsystem {D : NeighborhoodSystem α} (h : D ◁ E) :
    fixedNbhd (Subsystem.retractionOfSubsystem h) = D := by
  apply NeighborhoodSystem.ext
  · intro X
    rw [fixedNbhd_mem, Subsystem.retractionOfSubsystem_rel]
    constructor
    · rintro ⟨hXE, -, -, Y, hY, hXY, hYX⟩
      rw [Set.Subset.antisymm hXY hYX]
      exact hY
    · intro hX
      exact ⟨h.sub hX, h.sub hX, h.sub hX, X, hX, subset_rfl, subset_rfl⟩
  · exact h.master_eq.symm

/-- Every `retractionOfSubsystem h` is already a fixed point of `sub` — immediate from the round
trip `fixedNbhd_retractionOfSubsystem`, since `sub` is *defined* as `retractionOfSubsystem` applied
to `fixedNbhd`. -/
theorem sub_retractionOfSubsystem {D : NeighborhoodSystem α} (h : D ◁ E) :
    sub (Subsystem.retractionOfSubsystem h) = Subsystem.retractionOfSubsystem h := by
  unfold sub
  congr 1
  exact fixedNbhd_retractionOfSubsystem h

/-- **The finitary projections on `E` are order-isomorphic to the subsystems of `E`.** Forward:
`f ↦ ⟨fixedNbhd f, fixedNbhd_subsystem f⟩`; backward: `D ↦ retractionOfSubsystem D` (a fixed point
of `sub`, by `sub_retractionOfSubsystem`). Round trips are `fixedNbhd_retractionOfSubsystem` and
(definitionally) `sub`'s own defining equation; order is preserved/reflected via `sub`'s formula
being monotone in the underlying subsystem (`retractionOfSubsystem_rel`'s witness clause) together
with `Subsystem.subsystem_iff_subset_of_common`. -/
def finitaryProjectionSubsystemEquiv (E : NeighborhoodSystem α) :
    {f : ApproximableMap E E // sub f = f} ≃o {D : NeighborhoodSystem α // D ◁ E} where
  toFun f := ⟨fixedNbhd f.1, fixedNbhd_subsystem f.1⟩
  invFun D := ⟨Subsystem.retractionOfSubsystem D.2, sub_retractionOfSubsystem D.2⟩
  left_inv f := Subtype.ext f.2
  right_inv D := Subtype.ext (fixedNbhd_retractionOfSubsystem D.2)
  map_rel_iff' := by
    intro f g
    constructor
    · intro hle
      have hleD : fixedNbhd f.1 ◁ fixedNbhd g.1 := hle
      have hsub : sub f.1 ≤ sub g.1 := by
        rintro X Z hXZ
        rw [sub_rel] at hXZ ⊢
        obtain ⟨hX, hZ, Y, hY, hXY, hYZ⟩ := hXZ
        exact ⟨hX, hZ, Y, hleD.sub hY, hXY, hYZ⟩
      rwa [f.2, g.2] at hsub
    · intro hfg
      show fixedNbhd f.1 ◁ fixedNbhd g.1
      refine (Subsystem.subsystem_iff_subset_of_common
        (fixedNbhd_subsystem f.1) (fixedNbhd_subsystem g.1)).mpr ?_
      intro X hX
      exact ⟨hX.1, hfg X X hX.2⟩

/-! ## Theorem 8.6, clause 2 (partial): `sub` is itself approximable, and a projection, on
`(E → E)`

Scott's remark: "the correspondence `f ↦ sub(f)` preserves directed unions of `f`'s, thus `sub`
is itself approximable". We realize this via Exercise 2.13 (`ofContinuous`): transported along
`funSpaceEquiv` to `subFilter : (funSpace E E).Element → (funSpace E E).Element`, `sub` is monotone
(`subFilter_mono`, from `sub_mono`) and preserves directed unions (`subFilter_iSupDirected`) — the
latter because `sub`'s defining formula (`sub_rel`) is a *positive* existential in `f`'s relation,
so it commutes with the raw union of relations that `toApproxMap` assigns to a directed union of
filters (`toApproxMap_rel_iSupDirected`, immediate from `mem_iSupDirected`), with no extra
consistency argument needed. `continuous_of_monotone_iSupDirected` then upgrades this to genuine
topological continuity, giving `subApprox := ofContinuous subFilter hc`.

`IsFinitary subApprox` (further below) needs no new "domain of subsystems" construction: it
composes `Fix(subApprox) ≃o {f ∣ sub f = f}` (`subApproxFixIso`) with the
`finitaryProjectionSubsystemEquiv`/`subsystemReprIso` route already available from Theorem 8.6(a)
and Lecture VI's Proposition 6.11.

**Not yet formalized:** the computability clause (Theorem 8.6's clause 3), which needs `E`
effectively given (Def 7.1 machinery), a separate prerequisite. -/

namespace Sub8_6

theorem toFilter_toApproxMap (φ : (funSpace E E).Element) : toFilter (toApproxMap φ) = φ :=
  (funSpaceEquiv E E).left_inv φ

theorem toApproxMap_toFilter (f : ApproximableMap E E) : toApproxMap (toFilter f) = f :=
  (funSpaceEquiv E E).right_inv f

theorem toApproxMap_injective {φ ψ : (funSpace E E).Element} (h : toApproxMap φ = toApproxMap ψ) :
    φ = ψ := by
  rw [← toFilter_toApproxMap φ, ← toFilter_toApproxMap ψ, h]

theorem toApproxMap_monotone {φ ψ : (funSpace E E).Element} (h : φ ≤ ψ) :
    toApproxMap φ ≤ toApproxMap ψ := by
  have := (funSpaceEquiv E E).monotone h
  simpa using this

/-- **`sub`, transported to the function space's own `Element` type via `funSpaceEquiv`.** -/
def subFilter (φ : (funSpace E E).Element) : (funSpace E E).Element :=
  toFilter (sub (toApproxMap φ))

theorem toApproxMap_subFilter (φ : (funSpace E E).Element) :
    toApproxMap (subFilter φ) = sub (toApproxMap φ) :=
  toApproxMap_toFilter _

theorem subFilter_mono {φ ψ : (funSpace E E).Element} (h : φ ≤ ψ) : subFilter φ ≤ subFilter ψ :=
  toFilter_le_iff.mpr (sub_mono (toApproxMap_monotone h))

/-- Directed unions of filters correspond, under `toApproxMap`, to the raw (pointwise) union of the
underlying maps' relations — immediate from `mem_iSupDirected` unfolded through `toApproxMap_rel`.
No consistency/directedness argument is needed for this direction. -/
theorem toApproxMap_rel_iSupDirected {I : Type u} [Nonempty I] (φ : I → (funSpace E E).Element)
    (hdir : ∀ i j, ∃ k, φ i ≤ φ k ∧ φ j ≤ φ k) {X Z : Set α} :
    (toApproxMap (iSupDirected φ hdir)).rel X Z ↔ ∃ i, (toApproxMap (φ i)).rel X Z := by
  simp only [toApproxMap_rel, mem_iSupDirected]

/-- **`sub` commutes with directed unions of relations.** `sub`'s formula (`sub_rel`) is a positive
existential in `f`'s relation (`∃Y, ... ∧ f.rel Y Y ∧ ...`), so it commutes with an arbitrary union
of relations by pure logic (swapping the order of two existentials) — no directedness needed here
either, only for `iSupDirected` to be well-formed in the first place. -/
theorem sub_toApproxMap_iSupDirected {I : Type u} [Nonempty I] (φ : I → (funSpace E E).Element)
    (hdir : ∀ i j, ∃ k, φ i ≤ φ k ∧ φ j ≤ φ k) {X Z : Set α} :
    (sub (toApproxMap (iSupDirected φ hdir))).rel X Z ↔
      ∃ i, (sub (toApproxMap (φ i))).rel X Z := by
  simp only [sub_rel, toApproxMap_rel_iSupDirected]
  constructor
  · rintro ⟨hX, hZ, Y, ⟨hYE, i, hYi⟩, hXY, hYZ⟩
    exact ⟨i, hX, hZ, Y, ⟨hYE, hYi⟩, hXY, hYZ⟩
  · rintro ⟨i, hX, hZ, Y, ⟨hYE, hYi⟩, hXY, hYZ⟩
    exact ⟨hX, hZ, Y, ⟨hYE, i, hYi⟩, hXY, hYZ⟩

/-- **`subFilter` preserves directed unions.** Assembled from `sub_toApproxMap_iSupDirected` and
`toApproxMap_rel_iSupDirected` via `toApproxMap`'s injectivity. -/
theorem subFilter_iSupDirected {I : Type u} [Nonempty I] (φ : I → (funSpace E E).Element)
    (hdir : ∀ i j, ∃ k, φ i ≤ φ k ∧ φ j ≤ φ k)
    (hdir' : ∀ i j, ∃ k, subFilter (φ i) ≤ subFilter (φ k) ∧ subFilter (φ j) ≤ subFilter (φ k)) :
    subFilter (iSupDirected φ hdir) = iSupDirected (fun i => subFilter (φ i)) hdir' := by
  apply toApproxMap_injective
  rw [toApproxMap_subFilter]
  apply ApproximableMap.ext
  intro X Z
  rw [sub_toApproxMap_iSupDirected, toApproxMap_rel_iSupDirected]
  simp only [toApproxMap_subFilter]

theorem subFilter_monotone : Monotone (subFilter (E := E)) := fun _ _ h => subFilter_mono h

/-- **`subFilter` is (topologically) continuous**, via the domain-theoretic bridge
`continuous_of_monotone_iSupDirected` (monotone + preserves directed unions). -/
theorem continuous_subFilter : Continuous (subFilter (E := E)) :=
  continuous_of_monotone_iSupDirected subFilter_monotone subFilter_iSupDirected

/-- **`sub`, packaged as a genuine approximable map on the function space `(E → E)`** (Scott's
remark that `f ↦ sub(f)` is itself approximable), via Exercise 2.13's `ofContinuous`. -/
def subApprox : ApproximableMap (funSpace E E) (funSpace E E) :=
  ofContinuous subFilter continuous_subFilter

theorem toElementMap_subApprox (φ : (funSpace E E).Element) :
    subApprox.toElementMap φ = subFilter φ :=
  toElementMap_ofContinuous subFilter continuous_subFilter φ

theorem subFilter_subFilter (φ : (funSpace E E).Element) :
    subFilter (subFilter φ) = subFilter φ := by
  unfold subFilter
  rw [toApproxMap_toFilter, sub_sub]

theorem toElementMap_subApprox_comp (φ : (funSpace E E).Element) :
    (subApprox.comp subApprox).toElementMap φ = subApprox.toElementMap φ := by
  rw [toElementMap_comp]
  simp only [toElementMap_subApprox]
  exact subFilter_subFilter φ

/-- **`subApprox` is a retraction**: `subApprox ∘ subApprox = subApprox`, from `subFilter`'s own
idempotency (`subFilter_subFilter`), itself inherited from `sub_sub`. Proved via `le_antisymm` on
`le_iff_toElementMap_le` (choice-free), rather than the classical `ext_of_toElementMap`. -/
theorem isRetraction_subApprox : IsRetraction (subApprox (E := E)) :=
  le_antisymm (le_iff_toElementMap_le.mpr fun φ => (toElementMap_subApprox_comp φ).le)
    (le_iff_toElementMap_le.mpr fun φ => (toElementMap_subApprox_comp φ).ge)

/-- **`subApprox` is a projection**: `subApprox ≤ idMap`, from `subFilter φ ≤ φ`, itself
inherited from `sub_le`. -/
theorem subApprox_le_idMap : subApprox ≤ idMap (funSpace E E) := by
  rw [le_iff_toElementMap_le]
  intro φ
  rw [toElementMap_subApprox, toElementMap_idMap]
  calc subFilter φ = toFilter (sub (toApproxMap φ)) := rfl
    _ ≤ toFilter (toApproxMap φ) := toFilter_le_iff.mpr (sub_le _)
    _ = φ := toFilter_toApproxMap φ

/-- **`sub` is itself a *projection* on the function space `(E → E)`** (half of Theorem 8.6's
second clause; the other half, `IsFinitary subApprox`, is below). -/
theorem isProjection_subApprox : IsProjection (subApprox (E := E)) :=
  ⟨isRetraction_subApprox, subApprox_le_idMap⟩

/-! ### Theorem 8.6(b)(ii): `subApprox` is finitary

`Fix(subApprox)` is order-isomorphic to `{f ∣ sub f = f}` (the finitary projections on `E`, via
`toApproxMap`/`toFilter`), which in turn is order-isomorphic to the subsystems of `E`
(`finitaryProjectionSubsystemEquiv`, just above) — and Proposition 6.11 already exhibits the
subsystems of `E` as a genuine domain (`subsystemReprIso`). No new "domain of subsystems"
construction is needed: it was already built in Lecture VI. -/

/-- **`Fix(subApprox) ≃o {f ∣ sub f = f}`.** `subApprox.toElementMap φ = φ` unfolds (via
`toElementMap_subApprox`/`subFilter`) to `toFilter (sub (toApproxMap φ)) = φ`, i.e. exactly
`sub (toApproxMap φ) = toApproxMap φ` after transporting through `toApproxMap`/`toFilter`'s round
trips. -/
def subApproxFixIso :
    {φ : (funSpace E E).Element // subApprox.toElementMap φ = φ} ≃o
      {f : ApproximableMap E E // sub f = f} where
  toFun φ := ⟨toApproxMap φ.1, by
    have h1 : subFilter φ.1 = φ.1 := (toElementMap_subApprox φ.1).symm.trans φ.2
    have h2 : toApproxMap (subFilter φ.1) = toApproxMap φ.1 := congrArg toApproxMap h1
    rwa [toApproxMap_subFilter] at h2⟩
  invFun f := ⟨toFilter f.1, by
    rw [toElementMap_subApprox]
    show subFilter (toFilter f.1) = toFilter f.1
    unfold subFilter
    rw [toApproxMap_toFilter, f.2]⟩
  left_inv φ := Subtype.ext (toFilter_toApproxMap φ.1)
  right_inv f := Subtype.ext (toApproxMap_toFilter f.1)
  map_rel_iff' := by
    intro φ ψ
    show toApproxMap φ.1 ≤ toApproxMap ψ.1 ↔ φ.1 ≤ ψ.1
    exact (funSpaceEquiv E E).map_rel_iff

/-- **Theorem 8.6(b)(ii) (Scott 1981, PRG-19).** `subApprox` is finitary: composing
`subApproxFixIso` with `finitaryProjectionSubsystemEquiv` and Proposition 6.11's
`subsystemReprIso` witnesses `Fix(subApprox)` as (order-isomorphic to) a genuine domain. -/
theorem isFinitary_subApprox : IsFinitary (subApprox (E := E)) :=
  ⟨_, _, ⟨subApproxFixIso.trans
    ((finitaryProjectionSubsystemEquiv E).trans (Proposition611.subsystemReprIso E))⟩⟩

/-- **Theorem 8.6(b), in full.** `subApprox` is a finitary projection on `(E → E)`. -/
theorem isFinitaryProjection_subApprox : IsFinitaryProjection (subApprox (E := E)) :=
  ⟨isProjection_subApprox, isFinitary_subApprox⟩

end Sub8_6

end Scott1980.Neighborhood

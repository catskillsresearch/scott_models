/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Exercise813b
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Clopen

/-!
# Exercise 8.13(c) (Scott 1981, PRG-19, Lecture VIII) — connecting to Cantor space

> (For topologists.) Connect this representation of `𝒰` with the collection of non-empty open
> subsets of the product space `2^ℕ` (= Cantor space).

Per the scoping in `arxiv.md`, the literal "proper filters `≃o` non-empty opens" reading is
**false** (every filter contains `master`, so the naive map is constant); the mathematically
correct route lands on "opens" via the *dual* notion (**ideals**), decomposed into four subgoals
`8.13(c1)`–`(c4)`. This file carries `8.13(c1)`–`(c3)`.

## `8.13(c1)`: Cantor space's clopen algebra is `GeneratedBy genPoint`

`genPoint i := {x : ℕ → Bool | x i = true}` is the literal transcription, on carrier `ℕ → Bool`,
of `8.13(a)`'s `generator i` (on carrier `ℕ`). The headline, `isClopen_iff_generatedBy_genPoint`,
identifies Cantor space's clopen algebra with `GeneratedBy genPoint` exactly:

* `⟸` (`generatedBy_genPoint_isClopen`) is easy structural induction: each `genPoint i` is clopen
  (preimage of a clopen singleton in discrete `Bool` under the continuous projection), and clopens
  are closed under the Boolean operations `GeneratedBy` builds with.
* `⟹` is the substantive direction, via compactness: every open `Y` is covered by `box`es
  (`box I f := {x | ∀ i ∈ I, x i = f i}`, one finite-support box per point of `Y`, from
  `isOpen_pi_iff` — Bool's discreteness lets us shrink to a singleton box at each coordinate) each
  contained in `Y`; each `box` is itself `GeneratedBy genPoint` (`generatedBy_genPoint_box`, by
  `Finset.induction_on`); `Y` clopen (hence compact, as Cantor space is a `CompactSpace`) extracts
  a **finite** subcover, so `Y` is a finite union of `box`es, hence `GeneratedBy genPoint` by
  `generatedBy_genPoint_biUnion`.

`isOpen_iff_iUnion_genPoint` records the immediate corollary that opens (not just clopens) are
exactly unions of `GeneratedBy genPoint` sets — the "topological basis" fact `8.13(c)`'s scoping
row anticipated, now free from the clopen identification.
-/

namespace Scott1980.Neighborhood

/-! ### `genPoint`: the coordinate-projection clopens of Cantor space -/

/-- The `i`-th coordinate-projection basic clopen of Cantor space `ℕ → Bool`: the literal
transcription, on this carrier, of `8.13(a)`'s `generator i`. -/
def genPoint (i : ℕ) : Set (ℕ → Bool) := (fun x : ℕ → Bool => x i) ⁻¹' {true}

@[simp] theorem mem_genPoint {i : ℕ} {x : ℕ → Bool} : x ∈ genPoint i ↔ x i = true := Iff.rfl

theorem isClopen_genPoint (i : ℕ) : IsClopen (genPoint i) :=
  (isClopen_discrete ({true} : Set Bool)).preimage (continuous_apply i)

/-- `GeneratedBy genPoint ∅` — recorded separately since `GeneratedBy`'s only route to `∅` is via
`compl` of `univ`. -/
theorem generatedBy_genPoint_empty : GeneratedBy genPoint (∅ : Set (ℕ → Bool)) := by
  simpa using GeneratedBy.univ.compl

/-- **Easy direction**: everything `GeneratedBy genPoint` is clopen. -/
theorem generatedBy_genPoint_isClopen {Y : Set (ℕ → Bool)} (h : GeneratedBy genPoint Y) :
    IsClopen Y := by
  induction h with
  | of i => exact isClopen_genPoint i
  | univ => exact isClopen_univ
  | inter _ _ ih1 ih2 => exact ih1.inter ih2
  | union _ _ ih1 ih2 => exact ih1.union ih2
  | compl _ ih => exact ih.compl

theorem isOpen_genPoint (i : ℕ) : IsOpen (genPoint i) := (isClopen_genPoint i).isOpen

/-! ### `box`: finite-support basic clopens -/

/-- The basic clopen pinning every coordinate in `I` to match `f`, and leaving the rest free —
the standard basis element of the product topology on `ℕ → Bool`. -/
def box (I : Finset ℕ) (f : ℕ → Bool) : Set (ℕ → Bool) := {x | ∀ i ∈ I, x i = f i}

@[simp] theorem mem_box {I : Finset ℕ} {f x : ℕ → Bool} :
    x ∈ box I f ↔ ∀ i ∈ I, x i = f i := Iff.rfl

theorem self_mem_box (I : Finset ℕ) (f : ℕ → Bool) : f ∈ box I f := fun _ _ => rfl

theorem generatedBy_genPoint_box (I : Finset ℕ) (f : ℕ → Bool) :
    GeneratedBy genPoint (box I f) := by
  induction I using Finset.induction_on with
  | empty => simpa [box] using GeneratedBy.univ
  | insert a s ha ih =>
    have hstep : box (insert a s) f =
        (if f a = true then genPoint a else (genPoint a)ᶜ) ∩ box s f := by
      ext x
      by_cases hfa : f a = true
      · simp [hfa]
      · have hfa' : f a = false := by simpa using hfa
        simp [hfa]
    rw [hstep]
    split_ifs with hfa
    · exact (GeneratedBy.of a).inter ih
    · exact (GeneratedBy.of a).compl.inter ih

theorem isOpen_box (I : Finset ℕ) (f : ℕ → Bool) : IsOpen (box I f) :=
  (generatedBy_genPoint_isClopen (generatedBy_genPoint_box I f)).isOpen

/-- Finite unions of `box`es (over any index type) are `GeneratedBy genPoint` — the same
`Finset.induction_on`/`Finset.set_biUnion_insert` idiom as `8.13(a)`'s `generatedBy_biUnion_affine`. -/
theorem generatedBy_genPoint_biUnion {β : Type*} (t : Finset β) (I : β → Finset ℕ)
    (f : β → ℕ → Bool) : GeneratedBy genPoint (⋃ b ∈ t, box (I b) (f b)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using generatedBy_genPoint_empty
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    exact (generatedBy_genPoint_box _ _).union ih

/-! ### The headline: clopens are exactly `GeneratedBy genPoint` -/

/-- **`8.13(c1)`.** Cantor space's clopen algebra is exactly `GeneratedBy genPoint` — the free
Boolean algebra on `ℵ₀` generators (`8.13(a)`), transported to carrier `ℕ → Bool`. -/
theorem isClopen_iff_generatedBy_genPoint {Y : Set (ℕ → Bool)} :
    IsClopen Y ↔ GeneratedBy genPoint Y := by
  refine ⟨fun hY => ?_, generatedBy_genPoint_isClopen⟩
  classical
  have hbox : ∀ f ∈ Y, ∃ I : Finset ℕ, box I f ⊆ Y := by
    intro f hf
    obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.mp hY.isOpen f hf
    refine ⟨I, fun x hx => hIu fun i hi => ?_⟩
    rw [hx i hi]
    exact (hu i hi).2
  choose Ifn hIfn using hbox
  set Ig : Y → Finset ℕ := fun f => Ifn (f : ℕ → Bool) f.2
  set fg : Y → ℕ → Bool := fun f => (f : ℕ → Bool)
  have hcover : Y ⊆ ⋃ f : Y, box (Ig f) (fg f) :=
    fun f hf => Set.mem_iUnion.mpr ⟨⟨f, hf⟩, self_mem_box _ _⟩
  have hcompact : IsCompact Y := hY.isClosed.isCompact
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover (fun f : Y => box (Ig f) (fg f))
    (fun f => isOpen_box _ _) hcover
  have heq : Y = ⋃ f ∈ t, box (Ig f) (fg f) := by
    refine Set.Subset.antisymm ht (Set.iUnion₂_subset fun f _ => hIfn (f : ℕ → Bool) f.2)
  rw [heq]
  exact generatedBy_genPoint_biUnion t Ig fg

/-- Immediate corollary: **opens** (not just clopens) of Cantor space are exactly unions of
`GeneratedBy genPoint` clopens — the "topological basis" fact underlying the scoping row's
candidate `(ii)`. -/
theorem isOpen_iff_exists_iUnion_generatedBy {O : Set (ℕ → Bool)} :
    IsOpen O ↔ ∃ (S : Set (Set (ℕ → Bool))), (∀ Y ∈ S, GeneratedBy genPoint Y) ∧ O = ⋃ Y ∈ S, Y := by
  constructor
  · intro hO
    refine ⟨{Y | GeneratedBy genPoint Y ∧ Y ⊆ O}, fun Y hY => hY.1, ?_⟩
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro hx
      obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.mp hO x hx
      have hxbox : x ∈ box I x := self_mem_box I x
      exact ⟨box I x, ⟨generatedBy_genPoint_box I x,
        fun y hy => hIu fun i hi => by rw [hy i hi]; exact (hu i hi).2⟩, hxbox⟩
    · rintro ⟨Y, ⟨_, hYO⟩, hxY⟩
      exact hYO hxY
  · rintro ⟨S, hS, rfl⟩
    exact isOpen_biUnion fun Y hY => (generatedBy_genPoint_isClopen (hS Y hY)).isOpen

/-!
## `8.13(c2)`: `generator`/`genPoint` realize the same free Boolean algebra

`8.13(b)`'s `Formula`/`evalV` already has one evaluation, `evalSet : Formula → Set ℕ`
(`var i ↦ generator i`). A *second* evaluation, `evalSet' : Formula → Set (ℕ → Bool)`
(`var i ↦ genPoint i`), is even simpler than the first: since Cantor space's own points
`x : ℕ → Bool` already *are* valuations, `mem_evalSet'_iff` needs no bit-encoding step (unlike
`8.13(b)`'s `mem_evalSet_iff`, which had to translate `n : ℕ` into a valuation via its bits) —
and consequently `semanticEquiv_iff_evalSet'_eq` needs no finitary agreement argument either.

`Corresponds X Y := ∃ φ, evalSet φ = X ∧ evalSet' φ = Y` witnesses, via a common `Formula`, that
`generator`'s algebra `{X | GeneratedBy generator X}` and `genPoint`'s algebra
`{Y | GeneratedBy genPoint Y}` are "the same" abstract Boolean algebra: `Corresponds` relates them
functionally in both directions (`exists_corresponds_of_generatedBy_generator/genPoint`,
`Corresponds.unique_left/right`) and respects `⊆` (`Corresponds.subset_iff`) — i.e. it is exactly
an order-isomorphism between the two concrete algebras, without needing any (nonexistent) bijection
of the wildly different underlying carriers `ℕ`/`ℕ → Bool`.
-/

/-- The *same* recursion as `evalSet`, but interpreted via `genPoint` instead of `generator`. -/
def evalSet' : Formula → Set (ℕ → Bool)
  | .var i => genPoint i
  | .bot => ∅
  | .top => Set.univ
  | .neg φ => (evalSet' φ)ᶜ
  | .and φ ψ => evalSet' φ ∩ evalSet' ψ
  | .or φ ψ => evalSet' φ ∪ evalSet' ψ

/-- Cantor space's own points already *are* valuations, so this bridge is definitional-level
simple: no bit-encoding step is needed (contrast `8.13(b)`'s `mem_evalSet_iff`). -/
theorem mem_evalSet'_iff (x : ℕ → Bool) (φ : Formula) :
    x ∈ evalSet' φ ↔ evalV x φ = true := by
  induction φ with
  | var i => simp [evalSet', evalV]
  | bot => simp [evalSet', evalV]
  | top => simp [evalSet', evalV]
  | neg φ ih => simp [evalSet', evalV, ih]
  | and φ ψ ihφ ihψ => simp [evalSet', evalV, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [evalSet', evalV, ihφ, ihψ]

theorem generatedBy_iff_exists_evalSet' {Y : Set (ℕ → Bool)} :
    GeneratedBy genPoint Y ↔ ∃ φ : Formula, evalSet' φ = Y := by
  constructor
  · intro h
    induction h with
    | of i => exact ⟨.var i, rfl⟩
    | univ => exact ⟨.top, rfl⟩
    | @inter X Y _ _ ih1 ih2 =>
      obtain ⟨φ, rfl⟩ := ih1; obtain ⟨ψ, rfl⟩ := ih2
      exact ⟨.and φ ψ, rfl⟩
    | @union X Y _ _ ih1 ih2 =>
      obtain ⟨φ, rfl⟩ := ih1; obtain ⟨ψ, rfl⟩ := ih2
      exact ⟨.or φ ψ, rfl⟩
    | @compl X _ ih =>
      obtain ⟨φ, rfl⟩ := ih
      exact ⟨.neg φ, rfl⟩
  · rintro ⟨φ, rfl⟩
    induction φ with
    | var i => exact GeneratedBy.of i
    | bot => simpa using GeneratedBy.univ.compl
    | top => exact GeneratedBy.univ
    | neg φ ih => exact ih.compl
    | and φ ψ ihφ ihψ => exact ihφ.inter ihψ
    | or φ ψ ihφ ihψ => exact ihφ.union ihψ

/-- No finitary agreement argument is needed here (contrast `8.13(b)`'s `semanticEquiv_iff_
evalSet_eq`): `evalV`'s own domain `ℕ → Bool` already *is* Cantor space's points. -/
theorem semanticEquiv_iff_evalSet'_eq {φ ψ : Formula} :
    SemanticEquiv φ ψ ↔ evalSet' φ = evalSet' ψ := by
  constructor
  · intro h
    ext x
    rw [mem_evalSet'_iff, mem_evalSet'_iff, h]
  · intro h v
    have hmem : v ∈ evalSet' φ ↔ v ∈ evalSet' ψ := by rw [h]
    rw [mem_evalSet'_iff, mem_evalSet'_iff] at hmem
    rcases hφ : evalV v φ with - | - <;> rcases hψ : evalV v ψ with - | - <;> simp_all

/-- The same finitary-free argument as `semanticEquiv_iff_evalSet'_eq`, for entailment. -/
theorem entails_iff_evalSet'_subset {φ ψ : Formula} :
    Entails φ ψ ↔ evalSet' φ ⊆ evalSet' ψ := by
  constructor
  · intro h x hx
    rw [mem_evalSet'_iff] at hx ⊢
    exact h _ hx
  · intro h v hv
    exact (mem_evalSet'_iff v ψ).mp (h ((mem_evalSet'_iff v φ).mpr hv))

/-- `Lindenbaum`'s canonical map to Cantor-space clopens, the counterpart of `8.13(b)`'s
`Lindenbaum.toSet`. -/
def Lindenbaum.toSet' : Lindenbaum → Set (ℕ → Bool) :=
  Quotient.lift evalSet' fun _ _ h => semanticEquiv_iff_evalSet'_eq.mp h

@[simp] theorem Lindenbaum.toSet'_mk (φ : Formula) :
    Lindenbaum.toSet' ⟦φ⟧ = evalSet' φ := rfl

theorem Lindenbaum.toSet'_injective : Function.Injective Lindenbaum.toSet' := by
  intro x y
  induction x using Quotient.ind with
  | _ φ =>
    induction y using Quotient.ind with
    | _ ψ =>
      intro h
      exact Quotient.sound (semanticEquiv_iff_evalSet'_eq.mpr h)

theorem Lindenbaum.range_toSet' :
    Set.range Lindenbaum.toSet' = {Y | GeneratedBy genPoint Y} := by
  ext Y
  simp only [Set.mem_range, Set.mem_setOf_eq, generatedBy_iff_exists_evalSet']
  constructor
  · rintro ⟨x, rfl⟩
    induction x using Quotient.ind with
    | _ φ => exact ⟨φ, rfl⟩
  · rintro ⟨φ, rfl⟩
    exact ⟨⟦φ⟧, rfl⟩

/-- **`8.13(c2)`, the headline.** `X` and `Y` are the `evalSet`/`evalSet'` images of a *common*
`Formula` — i.e. the same node of the (unique, up to `SemanticEquiv`) Lindenbaum algebra. -/
def Corresponds (X : Set ℕ) (Y : Set (ℕ → Bool)) : Prop :=
  ∃ φ : Formula, evalSet φ = X ∧ evalSet' φ = Y

theorem exists_corresponds_of_generatedBy_generator {X : Set ℕ} (hX : GeneratedBy generator X) :
    ∃ Y, Corresponds X Y := by
  obtain ⟨φ, hφ⟩ := generatedBy_iff_exists_evalSet.mp hX
  exact ⟨evalSet' φ, φ, hφ, rfl⟩

theorem exists_corresponds_of_generatedBy_genPoint {Y : Set (ℕ → Bool)}
    (hY : GeneratedBy genPoint Y) : ∃ X, Corresponds X Y := by
  obtain ⟨φ, hφ⟩ := generatedBy_iff_exists_evalSet'.mp hY
  exact ⟨evalSet φ, φ, rfl, hφ⟩

theorem Corresponds.unique_right {X : Set ℕ} {Y₁ Y₂ : Set (ℕ → Bool)}
    (h1 : Corresponds X Y₁) (h2 : Corresponds X Y₂) : Y₁ = Y₂ := by
  obtain ⟨φ, hφX, hφY⟩ := h1
  obtain ⟨ψ, hψX, hψY⟩ := h2
  have hse : SemanticEquiv φ ψ := semanticEquiv_iff_evalSet_eq.mpr (hφX.trans hψX.symm)
  rw [← hφY, ← hψY, semanticEquiv_iff_evalSet'_eq.mp hse]

theorem Corresponds.unique_left {X₁ X₂ : Set ℕ} {Y : Set (ℕ → Bool)}
    (h1 : Corresponds X₁ Y) (h2 : Corresponds X₂ Y) : X₁ = X₂ := by
  obtain ⟨φ, hφX, hφY⟩ := h1
  obtain ⟨ψ, hψX, hψY⟩ := h2
  have hse : SemanticEquiv φ ψ := semanticEquiv_iff_evalSet'_eq.mpr (hφY.trans hψY.symm)
  rw [← hφX, ← hψX, semanticEquiv_iff_evalSet_eq.mp hse]

/-- `Corresponds` also matches `⊆` — i.e. it is an order-isomorphism between the two concrete
algebras, not just a bijection. -/
theorem Corresponds.subset_iff {X₁ X₂ : Set ℕ} {Y₁ Y₂ : Set (ℕ → Bool)}
    (h1 : Corresponds X₁ Y₁) (h2 : Corresponds X₂ Y₂) : X₁ ⊆ X₂ ↔ Y₁ ⊆ Y₂ := by
  obtain ⟨φ, hφX, hφY⟩ := h1
  obtain ⟨ψ, hψX, hψY⟩ := h2
  subst hφX; subst hφY; subst hψX; subst hψY
  exact ⟨fun hsub => entails_iff_evalSet'_subset.mp (entails_iff_evalSet_subset.mpr hsub),
    fun hsub => entails_iff_evalSet_subset.mp (entails_iff_evalSet'_subset.mpr hsub)⟩

theorem Corresponds.generatedBy_left {X : Set ℕ} {Y : Set (ℕ → Bool)} (h : Corresponds X Y) :
    GeneratedBy generator X := by
  obtain ⟨φ, rfl, -⟩ := h; exact generatedBy_iff_exists_evalSet.mpr ⟨φ, rfl⟩

theorem Corresponds.generatedBy_right {X : Set ℕ} {Y : Set (ℕ → Bool)} (h : Corresponds X Y) :
    GeneratedBy genPoint Y := by
  obtain ⟨φ, -, rfl⟩ := h; exact generatedBy_iff_exists_evalSet'.mpr ⟨φ, rfl⟩

/-- `Corresponds` matches `Set.Nonempty` — via `n ↦ fun i => n.testBit i` directly for `→`, and
`exists_bitsOf_agree` (`8.13(b)`) for `←`, since a formula's satisfying valuation can always be
swapped for a matching bit-derived one on its own (finite) variables. -/
theorem Corresponds.nonempty_iff {X : Set ℕ} {Y : Set (ℕ → Bool)} (h : Corresponds X Y) :
    X.Nonempty ↔ Y.Nonempty := by
  obtain ⟨φ, rfl, rfl⟩ := h
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨fun i => n.testBit i, (mem_evalSet'_iff _ φ).mpr ((mem_evalSet_iff n φ).mp hn)⟩
  · rintro ⟨v, hv⟩
    obtain ⟨n, hn⟩ := exists_bitsOf_agree (vars φ) v
    refine ⟨n, (mem_evalSet_iff n φ).mpr ?_⟩
    rw [evalV_eq_of_agree hn]
    exact (mem_evalSet'_iff v φ).mp hv

theorem Corresponds.inter {X₁ X₂ : Set ℕ} {Y₁ Y₂ : Set (ℕ → Bool)}
    (h1 : Corresponds X₁ Y₁) (h2 : Corresponds X₂ Y₂) :
    Corresponds (X₁ ∩ X₂) (Y₁ ∩ Y₂) := by
  obtain ⟨φ, hφX, hφY⟩ := h1
  obtain ⟨ψ, hψX, hψY⟩ := h2
  refine ⟨.and φ ψ, ?_, ?_⟩
  · show evalSet φ ∩ evalSet ψ = X₁ ∩ X₂; rw [hφX, hψX]
  · show evalSet' φ ∩ evalSet' ψ = Y₁ ∩ Y₂; rw [hφY, hψY]

/-!
## `8.13(c3)`: ideal/filter complementation

A general, `g`-generic toolkit (not specific to Cantor space): for a Boolean subalgebra of sets
`GeneratedBy g` closed under complement, `Y ↦ Yᶜ` turns a *downward*-closed, finite-join-closed,
`univ`-excluding family (an **ideal**) into an *upward*-closed, finite-meet-closed, `∅`-excluding,
`univ`-containing family — i.e. exactly the four fields `8.13(a)`'s `V.Element`
(`Basic.lean`'s `NeighborhoodSystem.Element`) bundles as a "proper filter." `dualFilter` is stated
as a plain `Set (Set α) → Set (Set α)` operation (not a bundled structure) with each of the four
properties as its own small lemma, so `8.13(c4)` can assemble a genuine `V.Element` term directly
from them.
-/

/-- `Y ↦ Yᶜ`, applied to a whole family: turns an ideal into (the membership predicate of) a
filter, and vice versa (`dualFilter` is its own inverse, `dualFilter_dualFilter`). -/
def dualFilter {α : Type*} (x : Set (Set α)) : Set (Set α) := {Y | Yᶜ ∈ x}

@[simp] theorem mem_dualFilter {α : Type*} {x : Set (Set α)} {Y : Set α} :
    Y ∈ dualFilter x ↔ Yᶜ ∈ x := Iff.rfl

@[simp] theorem dualFilter_dualFilter {α : Type*} (x : Set (Set α)) :
    dualFilter (dualFilter x) = x := by
  ext Y; simp [dualFilter]

/-- Dualizing preserves membership in the algebra generated by `g` (using that `GeneratedBy g` is
closed under `compl`). -/
theorem generatedBy_of_mem_dualFilter {α : Type*} {g : ℕ → Set α} {x : Set (Set α)}
    (hx : ∀ Y ∈ x, GeneratedBy g Y) {Y : Set α} (hY : Y ∈ dualFilter x) : GeneratedBy g Y := by
  simpa using (hx _ hY).compl

/-- An ideal containing `∅` dualizes to a filter containing `univ`. -/
theorem univ_mem_dualFilter {α : Type*} {x : Set (Set α)} (h : (∅ : Set α) ∈ x) :
    Set.univ ∈ dualFilter x := by simpa [dualFilter] using h

/-- An ideal excluding `univ` dualizes to a filter excluding `∅`. -/
theorem not_empty_mem_dualFilter {α : Type*} {x : Set (Set α)} (h : Set.univ ∉ x) :
    (∅ : Set α) ∉ dualFilter x := by simpa [dualFilter] using h

/-- An ideal closed under (binary, hence finite) union dualizes to a filter closed under
intersection (`(Y ∩ Z)ᶜ = Yᶜ ∪ Zᶜ`, De Morgan). -/
theorem inter_mem_dualFilter {α : Type*} {x : Set (Set α)}
    (hx : ∀ Y ∈ x, ∀ Z ∈ x, Y ∪ Z ∈ x) {Y Z : Set α}
    (hY : Y ∈ dualFilter x) (hZ : Z ∈ dualFilter x) : Y ∩ Z ∈ dualFilter x := by
  have h := hx _ hY _ hZ
  simpa [dualFilter, Set.compl_inter] using h

/-- An ideal downward-closed within `GeneratedBy g` dualizes to a filter upward-closed within
`GeneratedBy g` (De Morgan again: `Z ⊆ Y ↔ Yᶜ ⊆ Zᶜ`). -/
theorem up_mem_dualFilter {α : Type*} {g : ℕ → Set α} {x : Set (Set α)}
    (hx : ∀ Y ∈ x, ∀ Z, GeneratedBy g Z → Z ⊆ Y → Z ∈ x) {Y Z : Set α}
    (hY : Y ∈ dualFilter x) (hZg : GeneratedBy g Z) (hYZ : Y ⊆ Z) : Z ∈ dualFilter x := by
  have hcompl : Zᶜ ⊆ Yᶜ := Set.compl_subset_compl.mpr hYZ
  simpa [dualFilter] using hx _ hY _ hZg.compl hcompl

/-!
## `8.13(c4)`: assembly

For an open `O ⊆ 2^ℕ` with `O ≠ Set.univ`, `idealOf O` ("the clopens inside `O`") is a proper
ideal of `GeneratedBy genPoint`, so (`8.13(c3)`) `dualFilter (idealOf O)` is a proper filter of
`GeneratedBy genPoint`; transporting through `Corresponds` (`8.13(c2)`) gives a proper filter of
`GeneratedBy generator`, i.e. (`8.13(a)`) a genuine element of `V` (hence, via `exercise813a`, of
`U`) — `elementOfOpen`.

**On Scott's "non-empty":** taken at face value this is the *wrong* exclusion for this specific
construction. Emptiness of `O` never breaks properness here — `idealOf ∅ = {∅}` dualizes to the
filter `{Set.univ}`, the perfectly legitimate (if degenerate) **bottom** element of `U`. What
actually breaks properness is `O = Set.univ`: then `idealOf O` contains `Set.univ` itself
(violating "excludes `univ`"), and dualizing produces a "filter" containing `∅` — exactly what
`V.Element`'s `sub` field (via `V_mem_iff_generatedBy`, which excludes `∅`) forbids. So the
precise hypothesis this construction needs is `O ≠ Set.univ` ("proper"), not `O.Nonempty` — Scott's
remark is informal here, consistent with the parenthetical's own looser phrasing (`arxiv.md`'s
scoping already flagged the parallel "opens vs. closeds" imprecision).
-/

/-- The clopens contained in `O`: a proper ideal of `GeneratedBy genPoint` whenever `O ≠ univ`. -/
def idealOf (O : Set (ℕ → Bool)) : Set (Set (ℕ → Bool)) := {Y | GeneratedBy genPoint Y ∧ Y ⊆ O}

theorem empty_mem_idealOf (O : Set (ℕ → Bool)) : (∅ : Set (ℕ → Bool)) ∈ idealOf O :=
  ⟨generatedBy_genPoint_empty, Set.empty_subset _⟩

theorem univ_not_mem_idealOf {O : Set (ℕ → Bool)} (hO : O ≠ Set.univ) : Set.univ ∉ idealOf O :=
  fun h => hO (Set.univ_subset_iff.mp h.2)

theorem union_mem_idealOf {O Y Z : Set (ℕ → Bool)} (hY : Y ∈ idealOf O) (hZ : Z ∈ idealOf O) :
    Y ∪ Z ∈ idealOf O := ⟨hY.1.union hZ.1, Set.union_subset hY.2 hZ.2⟩

theorem down_mem_idealOf {O Y Z : Set (ℕ → Bool)} (hY : Y ∈ idealOf O)
    (hZg : GeneratedBy genPoint Z) (hZY : Z ⊆ Y) : Z ∈ idealOf O := ⟨hZg, hZY.trans hY.2⟩

/-- **`8.13(c4)`, the headline connection.** Every open `O ≠ Set.univ` of Cantor space `2^ℕ`
determines a genuine element of `V` (hence of `U`, via `exercise813a`) — the proper filter "dual"
to the ideal of clopens inside `O`, transported to `ℕ`-clopens via `Corresponds`. This is the
precise sense in which `8.13(a)`'s filter-domain representation of `U` connects with the
(non-`univ`, and per Scott's remark, morally non-empty) open subsets of Cantor space. -/
def elementOfOpen {O : Set (ℕ → Bool)} (hO : O ≠ Set.univ) : V.Element where
  mem X := ∃ Y, Y ∈ dualFilter (idealOf O) ∧ Corresponds X Y
  sub := by
    rintro X ⟨Y, hY, hCorr⟩
    have hYne : Y ≠ ∅ := fun hYe =>
      not_empty_mem_dualFilter (univ_not_mem_idealOf hO) (hYe ▸ hY)
    exact V_mem_iff_generatedBy.mpr ⟨hCorr.generatedBy_left,
      hCorr.nonempty_iff.mpr (Set.nonempty_iff_ne_empty.mpr hYne)⟩
  master_mem := ⟨Set.univ, univ_mem_dualFilter (empty_mem_idealOf O), .top, rfl, rfl⟩
  inter_mem := by
    rintro X₁ X₂ ⟨Y₁, hY₁, hC₁⟩ ⟨Y₂, hY₂, hC₂⟩
    exact ⟨Y₁ ∩ Y₂,
      inter_mem_dualFilter (fun Y hY Z hZ => union_mem_idealOf hY hZ) hY₁ hY₂, hC₁.inter hC₂⟩
  up_mem := by
    rintro X₁ X₂ ⟨Y₁, hY₁, hC₁⟩ hX₂mem hX₁X₂
    obtain ⟨hX₂gen, -⟩ := V_mem_iff_generatedBy.mp hX₂mem
    obtain ⟨ψ, hψ⟩ := generatedBy_iff_exists_evalSet.mp hX₂gen
    have hC₂ : Corresponds X₂ (evalSet' ψ) := ⟨ψ, hψ, rfl⟩
    refine ⟨evalSet' ψ,
      up_mem_dualFilter (fun Y hY Z hZg hZY => down_mem_idealOf hY hZg hZY) hY₁
        hC₂.generatedBy_right ((hC₁.subset_iff hC₂).mp hX₁X₂),
      hC₂⟩

end Scott1980.Neighborhood

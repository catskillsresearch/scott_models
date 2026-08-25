/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott_models
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sum.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.DirSupClosed
import Mathlib.Order.Directed
import Mathlib.Order.FixedPoints
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Hom.WithTopBot
import Mathlib.Order.Ideal
import Mathlib.Order.ScottContinuity
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.WithBot
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Order
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Topology.Separation.Basic

/-!
# Single-file ScottModels

Self-contained flatten of the bridge theorems in `ScottModels/` together
with the transitive vendor modules they import (`vendor/scott1972`,
`vendor/scott1980`, `vendor/scott1982`). Mathlib stays imported.
Regenerate with `python3 scripts/generate_everything.py`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Vendor dependencies -/

-- Vendor 1980 — Scott1980.Neighborhood.Basic (from vendor/scott1980/Scott1980/Neighborhood/Basic.lean)

/-!
# Neighborhood systems (Scott 1981, PRG-19, §1) — foundations

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, Technical
Monograph PRG-19, Oxford (May 1981), Lecture I, *Domains given by neighbourhoods*.

Scott fixes a non-empty set `Δ` of *tokens* and considers a family `𝒟` of subsets of `Δ`
(the *neighbourhoods*). The order is *reversed* relative to information: a **smaller**
neighbourhood carries **more** information. A finite sequence of neighbourhoods is
*consistent* when it has a common lower bound inside `𝒟` (a `Z ∈ 𝒟` contained in all of
them); a neighbourhood system is closed under intersections of consistent finite sequences.

This file formalizes the very first page of §1:

* **Definition 1.1** — `NeighborhoodSystem`: a family with `Δ ∈ 𝒟` (condition (i)) and
  closure under consistent binary intersections (condition (ii)).
* **Factoid 1.1a / 1.1b** — Scott's recursive *convention* for the finite intersection
  `⋂_{i < n} Xᵢ` (`interUpTo`): the empty intersection is `Δ`, and the `(n+1)`-fold
  intersection peels off the last factor.
* **Theorem 1.1c** — "from (ii) we can extend the intersection property to any finite
  sequence", and *consequently* a finite sequence is consistent **iff** its intersection
  lies in `𝒟`.

The §1 core is deliberately **constructive**: Scott uses *partial* filters so that the
basic theory avoids maximal-filter existence (Zorn/choice). Every theorem here depends only
on `propext`/`Quot.sound` (no `Classical.choice`).
-/

namespace Scott1980.Neighborhood

/-- **Definition 1.1 (Scott 1981, PRG-19).** A *neighbourhood system* over a token type
`α`. `mem X` means "`X` is a neighbourhood" (`X ∈ 𝒟`), and `master` is Scott's least
informative neighbourhood `Δ` (the whole token set, "ask me no questions").

The two conditions are exactly Scott's:

* (i)  `Δ ∈ 𝒟`                                        — `master_mem`;
* (ii) whenever `X, Y, Z ∈ 𝒟` and `Z ⊆ X ∩ Y`, then `X ∩ Y ∈ 𝒟` — `inter_mem`.

We keep `master` as a field (rather than hard-wiring `Set.univ`) to stay faithful to
Scott's `Δ` notation, and record Scott's standing assumption `𝒟 ⊆ 𝒫(Δ)` as the field
`sub_master` (every neighbourhood is a subset of `Δ`). Scott also assumes from the outset
that the token set `Δ` is non-empty; `master_nonempty` records this standing assumption
explicitly. The subset condition is what makes the principal filter `↑X` (Definition 1.7)
contain `Δ`, and underlies the least element `⊥ = ↑Δ`. -/
structure NeighborhoodSystem (α : Type*) where
  /-- `mem X` holds iff `X` is a neighbourhood of the system (`X ∈ 𝒟`). -/
  mem : Set α → Prop
  /-- Scott's distinguished least-informative neighbourhood `Δ`. -/
  master : Set α
  /-- Scott's standing assumption that the token set `Δ` is non-empty. -/
  master_nonempty : master.Nonempty
  /-- (i) `Δ ∈ 𝒟`. -/
  master_mem : mem master
  /-- (ii) Closure under intersection of a *consistent* pair: if `X, Y, Z ∈ 𝒟` with the
  witness `Z ⊆ X ∩ Y`, then `X ∩ Y ∈ 𝒟`. -/
  inter_mem : ∀ {X Y Z : Set α}, mem X → mem Y → mem Z → Z ⊆ X ∩ Y → mem (X ∩ Y)
  /-- Scott's `𝒟 ⊆ 𝒫(Δ)`: every neighbourhood is a subset of the master neighbourhood `Δ`. -/
  sub_master : ∀ {X : Set α}, mem X → X ⊆ master

/-- Scott's *"very special circumstance"* (the prose after Examples 1.2–1.4): a family `𝒟`
is **nested-or-disjoint** when any two of its members are either nested (one included in the
other) or disjoint. -/
def NestedOrDisjoint {α : Type*} (mem : Set α → Prop) : Prop :=
  ∀ ⦃X Y : Set α⦄, mem X → mem Y → X ⊆ Y ∨ Y ⊆ X ∨ X ∩ Y = ∅

/-- **Factoid 1.4a (Scott 1981, PRG-19).** "In these systems two neighbourhoods are either
disjoint or one is included in the other": a family containing `Δ` whose members are pairwise
nested-or-disjoint **is** a neighbourhood system. This uniformly explains why Examples 1.2,
1.3 and 1.4 satisfy Definition 1.1.

The verification of condition (ii) needs no choice: if `X, Y` are nested then `X ∩ Y` is the
smaller (already in `𝒟`); if they are disjoint then the consistency witness `Z ⊆ X ∩ Y = ∅`
forces `Z = ∅`, whence `X ∩ Y = ∅ = Z ∈ 𝒟`. The caller supplies `master_nonempty`
(Scott's standing `Δ ≠ ∅` assumption) and `sub_master` (`𝒟 ⊆ 𝒫(Δ)`) directly. -/
def NeighborhoodSystem.ofNestedOrDisjoint {α : Type*} (mem : Set α → Prop) (master : Set α)
    (master_nonempty : master.Nonempty) (master_mem : mem master) (hnd : NestedOrDisjoint mem)
    (sub_master : ∀ {X : Set α}, mem X → X ⊆ master) : NeighborhoodSystem α where
  mem := mem
  master := master
  master_nonempty := master_nonempty
  master_mem := master_mem
  sub_master := sub_master
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    rcases hnd hX hY with h | h | h
    · rwa [Set.inter_eq_left.mpr h]
    · rwa [Set.inter_eq_right.mpr h]
    · rw [h]
      rw [h] at hZsub
      rwa [← Set.subset_empty_iff.mp hZsub]

/-- **Exercise 1.19 (Scott 1981, PRG-19) — positivity, condition (ii′).** A neighbourhood
system is *positive* when Scott's (ii) is strengthened to the biconditional **(ii′)**: for
`X, Y ∈ 𝒟`, the intersection `X ∩ Y` is a neighbourhood **iff** it is non-empty. -/
def NeighborhoodSystem.IsPositive {α : Type*} (V : NeighborhoodSystem α) : Prop :=
  ∀ ⦃X Y : Set α⦄, V.mem X → V.mem Y → (V.mem (X ∩ Y) ↔ (X ∩ Y).Nonempty)

/-- **Exercise 1.19 — a positive system is a neighbourhood system.** Scott: "*prove that a
positive neighbourhood system is indeed a neighbourhood system*". From the raw data — (i)
`Δ ∈ 𝒟`, `𝒟 ⊆ 𝒫(Δ)`, and the positivity axiom (ii′) — condition (ii) follows: a consistency
witness `Z ⊆ X ∩ Y` with `Z ∈ 𝒟` is itself non-empty (apply (ii′) to `Z ∩ Z = Z`), so
`X ∩ Y ⊇ Z` is non-empty, whence `X ∩ Y ∈ 𝒟` by (ii′). Choice-free. -/
def NeighborhoodSystem.ofPositive {α : Type*} (mem : Set α → Prop) (master : Set α)
    (master_nonempty : master.Nonempty) (master_mem : mem master)
    (sub_master : ∀ {X : Set α}, mem X → X ⊆ master)
    (pos : ∀ ⦃X Y : Set α⦄, mem X → mem Y → (mem (X ∩ Y) ↔ (X ∩ Y).Nonempty)) :
    NeighborhoodSystem α where
  mem := mem
  master := master
  master_nonempty := master_nonempty
  master_mem := master_mem
  sub_master := sub_master
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    have hZZ : mem (Z ∩ Z) := by rwa [Set.inter_self]
    have hZne : (Z ∩ Z).Nonempty := (pos hZ hZ).mp hZZ
    rw [Set.inter_self] at hZne
    exact (pos hX hY).mpr (hZne.mono hZsub)

/-- The system built by `ofPositive` is indeed positive. -/
theorem NeighborhoodSystem.ofPositive_isPositive {α : Type*} (mem : Set α → Prop)
    (master : Set α) (master_nonempty : master.Nonempty) (master_mem : mem master)
    (sub_master : ∀ {X : Set α}, mem X → X ⊆ master)
    (pos : ∀ ⦃X Y : Set α⦄, mem X → mem Y → (mem (X ∩ Y) ↔ (X ∩ Y).Nonempty)) :
    (NeighborhoodSystem.ofPositive mem master master_nonempty master_mem sub_master pos).IsPositive :=
  pos

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The finite intersection `⋂_{i < n} Xᵢ` of the first `n` terms of a sequence of
neighbourhoods, defined by Scott's recursive convention (**Factoid 1.1a / 1.1b**):

* `n = 0` : the empty intersection is `Δ` (`master`);
* `n + 1` : `(⋂_{i < n} Xᵢ) ∩ Xₙ`.

(See `interUpTo_zero` and `interUpTo_succ` for the two defining equations as lemmas.) -/
def interUpTo (V : NeighborhoodSystem α) (X : ℕ → Set α) : ℕ → Set α
  | 0 => V.master
  | (n + 1) => interUpTo V X n ∩ X n

/-- **Factoid 1.1a.** The intersection of the empty sequence of neighbourhoods is `Δ`:
`⋂_{i < 0} Xᵢ = Δ`. -/
@[simp] theorem interUpTo_zero (X : ℕ → Set α) : V.interUpTo X 0 = V.master := rfl

/-- **Factoid 1.1b.** The intersection of the first `n + 1` neighbourhoods peels off the
last factor: `⋂_{i < n+1} Xᵢ = (⋂_{i < n} Xᵢ) ∩ Xₙ`. -/
@[simp] theorem interUpTo_succ (X : ℕ → Set α) (n : ℕ) :
    V.interUpTo X (n + 1) = V.interUpTo X n ∩ X n := rfl

/-- The finite intersection is contained in each of its factors: `⋂_{i < n} Xᵢ ⊆ Xⱼ` for
`j < n`. (Supporting lemma: this is what makes `⋂_{i < n} Xᵢ` a common lower bound of the
sequence, the intuition behind consistency.) -/
theorem interUpTo_subset (X : ℕ → Set α) :
    ∀ {n j : ℕ}, j < n → V.interUpTo X n ⊆ X j := by
  intro n
  induction n with
  | zero => intro j h; exact absurd h (Nat.not_lt_zero j)
  | succ n ih =>
    intro j h
    rw [interUpTo_succ]
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp h) with h' | h'
    · subst h'; exact Set.inter_subset_right
    · exact Set.inter_subset_left.trans (ih h')

/-- A finite sequence `X₀, …, Xₙ₋₁` of neighbourhoods is *consistent in* `𝒟` when it has a
common lower bound inside `𝒟`: some `Z ∈ 𝒟` contained in the intersection `⋂_{i < n} Xᵢ`
(equivalently, contained in every `Xⱼ`, `j < n`). This is Scott's notion of consistency,
generalized from pairs to finite sequences. -/
def Consistent (X : ℕ → Set α) (n : ℕ) : Prop :=
  ∃ Z, V.mem Z ∧ Z ⊆ V.interUpTo X n

/-- **Theorem 1.1c (extension of the intersection property).** Scott: "from (ii), we can
extend the intersection property to any finite sequence." If `Xᵢ ∈ 𝒟` for every `i < n`
and the sequence is consistent, then the finite intersection `⋂_{i < n} Xᵢ` is again a
neighbourhood (`∈ 𝒟`). Proved by induction on `n`; the inductive step is one application of
condition (ii). -/
theorem interUpTo_mem (X : ℕ → Set α) :
    ∀ {n : ℕ}, (∀ i, i < n → V.mem (X i)) → V.Consistent X n →
      V.mem (V.interUpTo X n) := by
  intro n
  induction n with
  | zero => intro _ _; exact V.master_mem
  | succ n ih =>
    intro hX hcons
    obtain ⟨Z, hZmem, hZsub⟩ := hcons
    have hZsub' : Z ⊆ V.interUpTo X n ∩ X n := by rwa [interUpTo_succ] at hZsub
    -- The same witness `Z` shows the length-`n` prefix is consistent.
    have hconsn : V.Consistent X n :=
      ⟨Z, hZmem, hZsub'.trans Set.inter_subset_left⟩
    have hmemn : V.mem (V.interUpTo X n) :=
      ih (fun i hi => hX i (Nat.lt_succ_of_lt hi)) hconsn
    have hXn : V.mem (X n) := hX n (Nat.lt_succ_self n)
    rw [interUpTo_succ]
    exact V.inter_mem hmemn hXn hZmem hZsub'

/-- **Theorem 1.1c (consistency characterization).** "Consequently, `X₀, …, Xₙ₋₁` is
consistent in `𝒟` iff `⋂_{i < n} Xᵢ ∈ 𝒟`." (Given `Xᵢ ∈ 𝒟` for all `i < n`.)

* `→` is the extension property `interUpTo_mem`;
* `←` is immediate: the intersection is its own common lower bound. -/
theorem consistent_iff_interUpTo_mem (X : ℕ → Set α) {n : ℕ}
    (hX : ∀ i, i < n → V.mem (X i)) :
    V.Consistent X n ↔ V.mem (V.interUpTo X n) := by
  constructor
  · exact V.interUpTo_mem X hX
  · intro h; exact ⟨V.interUpTo X n, h, Set.Subset.refl _⟩

/-- **Definition 1.6 (Scott 1981, PRG-19).** An (ideal) *element* of a neighbourhood system:
a subfamily `x ⊆ 𝒟` that is a *filter* — (i) `Δ ∈ x`, (ii) closed under intersection, (iii)
upward closed within `𝒟`. The domain is the type `Element` of all such filters, ordered by
inclusion. -/
structure Element where
  /-- `mem X` holds iff the neighbourhood `X` belongs to the filter `x`. -/
  mem : Set α → Prop
  /-- `x` is a subfamily of `𝒟`. -/
  sub : ∀ {X}, mem X → V.mem X
  /-- (i) `Δ ∈ x`. -/
  master_mem : mem V.master
  /-- (ii) `X, Y ∈ x ⟹ X ∩ Y ∈ x`. -/
  inter_mem : ∀ {X Y}, mem X → mem Y → mem (X ∩ Y)
  /-- (iii) `X ∈ x` and `X ⊆ Y ∈ 𝒟 ⟹ Y ∈ x`. -/
  up_mem : ∀ {X Y}, mem X → V.mem Y → X ⊆ Y → mem Y

/-- Two elements with the same membership predicate are equal (the remaining fields are `Prop`s). -/
theorem Element.ext {x y : V.Element} (h : ∀ X, x.mem X ↔ y.mem X) : x = y := by
  rcases x with ⟨xmem, _, _, _, _⟩
  rcases y with ⟨ymem, _, _, _, _⟩
  have hmem : xmem = ymem := funext fun X => propext (h X)
  subst hmem
  rfl

/-- A filter (`Element`) is closed under the finite intersection `⋂_{i<n} Xᵢ`: if every factor
`Xᵢ` (`i < n`) lies in the filter `x`, so does `interUpTo X n`. Used in Exercises 1.18 and 1.21.
Base case `x.master_mem`; inductive step one `x.inter_mem`. -/
theorem Element.mem_interUpTo {α : Type*} {V : NeighborhoodSystem α} (x : V.Element)
    (X : ℕ → Set α) :
    ∀ {n : ℕ}, (∀ i, i < n → x.mem (X i)) → x.mem (V.interUpTo X n) := by
  intro n
  induction n with
  | zero => intro _; exact x.master_mem
  | succ n ih =>
    intro h
    rw [interUpTo_succ]
    exact x.inter_mem (ih (fun i hi => h i (Nat.lt_succ_of_lt hi))) (h n (Nat.lt_succ_self n))

/-- Membership of the finite intersection in a filter, as a biconditional (given all factors
are neighbourhoods). `→` is upward closure along `interUpTo X n ⊆ Xᵢ` (`interUpTo_subset`); `←`
is `Element.mem_interUpTo`. -/
theorem Element.mem_interUpTo_iff {α : Type*} {V : NeighborhoodSystem α} (x : V.Element)
    (X : ℕ → Set α) {n : ℕ} (hX : ∀ i, i < n → V.mem (X i)) :
    x.mem (V.interUpTo X n) ↔ ∀ i, i < n → x.mem (X i) := by
  constructor
  · intro h i hi
    exact x.up_mem h (hX i hi) (V.interUpTo_subset X hi)
  · exact x.mem_interUpTo X

/-- Filter-inclusion order on elements (Scott's approximation order, Definition 1.8).
Named so Palomar can lock the `PartialOrder` relation without inlining it. -/
def element_le (x y : V.Element) : Prop :=
  ∀ X, x.mem X → y.mem X

/-- Reflexivity of the filter-inclusion order. Named so Palomar can lock the
`PartialOrder` instance without a generated `._proof_N`. -/
theorem element_le_refl (x : V.Element) : ∀ X, x.mem X → x.mem X :=
  fun _ h => h

/-- Transitivity of the filter-inclusion order. -/
theorem element_le_trans (x y z : V.Element)
    (hxy : ∀ X, x.mem X → y.mem X) (hyz : ∀ X, y.mem X → z.mem X) :
    ∀ X, x.mem X → z.mem X :=
  fun X h => hyz X (hxy X h)

/-- Antisymmetry of the filter-inclusion order. -/
theorem element_le_antisymm (x y : V.Element)
    (hxy : ∀ X, x.mem X → y.mem X) (hyx : ∀ X, y.mem X → x.mem X) :
    x = y :=
  @Element.ext α V x y fun X => ⟨hxy X, hyx X⟩

/-- Elements are ordered by inclusion of their membership predicates (Scott's approximation
order, Definition 1.8). -/
instance instPartialOrderElement : PartialOrder V.Element where
  le := element_le V
  le_refl := element_le_refl V
  le_trans := element_le_trans V
  le_antisymm := element_le_antisymm V

/-- The **limit family** of a sequence of neighbourhoods (Scott, the prose before Definition
1.6): `x = {Z ∈ 𝒟 ∣ Xₙ ⊆ Z for some n}` — the family of all neighbourhoods eventually reached
by `⟨Xₙ⟩`. This is the construction Scott uses to motivate the (ideal) elements of `|𝒟|`. -/
def limitFamily (X : ℕ → Set α) : Set (Set α) := {Z | V.mem Z ∧ ∃ n, X n ⊆ Z}

/-- Two sequences of neighbourhoods are **equivalent** ("each goes equally deep as the other"):
for every `Yₘ` some `Xₙ ⊆ Yₘ`, and for every `Xₙ` some `Yₘ ⊆ Xₙ`. -/
def SeqEquiv (X Y : ℕ → Set α) : Prop :=
  (∀ m, ∃ n, X n ⊆ Y m) ∧ (∀ n, ∃ m, Y m ⊆ X n)

/-- **Factoid 1.5b (Scott 1981, PRG-19).** "It is easy to prove that … the two families are
*equal* if and only if the sequences are *equivalent*." Given that every term of each sequence
is a neighbourhood, the limit families coincide exactly when the sequences are equivalent. -/
theorem limitFamily_eq_iff (X Y : ℕ → Set α)
    (hX : ∀ n, V.mem (X n)) (hY : ∀ m, V.mem (Y m)) :
    V.limitFamily X = V.limitFamily Y ↔ SeqEquiv X Y := by
  constructor
  · intro hEq
    refine ⟨fun m => ?_, fun n => ?_⟩
    · have hmem : Y m ∈ V.limitFamily Y := ⟨hY m, m, subset_rfl⟩
      rw [← hEq] at hmem
      obtain ⟨_, n, hn⟩ := hmem
      exact ⟨n, hn⟩
    · have hmem : X n ∈ V.limitFamily X := ⟨hX n, n, subset_rfl⟩
      rw [hEq] at hmem
      obtain ⟨_, m, hm⟩ := hmem
      exact ⟨m, hm⟩
  · rintro ⟨h1, h2⟩
    apply Set.ext
    intro Z
    constructor
    · rintro ⟨hZ, n, hn⟩
      obtain ⟨m, hm⟩ := h2 n
      exact ⟨hZ, m, hm.trans hn⟩
    · rintro ⟨hZ, m, hm⟩
      obtain ⟨n, hn⟩ := h1 m
      exact ⟨hZ, n, hn.trans hm⟩

/-- **Definition 1.7 (Scott 1981, PRG-19).** The *principal filter* `↑X` determined by a
neighbourhood `X ∈ 𝒟`:

`↑X = {Y ∈ 𝒟 ∣ X ⊆ Y}`.

These are Scott's *finite elements* of `|𝒟|`. The four filter conditions:

* `sub` is the first projection (`Y ∈ ↑X ⟹ Y ∈ 𝒟`);
* `master_mem` needs `X ⊆ Δ`, supplied by `V.sub_master` (Scott's `𝒟 ⊆ 𝒫(Δ)`);
* `inter_mem` uses `Set.subset_inter` (from `X ⊆ Y₁`, `X ⊆ Y₂`) with `X` itself as the
  consistency witness for `V.inter_mem`;
* `up_mem` is transitivity of `⊆`. -/
def principal {X : Set α} (hX : V.mem X) : V.Element where
  mem Y := V.mem Y ∧ X ⊆ Y
  sub h := h.1
  master_mem := ⟨V.master_mem, V.sub_master hX⟩
  inter_mem h1 h2 :=
    ⟨V.inter_mem h1.1 h2.1 hX (Set.subset_inter h1.2 h2.2), Set.subset_inter h1.2 h2.2⟩
  up_mem h hY hsub := ⟨hY, h.2.trans hsub⟩

@[simp] theorem mem_principal {X Y : Set α} (hX : V.mem X) :
    (V.principal hX).mem Y ↔ V.mem Y ∧ X ⊆ Y := Iff.rfl

/-- **Factoid 1.7a (Scott 1981, PRG-19) — inclusion-*reversing*.** "It is obvious that the
correspondence between `X` and `↑X` is one-one and inclusion *reversing*." The order on `↑`:
`↑X ⊑ ↑Y ↔ Y ⊆ X` (equivalently Scott's `X ⊆ Y ↔ ↑Y ⊑ ↑X`).

`→` tests at `Z = X` (`X ∈ ↑X` since `X ⊆ X`), reading off `Y ⊆ X` from `X ∈ ↑Y`; `←` chains
`Y ⊆ X ⊆ Z`. -/
theorem principal_le_iff {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    V.principal hX ≤ V.principal hY ↔ Y ⊆ X := by
  constructor
  · intro h
    exact (h X ⟨hX, subset_rfl⟩).2
  · intro hYX Z hZ
    exact ⟨hZ.1, hYX.trans hZ.2⟩

/-- **Factoid 1.7a (Scott 1981, PRG-19) — one-one.** The correspondence `X ↦ ↑X` is injective:
`↑X = ↑Y ⟹ X = Y`. Antisymmetry applied to `principal_le_iff` in both directions. -/
theorem principal_injective {X Y : Set α} (hX : V.mem X) (hY : V.mem Y)
    (h : V.principal hX = V.principal hY) : X = Y := by
  have hYX : Y ⊆ X := (V.principal_le_iff hX hY).mp (le_of_eq h)
  have hXY : X ⊆ Y := (V.principal_le_iff hY hX).mp (le_of_eq h.symm)
  exact Set.Subset.antisymm hXY hYX

/-- **Factoid 1.7b (Scott 1981, PRG-19).** "It is also obvious from the definitions that for each
`x ∈ |𝒟|`, `x = ⋃ {↑X ∣ X ∈ x}`." In membership form (the union over a `Set (Set α)` made
concrete): a neighbourhood `Z` is in `x` iff `Z` lies in the principal filter `↑X` of *some*
member `X` of `x`.

`→` uses `X = Z` (`Z ∈ ↑Z` as `Z ⊆ Z`); `←` is upward closure `up_mem` (`X ⊆ Z`, `Z ∈ 𝒟`). -/
theorem eq_iUnion_principal (x : V.Element) {Z : Set α} :
    x.mem Z ↔ ∃ X, ∃ hX : x.mem X, (V.principal (x.sub hX)).mem Z := by
  constructor
  · intro hZ
    exact ⟨Z, hZ, x.sub hZ, subset_rfl⟩
  · rintro ⟨X, hX, hVZ, hXZ⟩
    exact x.up_mem hX hVZ hXZ

/-- **Definition 1.8 (Scott 1981, PRG-19) — `⊥`.** The least defined element `⊥ = {Δ}`,
"read: *bottom*". It is the principal filter of the master neighbourhood `Δ`: `⊥ = ↑Δ`. -/
def bot : V.Element := V.principal V.master_mem

/-- **Definition 1.8 — `⊥ = {Δ}` literally.** Scott's `⊥` is the *singleton* `{Δ}`: a
neighbourhood `Y` belongs to `⊥` iff `Y = Δ`.

`→`: `Y ∈ ⊥ = ↑Δ` gives `Y ∈ 𝒟` and `Δ ⊆ Y`; `V.sub_master` gives the reverse `Y ⊆ Δ`, so
`Y = Δ` by antisymmetry. `←`: `Δ ∈ 𝒟` and `Δ ⊆ Δ`. -/
@[simp] theorem mem_bot {Y : Set α} : V.bot.mem Y ↔ Y = V.master := by
  constructor
  · rintro ⟨hY, hΔY⟩
    exact Set.Subset.antisymm (V.sub_master hY) hΔY
  · rintro rfl
    exact ⟨V.master_mem, subset_rfl⟩

/-- **Factoid 1.8a (Scott 1981, PRG-19).** "The element that approximates all others, `{Δ}`,
is called `⊥`": `⊥` is the least element of `|𝒟|`, `⊥ ⊑ x` for every `x`.

Given `Y ∈ ⊥`, i.e. `Y = Δ`, membership `Δ ∈ x` is filter condition (i) (`x.master_mem`). -/
theorem bot_le (x : V.Element) : V.bot ≤ x := by
  intro Y hY
  rw [mem_bot] at hY
  subst hY
  exact x.master_mem

/-- **Factoid 1.8a, packaged.** `⊥` is an `OrderBot` for the approximation order, so the `⊥`
notation refers to `{Δ}`. Constructive (`bot_le` is `[propext, Quot.sound]`). -/
instance : OrderBot V.Element where
  bot := V.bot
  bot_le := V.bot_le

/-- **Definition 1.8 (Scott 1981, PRG-19) — *total* elements.** "Elements maximal with respect
to the approximation relation are called *total elements*." `x` is total iff it is maximal: any
`y` it approximates approximates it back. This is the *predicate* only; the *existence* of total
elements above a given `x` (Exercise 1.24) is choice-dependent and out of scope here. -/
def IsTotal (x : V.Element) : Prop := ∀ y, x ≤ y → y ≤ x

/-- **Factoid 1.8b (Scott 1981, PRG-19) — "Examples 1.2–1.5 revisited".** "Any explicitly given
filter `x` is principal … the minimal `X ∈ x` tells us all we need to know." Stated honestly: if
the filter `x` has a `⊆`-minimum member `X` (one contained in every member of `x`), then `x` is
exactly the principal filter `↑X`. In a *finite* system every filter has such a minimum (the
intersection of its finitely many members, itself in `x` by closure), so every element is
principal; that finiteness step is the only classical ingredient and is left implicit here — this
constructive core captures the content.

`⊆`: any `Z ∈ x` satisfies `X ⊆ Z` by minimality, so `Z ∈ ↑X`. `⊇`: `Z ∈ ↑X` means `Z ∈ 𝒟` and
`X ⊆ Z`, so `Z ∈ x` by upward closure from `X ∈ x`. -/
theorem eq_principal_of_isMin (x : V.Element) {X : Set α} (hX : x.mem X)
    (hmin : ∀ Y, x.mem Y → X ⊆ Y) : x = V.principal (x.sub hX) := by
  apply Element.ext
  intro Z
  constructor
  · intro hZ
    exact ⟨x.sub hZ, hmin Z hZ⟩
  · rintro ⟨hZmem, hXZ⟩
    exact x.up_mem hX hZmem hXZ

end NeighborhoodSystem

/-- **Definition 1.9 (Scott 1981, PRG-19).** Two neighbourhood systems `𝒟₀` and `𝒟₁` (over possibly
*different* token types) *determine isomorphic domains* iff there is a one-one, inclusion-preserving
correspondence between `|𝒟₀|` and `|𝒟₁|`. We package "one-one + preserves inclusion (both ways)" as
mathlib's order-isomorphism `≃o`: an `OrderIso` is automatically a bijection that *reflects* as well
as preserves `⊑` (`map_rel_iff`), which is exactly Scott's requirement. -/
abbrev DomainIso {α β : Type*} (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : Type _ :=
  V₀.Element ≃o V₁.Element

/-- Scott's `𝒟₀ ≅ 𝒟₁`: the domains are isomorphic (there *exists* a `DomainIso`). -/
def Isomorphic {α β : Type*} (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : Prop :=
  Nonempty (DomainIso V₀ V₁)

@[inherit_doc] infix:25 " ≅ᴰ " => Isomorphic

/-- `≅ᴰ` is reflexive (`OrderIso.refl`). -/
theorem Isomorphic.refl {α : Type*} (V : NeighborhoodSystem α) : V ≅ᴰ V :=
  ⟨OrderIso.refl _⟩

/-- `≅ᴰ` is symmetric (`OrderIso.symm`). -/
theorem Isomorphic.symm {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (h : V₀ ≅ᴰ V₁) : V₁ ≅ᴰ V₀ :=
  h.elim fun e => ⟨e.symm⟩

/-- `≅ᴰ` is transitive (`OrderIso.trans`). -/
theorem Isomorphic.trans {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {V₂ : NeighborhoodSystem γ} (h₀ : V₀ ≅ᴰ V₁) (h₁ : V₁ ≅ᴰ V₂) : V₀ ≅ᴰ V₂ :=
  h₀.elim fun e₀ => h₁.elim fun e₁ => ⟨e₀.trans e₁⟩

end Scott1980.Neighborhood

-- Vendor 1982 — Scott1982.InfoSys (from vendor/scott1982/Scott1982/InfoSys.lean)

/-!
# Scott Information Systems

Following Dana Scott, *"Domains for Denotational Semantics"* (ICALP 1982) and the
compact presentation in Glynn Winskel, *The Formal Semantics of Programming
Languages*, Chapter 8.

Following Scott's **Definition 2.1**, an information system is a structure
`(P, Δ, Con, ⊢)` where

* `P` is a set of *data objects* / *propositions* (our token type `α`);
* `Δ ∈ P` is a distinguished *least informative* object (here the field `bot`);
* `Con` is a set of finite subsets of `P`, the *consistent* sets; and
* `⊢` (entailment, here `Ent`) relates a finite set to a token it forces.

Scott's six axioms (Def. 2.1) are, for finite `u, v ⊆ P` and `X ∈ P`:

* (i)   `u ∈ Con` whenever `u ⊆ v ∈ Con`              — `con_subset`
* (ii)  `{X} ∈ Con`                                    — `con_sing`
* (iii) `u ∪ {X} ∈ Con` whenever `u ⊢ X`               — `ent_con`
* (iv)  `u ⊢ Δ`                                         — `ent_bot`
* (v)   `u ⊢ X` whenever `X ∈ u`                        — `ent_refl`
* (vi)  if `v ⊢ Y` for all `Y ∈ u` and `u ⊢ X` then `v ⊢ X` — `ent_trans`

The **domain** determined by an information system is the poset of its *elements*
(a.k.a. *ideals*): sets of tokens that are consistent on every finite subset and
closed under entailment, ordered by inclusion. This file sets up the structure, the
notion of element, and the partial order; later files build the function, product,
and sum spaces.

This is the **1982** presentation; the development is kept choice-free (constructive),
matching Scott's emphasis on the constructive nature of the definitions.
-/

namespace Scott1982

universe u

/-- A Scott information system on a type of tokens `α`, following Scott's Definition 2.1
in *"Domains for Denotational Semantics"* (ICALP 1982).

`DecidableEq α` is required so that finite token sets support union (`X ∪ {a}`) and the
other `Finset` operations the axioms mention. -/
structure InfoSys (α : Type u) [DecidableEq α] where
  /-- The distinguished least-informative object `Δ`. -/
  bot : α
  /-- The consistent finite sets of tokens. -/
  Con : Set (Finset α)
  /-- Entailment: `Ent u a` means the consistent set `u` forces the token `a`. -/
  Ent : Finset α → α → Prop
  /-- (i) Consistency is downward closed under `⊆`. -/
  con_subset : ∀ {u v : Finset α}, u ∈ Con → v ⊆ u → v ∈ Con
  /-- (ii) Every singleton is consistent. -/
  con_sing : ∀ a : α, {a} ∈ Con
  /-- (iii) A set entailing `a` stays consistent when `a` is added. Scott writes this as
  `u ∪ {a} ∈ Con`; we use the definitionally identical `insert a u`, because mathlib's
  `Finset` union instance (unlike `insert`) depends on `Classical.choice`, which would
  break the constructive development. -/
  ent_con : ∀ {u : Finset α} {a : α}, Ent u a → insert a u ∈ Con
  /-- (iv) The least token `Δ` is entailed by every consistent set. -/
  ent_bot : ∀ {u : Finset α}, u ∈ Con → Ent u bot
  /-- (v) Entailment is reflexive on members of a consistent set. -/
  ent_refl : ∀ {u : Finset α} {a : α}, u ∈ Con → a ∈ u → Ent u a
  /-- (vi) Entailment is transitive (cut): if a consistent `v` entails every member of a
  consistent `u`, and `u ⊢ c`, then `v ⊢ c`. -/
  ent_trans : ∀ {u v : Finset α} {c : α},
    v ∈ Con → u ∈ Con → (∀ y ∈ u, Ent v y) → Ent u c → Ent v c

namespace InfoSys

variable {α : Type u} [DecidableEq α] (sys : InfoSys α)

/-- An *element* (ideal) of the domain: a set of tokens that is consistent on every
finite subset and closed under entailment. -/
structure Element where
  /-- The underlying set of tokens. -/
  carrier : Set α
  /-- Every finite subset of the element is consistent. -/
  consistent : ∀ Y : Finset α, (Y : Set α) ⊆ carrier → Y ∈ sys.Con
  /-- The element is closed under entailment. -/
  closed : ∀ (Y : Finset α) (a : α), (Y : Set α) ⊆ carrier → sys.Ent Y a → a ∈ carrier

/-- Extensional equality of elements. -/
theorem Element.ext {x y : sys.Element} (h : x.carrier = y.carrier) : x = y := by
  cases x
  cases y
  subst h
  rfl

/-- Reflexivity of the carrier-inclusion order. -/
theorem element_le_refl (x : sys.Element) : x.carrier ⊆ x.carrier :=
  Set.Subset.refl _

/-- Transitivity of the carrier-inclusion order. -/
theorem element_le_trans (x y z : sys.Element)
    (hxy : x.carrier ⊆ y.carrier) (hyz : y.carrier ⊆ z.carrier) :
    x.carrier ⊆ z.carrier :=
  Set.Subset.trans hxy hyz

/-- Antisymmetry of the carrier-inclusion order. -/
theorem element_le_antisymm (x y : sys.Element)
    (hxy : x.carrier ⊆ y.carrier) (hyx : y.carrier ⊆ x.carrier) :
    x = y :=
  Element.ext sys (Set.Subset.antisymm hxy hyx)

/-- Elements are ordered by inclusion of their carriers; this is the Scott ordering. -/
instance instPartialOrderElement : PartialOrder sys.Element where
  le x y := x.carrier ⊆ y.carrier
  le_refl := element_le_refl sys
  le_trans := element_le_trans sys
  le_antisymm := element_le_antisymm sys

/-- Empty set is consistent (subset of any singleton). -/
theorem con_empty : (∅ : Finset α) ∈ sys.Con :=
  sys.con_subset (sys.con_sing sys.bot) (Finset.empty_subset _)

end InfoSys

end Scott1982

-- Vendor 1982 — Scott1982.Constructive (from vendor/scott1982/Scott1982/Constructive.lean)

/-!
# A choice-free `Finset` prelude

One of the project's goals (Goal 3) is to certify that the *information-system*
presentation of Scott domains can be developed in a **purely constructive** fragment of
Lean: every result must have a `#print axioms` footprint contained in
`[propext, Quot.sound]`, with **no `Classical.choice`** and no use of the law of excluded
middle.

This is harder than it looks, because several of mathlib's `Finset` *operations* and even
a few basic *lemmas* transitively depend on `Classical.choice` (through the
`Multiset.dedup` / quotient machinery), in version `v4.30.0`:

* tainted operations: `(· ∪ ·)`, `Finset.image`, `(· ×ˢ ·)`, `Finset.biUnion`, `(· \ ·)`,
  and mathlib's `Finset.decidableEq` (via `Multiset` quotients);
* tainted lemmas: e.g. `Finset.insert_comm`, `Finset.singleton_subset_iff`;
* tainted *tactics*: `tauto`, `aesop` (they close goals via classical reasoning).

By contrast the following are choice-free and form our working toolkit: `insert`,
`(· ∩ ·)`, `Finset.filter`, `Finset.fold`, `Multiset.foldr`, the membership/subset lemmas
(`Finset.mem_insert`, `Finset.mem_singleton`, `Finset.subset_iff`, `Finset.mem_coe`,
`Finset.coe_subset`, `Finset.mem_inter`, `Finset.ext`), set-level unions/intersections,
and explicit term-mode/`rintro`/`constructor` proofs.

This file provides the finite-set operations the development needs but mathlib only
offers in choice-tainted form: a **binary union of `Finset`s**, built choice-free by
folding `insert`, and a **decidable equality** for `Finset` via subset antisymmetry.
Every declaration here is audited to depend only on
`[propext, Quot.sound]`.
-/

namespace Scott1982.Constructive

variable {α : Type*} [DecidableEq α]

/-- Choice-free commutativity of `insert` (mathlib's `Finset.insert_comm` is choice-tainted).
Needed to fold `insert` over a `Multiset`. -/
theorem insert_comm' (a b : α) (s : Finset α) :
    insert a (insert b s) = insert b (insert a s) := by
  ext x
  simp only [Finset.mem_insert]
  constructor
  · rintro (h | h | h)
    exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]
  · rintro (h | h | h)
    exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]

instance instLeftCommutativeInsert :
    LeftCommutative (insert : α → Finset α → Finset α) := ⟨insert_comm'⟩

/-- Choice-free binary union of finite sets, obtained by folding `insert` over the second
argument's underlying multiset. Definitionally equal in content to `u ∪ v`, but — unlike
mathlib's `(· ∪ ·)` — free of any `Classical.choice` dependency. -/
def funion (u v : Finset α) : Finset α := Multiset.foldr insert u v.1

@[inherit_doc] infixl:65 " ∪' " => funion

theorem mem_foldr_insert (a : α) (u : Finset α) (s : Multiset α) :
    a ∈ Multiset.foldr insert u s ↔ a ∈ u ∨ a ∈ s := by
  refine Multiset.induction_on s ?_ ?_
  · simp
  · intro b t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (h | h | h)
      exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]
    · rintro (h | h | h)
      exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]

@[simp] theorem mem_funion {a : α} {u v : Finset α} :
    a ∈ u ∪' v ↔ a ∈ u ∨ a ∈ v := mem_foldr_insert a u v.1

/-- The coercion of `u ∪' v` to a `Set` is the (choice-free) set union of the coercions. -/
theorem coe_funion (u v : Finset α) :
    (↑(u ∪' v) : Set α) = (↑u : Set α) ∪ ↑v := by
  ext x
  simp only [Set.mem_union, Finset.mem_coe, mem_funion]

theorem subset_funion_left (u v : Finset α) : u ⊆ u ∪' v := fun _ hx => mem_funion.2 (Or.inl hx)

theorem subset_funion_right (u v : Finset α) : v ⊆ u ∪' v := fun _ hx => mem_funion.2 (Or.inr hx)

@[simp] theorem funion_empty_right (u : Finset α) : u ∪' (∅ : Finset α) = u := by
  ext x
  simp only [mem_funion, Finset.notMem_empty, or_false]

/-- Universal property of the union: `u ∪' v ⊆ w` iff both `u ⊆ w` and `v ⊆ w`. -/
theorem funion_subset_iff {u v w : Finset α} : u ∪' v ⊆ w ↔ u ⊆ w ∧ v ⊆ w := by
  constructor
  · intro h
    exact ⟨fun x hx => h (subset_funion_left u v hx),
           fun x hx => h (subset_funion_right u v hx)⟩
  · rintro ⟨hu, hv⟩ x hx
    rcases mem_funion.1 hx with h | h
    exacts [hu h, hv h]

omit [DecidableEq α] in
/-- If mutual subset holds, the finsets are equal. -/
theorem decidableEq_finset_eq_of_subset (s t : Finset α) (h : s ⊆ t ∧ t ⊆ s) : s = t :=
  Finset.Subset.antisymm h.1 h.2

omit [DecidableEq α] in
/-- Mutual subset is required for finset equality in this decidable instance. -/
theorem decidableEq_finset_false_of_ne (s t : Finset α) (h : ¬(s ⊆ t ∧ t ⊆ s)) (heq : s = t) :
    False := by
  subst heq
  exact h ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩

/-- Choice-free decidable equality for `Finset`.
mathlib's `Finset.decidableEq` goes through `Multiset` quotients and pulls
`Classical.choice`; this version uses only decidable membership and subset. -/
def decidableEq_finset {α : Type*} [DecidableEq α] : DecidableEq (Finset α) :=
  fun s t =>
    if h : s ⊆ t ∧ t ⊆ s then
      isTrue (decidableEq_finset_eq_of_subset s t h)
    else
      isFalse (decidableEq_finset_false_of_ne s t h)

end Scott1982.Constructive

-- Vendor 1982 — Scott1982.Definition22 (from vendor/scott1982/Scott1982/Definition22.lean)

/-!
# Definition 2.2 — set-level entailment

**Scott 1982, Definition 2.2.** For `u, v ∈ Con` we write `u ⊢ v` to mean that
`u ⊢ X` for all `X ∈ v`.
-/

namespace Scott1982

namespace InfoSys

universe u

variable {α : Type u} [DecidableEq α] (sys : InfoSys α)

/-- **Definition 2.2 (Scott 1982).** Set-level entailment: `EntSet u v` means
`u ⊢ X` for every `X ∈ v`. -/
def EntSet (u v : Finset α) : Prop := ∀ X ∈ v, sys.Ent u X

theorem entSet_empty (u : Finset α) : sys.EntSet u (∅ : Finset α) := by
  intro X hX
  exact False.elim (Finset.notMem_empty X hX)

theorem entSet_singleton {u : Finset α} {X : α} :
    sys.EntSet u {X} ↔ sys.Ent u X := by
  constructor
  · intro h
    exact h X (Finset.mem_singleton_self X)
  · intro h Y hY
    rw [Finset.mem_singleton] at hY
    subst hY
    exact h

end InfoSys

end Scott1982

-- Vendor 1982 — Scott1982.Proposition23 (from vendor/scott1982/Scott1982/Proposition23.lean)

/-!
# Proposition 2.3 — elementary properties of set-level entailment

**Scott 1982, Proposition 2.3.** For all `u, v, w, u', v' ∈ Con`:
(i) `∅ ⊢ {Δ}`; (ii) `u ⊢ v ⇒ u ∪ v ∈ Con`; (iii) `u ⊢ u`;
(iv) transitivity; (v) monotonicity; (vi) `u ⊢ v ∧ u ⊢ v' ⇒ u ⊢ v ∪ v'`.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- `u ∪' insert a t = insert a (u ∪' t)`. -/
theorem funion_insert (u : Finset α) (a : α) (t : Finset α) :
    u ∪' insert a t = insert a (u ∪' t) := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with hu | hins
    · exact Finset.mem_insert_of_mem (mem_funion.mpr (Or.inl hu))
    · rcases Finset.mem_insert.mp hins with ha | ht
      · exact Finset.mem_insert.mpr (Or.inl ha)
      · exact Finset.mem_insert_of_mem (mem_funion.mpr (Or.inr ht))
  · intro hx
    rcases Finset.mem_insert.mp hx with ha | h
    · exact mem_funion.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl ha)))
    · rcases mem_funion.mp h with hu | ht
      · exact mem_funion.mpr (Or.inl hu)
      · exact mem_funion.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr ht)))

/-- **Proposition 2.3(i).** `∅ ⊢ {Δ}`. -/
theorem proposition_2_3_i : sys.EntSet ∅ ({sys.bot} : Finset α) := by
  intro X hX
  rw [Finset.mem_singleton] at hX
  subst hX
  exact sys.ent_bot sys.con_empty

/-- **Proposition 2.3(iii).** `u ⊢ u`. -/
theorem proposition_2_3_iii {u : Finset α} (hu : u ∈ sys.Con) : sys.EntSet u u :=
  fun _X hX => sys.ent_refl hu hX

/-- **Proposition 2.3(iv).** Transitivity of `EntSet`. -/
theorem proposition_2_3_iv {u v w : Finset α}
    (hu : u ∈ sys.Con) (hv : v ∈ sys.Con)
    (huv : sys.EntSet u v) (hvw : sys.EntSet v w) : sys.EntSet u w :=
  fun X hX => sys.ent_trans hu hv huv (hvw X hX)

/-- **Proposition 2.3(v).** Monotonicity: `u ⊆ u'`, `u ⊢ v`, `v' ⊆ v` ⇒ `u' ⊢ v'`. -/
theorem proposition_2_3_v {u u' v v' : Finset α}
    (hu : u ∈ sys.Con) (hu' : u' ∈ sys.Con)
    (hsubu : u ⊆ u') (huv : sys.EntSet u v) (hsubv : v' ⊆ v) :
    sys.EntSet u' v' := by
  intro X hX
  have hEnt : sys.Ent u X := huv X (hsubv hX)
  refine sys.ent_trans hu' hu ?_ hEnt
  intro y hy
  exact sys.ent_refl hu' (hsubu hy)

/-- **Proposition 2.3(vi).** `u ⊢ v` and `u ⊢ v'` imply `u ⊢ v ∪' v'`. -/
theorem proposition_2_3_vi {u v v' : Finset α}
    (huv : sys.EntSet u v) (huv' : sys.EntSet u v') : sys.EntSet u (v ∪' v') := by
  intro X hX
  rcases mem_funion.mp hX with h | h
  · exact huv X h
  · exact huv' X h

/-- **Proposition 2.3(ii).** `u ⊢ v` implies `u ∪' v ∈ Con`. -/
theorem proposition_2_3_ii {u v : Finset α} (hu : u ∈ sys.Con) (h : sys.EntSet u v) :
    u ∪' v ∈ sys.Con := by
  have : ∀ s : Finset α, (∀ x ∈ s, x ∈ v) → u ∪' s ∈ sys.Con := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      -- foldr insert u 0 = u
      simpa [funion_empty_right] using hu
    · intro a t _ha ih hmem
      have hEnt_u_a : sys.Ent u a := h a (hmem a (Finset.mem_insert_self a t))
      have hut : u ∪' t ∈ sys.Con := ih fun x hx => hmem x (Finset.mem_insert_of_mem hx)
      have hEnt : sys.Ent (u ∪' t) a :=
        sys.ent_trans hut hu (fun y hy => sys.ent_refl hut (subset_funion_left u t hy))
          hEnt_u_a
      have hins : insert a (u ∪' t) ∈ sys.Con := sys.ent_con hEnt
      simpa [funion_insert] using hins
  exact this v fun _ hx => hx

end InfoSys

end Scott1982

-- Vendor 1982 — Scott1982.Factoid35 (from vendor/scott1982/Scott1982/Factoid35.lean)

/-!
# Factoid 3.5 — finite elements as entailment closures

**Factoid 3.5 (inventory).** For `u ∈ Con`, the closure
`ū = {X ∣ u ⊢ X}` is an element of `|A|` (a *finite element*).
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- **Factoid 3.5.** Entailment closure of a consistent set. -/
def closure (u : Finset α) (hu : u ∈ sys.Con) : sys.Element where
  carrier := {X | sys.Ent u X}
  consistent := by
    intro Y hY
    have hEnt : sys.EntSet u Y := fun X hX => hY (Finset.mem_coe.2 hX)
    exact sys.con_subset (proposition_2_3_ii sys hu hEnt) (subset_funion_right _ _)
  closed := by
    intro Y a hY hEnt
    have hYcon : Y ∈ sys.Con := by
      have hEntY : sys.EntSet u Y := fun X hX => hY (Finset.mem_coe.2 hX)
      exact sys.con_subset (proposition_2_3_ii sys hu hEntY) (subset_funion_right _ _)
    exact sys.ent_trans hu hYcon (fun y hy => hY (Finset.mem_coe.2 hy)) hEnt

theorem mem_closure_iff {u : Finset α} (hu : u ∈ sys.Con) {X : α} :
    X ∈ (sys.closure u hu).carrier ↔ sys.Ent u X := Iff.rfl

/-- `u ⊆ ū`. -/
theorem subset_closure {u : Finset α} (hu : u ∈ sys.Con) :
    ↑u ⊆ (sys.closure u hu).carrier :=
  fun _ hX => sys.ent_refl hu (Finset.mem_coe.1 hX)

end InfoSys

end Scott1982

-- Vendor 1982 — Scott1982.Approximable (from vendor/scott1982/Scott1982/Approximable.lean)

/-!
# Approximable mappings — Definitions 5.1 and 5.2

Adapted from the PRG-19 approximable-map pattern, rewritten for Scott 1982
information systems (relations on `Con × Con`).
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

/-- **Definition 5.1 (Scott 1982).** Approximable mapping between information systems. -/
structure ApproximableMap (A : InfoSys α) (B : InfoSys β) where
  rel : Finset α → Finset β → Prop
  rel_dom : ∀ {u v}, rel u v → u ∈ A.Con
  rel_cod : ∀ {u v}, rel u v → v ∈ B.Con
  empty_rel : rel ∅ ∅
  union_right : ∀ {u v v'}, rel u v → rel u v' → rel u (v ∪' v')
  mono : ∀ {u u' v v'},
    rel u v → A.EntSet u' u → B.EntSet v v' → u' ∈ A.Con → v' ∈ B.Con → rel u' v'

namespace ApproximableMap

variable {A : InfoSys α} {B : InfoSys β}

theorem ext {f g : ApproximableMap A B} (h : ∀ u v, f.rel u v ↔ g.rel u v) : f = g := by
  obtain ⟨rf, _, _, _, _, _⟩ := f
  obtain ⟨rg, _, _, _, _, _⟩ := g
  have : rf = rg := by
    funext u v
    exact propext (h u v)
  subst this
  rfl

private theorem Approximable_singleton_funion_eq (a : β) (s : Finset β) :
    ({a} : Finset β) ∪' s = insert a s := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with ha | hs
    · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp ha))
    · exact Finset.mem_insert_of_mem hs
  · intro hx
    rcases Finset.mem_insert.mp hx with ha | hs
    · exact mem_funion.mpr (Or.inl (Finset.mem_singleton.mpr ha))
    · exact mem_funion.mpr (Or.inr hs)

/-- Given `↑Y ⊆ f(x).carrier`, produce `u ⊆ x` with `u f Y`. -/
theorem exists_rel_of_subset_image (f : ApproximableMap A B) (x : A.Element)
    (Y : Finset β)
    (hY : ↑Y ⊆ ({Y : β | ∃ u : Finset α, ↑u ⊆ x.carrier ∧ f.rel u {Y}} : Set β)) :
    ∃ u : Finset α, ↑u ⊆ x.carrier ∧ f.rel u Y := by
  induction Y using Finset.induction_on with
  | empty =>
    refine ⟨∅, ?_, ?_⟩
    · intro a ha
      exact False.elim (Finset.notMem_empty a (Finset.mem_coe.1 ha))
    · exact f.mono f.empty_rel (A.entSet_empty ∅) (B.entSet_empty ∅) A.con_empty B.con_empty
  | insert a s _ha ih =>
    have ha' : ∃ u : Finset α, ↑u ⊆ x.carrier ∧ f.rel u {a} :=
      hY (Finset.mem_coe.2 (Finset.mem_insert_self a s))
    have hs' :
        ↑s ⊆ ({Y : β | ∃ u : Finset α, ↑u ⊆ x.carrier ∧ f.rel u {Y}} : Set β) := by
      intro b hb
      exact hY (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hb)))
    obtain ⟨ua, hua, hrela⟩ := ha'
    obtain ⟨us, hus, hrels⟩ := ih hs'
    refine ⟨ua ∪' us, ?_, ?_⟩
    · intro z hz
      have hz' : z ∈ ua ∪' us := Finset.mem_coe.1 hz
      rcases mem_funion.mp hz' with h | h
      · exact hua (Finset.mem_coe.2 h)
      · exact hus (Finset.mem_coe.2 h)
    · have hUcon : ua ∪' us ∈ A.Con :=
        x.consistent (ua ∪' us) fun z hz => by
          rcases mem_funion.mp hz with h | h
          · exact hua (Finset.mem_coe.2 h)
          · exact hus (Finset.mem_coe.2 h)
      have hEnt_ua : A.EntSet (ua ∪' us) ua :=
        fun y hy => A.ent_refl hUcon (subset_funion_left ua us hy)
      have hEnt_us : A.EntSet (ua ∪' us) us :=
        fun y hy => A.ent_refl hUcon (subset_funion_right ua us hy)
      have h1 : f.rel (ua ∪' us) {a} :=
        f.mono hrela hEnt_ua
          (fun z hz => by
            rw [Finset.mem_singleton] at hz
            rw [hz]
            exact B.ent_refl (B.con_sing a) (Finset.mem_singleton_self a))
          hUcon (B.con_sing a)
      have h2 : f.rel (ua ∪' us) s :=
        f.mono hrels hEnt_us (proposition_2_3_iii B (f.rel_cod hrels))
          hUcon (f.rel_cod hrels)
      have hU : f.rel (ua ∪' us) ({a} ∪' s) := f.union_right h1 h2
      simpa [Approximable_singleton_funion_eq] using hU

/-- **Definition 5.2.** Image of an element under an approximable mapping. -/
def toElement (f : ApproximableMap A B) (x : A.Element) : B.Element where
  carrier := {Y | ∃ u : Finset α, ↑u ⊆ x.carrier ∧ f.rel u {Y}}
  consistent := by
    intro Y hY
    obtain ⟨u, _, hrel⟩ := exists_rel_of_subset_image f x Y hY
    exact f.rel_cod hrel
  closed := by
    intro Y a hY hEnt
    obtain ⟨u, hu, hrel⟩ := exists_rel_of_subset_image f x Y hY
    have harel : f.rel u {a} :=
      f.mono hrel (proposition_2_3_iii A (f.rel_dom hrel))
        (fun z hz => by
          rw [Finset.mem_singleton] at hz
          rw [hz]
          exact hEnt)
        (f.rel_dom hrel) (B.con_sing a)
    exact ⟨u, hu, harel⟩

@[simp] theorem mem_toElement (f : ApproximableMap A B) (x : A.Element) {Y : β} :
    Y ∈ (f.toElement x).carrier ↔ ∃ u : Finset α, ↑u ⊆ x.carrier ∧ f.rel u {Y} :=
  Iff.rfl

theorem toElement_mono (f : ApproximableMap A B) {x y : A.Element} (hxy : x ≤ y) :
    f.toElement x ≤ f.toElement y := by
  intro Y ⟨u, hu, hrel⟩
  exact ⟨u, fun z hz => hxy (hu hz), hrel⟩

end ApproximableMap

end InfoSys

end Scott1982

-- Vendor 1982 — Scott1982.Factoid36 (from vendor/scott1982/Scott1982/Factoid36.lean)

/-!
# Factoid 3.6 — every element is the directed union of its finite approximations

**Factoid 3.6 (Scott §3 / inventory).** For every element `x ∈ |A|`,
`x` equals the union of all `ū` with `u ∈ Con` and `u ⊆ x`.
Intuitively: every element is the limit of its finite approximations. The union is directed.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- If `w` entails every member of `u`, then `ū ⊆ w̄`. -/
theorem closure_le_of_entSet {u w : Finset α} (hu : u ∈ sys.Con) (hw : w ∈ sys.Con)
    (h : sys.EntSet w u) : sys.closure u hu ≤ sys.closure w hw := by
  intro a ha
  exact sys.ent_trans hw hu h ha

/-- Monotonicity of closure under inclusion of consistent sets. -/
theorem closure_le_of_subset {u w : Finset α} (hu : u ∈ sys.Con) (hw : w ∈ sys.Con)
    (hsub : u ⊆ w) : sys.closure u hu ≤ sys.closure w hw :=
  sys.closure_le_of_entSet hu hw fun _ hy => sys.ent_refl hw (hsub hy)

/-- Finite approximations below `x` really do approximate `x`. -/
theorem closure_le_element (x : sys.Element) {u : Finset α} (hu : u ∈ sys.Con)
    (hsub : ↑u ⊆ x.carrier) : sys.closure u hu ≤ x := by
  intro a ha
  exact x.closed u a hsub ha

/-- The set-theoretic union of all finite approximations of `x`. -/
def approxUnion (x : sys.Element) : Set α :=
  {a | ∃ (u : Finset α) (hu : u ∈ sys.Con),
    ↑u ⊆ x.carrier ∧ a ∈ (sys.closure u hu).carrier}

/-- **Factoid 3.6.** Membership in `x` iff membership in some finite approximation `ū ⊆ x`. -/
theorem mem_element_iff_mem_closure (x : sys.Element) (a : α) :
    a ∈ x.carrier ↔ a ∈ sys.approxUnion x := by
  constructor
  · intro ha
    refine ⟨{a}, sys.con_sing a, ?_, ?_⟩
    · intro b hb
      have hb' : b ∈ ({a} : Finset α) := Finset.mem_coe.1 hb
      rw [Finset.mem_singleton] at hb'
      subst hb'
      exact ha
    · exact sys.ent_refl (sys.con_sing a) (Finset.mem_singleton_self a)
  · rintro ⟨u, hu, hsub, ha⟩
    exact x.closed u a hsub ha

/-- **Factoid 3.6.** Carrier form: `x = ⋃{ū | u ∈ Con, u ⊆ x}`. -/
theorem element_eq_approxUnion (x : sys.Element) : x.carrier = sys.approxUnion x := by
  ext a
  exact sys.mem_element_iff_mem_closure x a

/-- The family of finite approximations to `x` is directed under `≤`. -/
theorem closures_directed (x : sys.Element) {u v : Finset α}
    (hu : u ∈ sys.Con) (hv : v ∈ sys.Con)
    (huX : ↑u ⊆ x.carrier) (hvX : ↑v ⊆ x.carrier) :
    ∃ (w : Finset α) (hw : w ∈ sys.Con),
      ↑w ⊆ x.carrier ∧
        sys.closure u hu ≤ sys.closure w hw ∧
        sys.closure v hv ≤ sys.closure w hw := by
  let w := u ∪' v
  have hwX : ↑w ⊆ x.carrier := by
    intro a ha
    rcases mem_funion.1 (Finset.mem_coe.1 ha) with h | h
    · exact huX (Finset.mem_coe.2 h)
    · exact hvX (Finset.mem_coe.2 h)
  have hw : w ∈ sys.Con := x.consistent w hwX
  refine ⟨w, hw, hwX, ?_, ?_⟩
  · exact sys.closure_le_of_subset hu hw (subset_funion_left u v)
  · exact sys.closure_le_of_subset hv hw (subset_funion_right u v)

end InfoSys

end Scott1982

-- Vendor 1982 — Scott1982.Factoid32 (from vendor/scott1982/Scott1982/Factoid32.lean)

/-!
# Factoid 3.2 — every element contains Δ

**Factoid 3.2 (inventory).** Scott remarks after Def 3.1 that every element contains `Δ`,
because the least informative proposition is true of all elements.
-/

namespace Scott1982

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- **Factoid 3.2.** Every element contains `Δ`. -/
theorem factoid_3_2 (x : sys.Element) : sys.bot ∈ x.carrier := by
  have hempty : (↑(∅ : Finset α) : Set α) ⊆ x.carrier := by
    intro a ha
    exact False.elim (Finset.notMem_empty a (Finset.mem_coe.1 ha))
  have hEnt : sys.Ent ∅ sys.bot := sys.ent_bot sys.con_empty
  exact x.closed ∅ sys.bot hempty hEnt

end InfoSys

end Scott1982

-- Vendor 1982 — Scott1982.Factoid33 (from vendor/scott1982/Scott1982/Factoid33.lean)

/-!
# Factoid 3.3 — the bottom element ⊥

**Factoid 3.3 (inventory).** Scott defines
`⊥_A = {X ∈ D_A ∣ {Δ_A} ⊢_A X}` and notes it is the least element of `|A|`.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- **Factoid 3.3.** The bottom element `⊥ = {X ∣ {Δ} ⊢ X}`. -/
def botElement : sys.Element where
  carrier := {X | sys.Ent {sys.bot} X}
  consistent := by
    intro Y hY
    have hbot : ({sys.bot} : Finset α) ∈ sys.Con := sys.con_sing sys.bot
    have hEnt : sys.EntSet {sys.bot} Y := fun X hX => hY (Finset.mem_coe.2 hX)
    have hunion : {sys.bot} ∪' Y ∈ sys.Con := proposition_2_3_ii sys hbot hEnt
    exact sys.con_subset hunion (subset_funion_right _ _)
  closed := by
    intro Y a hY hEnt
    have hbot : ({sys.bot} : Finset α) ∈ sys.Con := sys.con_sing sys.bot
    have hYcon : Y ∈ sys.Con := by
      have hEntY : sys.EntSet {sys.bot} Y := fun X hX => hY (Finset.mem_coe.2 hX)
      exact sys.con_subset (proposition_2_3_ii sys hbot hEntY) (subset_funion_right _ _)
    exact sys.ent_trans hbot hYcon (fun y hy => hY (Finset.mem_coe.2 hy)) hEnt

/-- `⊥` is least. -/
theorem botElement_le (x : sys.Element) : sys.botElement ≤ x := by
  intro a ha
  have hsub : (↑({sys.bot} : Finset α) : Set α) ⊆ x.carrier := by
    intro b hb
    have hb' : b ∈ ({sys.bot} : Finset α) := Finset.mem_coe.1 hb
    rw [Finset.mem_singleton] at hb'
    subst hb'
    exact factoid_3_2 sys x
  exact x.closed {sys.bot} a hsub ha

end InfoSys

end Scott1982

-- Vendor 1982 — Scott1982.Factoid41 (from vendor/scott1982/Scott1982/Factoid41.lean)

/-!
# Factoid 4.1 — `|A|` is an inf-semilattice under intersection

**Factoid 4.1 (Scott §4 / inventory).** The intersection of two elements is again an
element, so `|A|` is an inf-semilattice under `∩`. In particular
`x ⊆ y ↔ x ∩ y = x`. Scott also records that `∩` is idempotent, commutative, and
associative, and that `⊥` is a zero for `∩`.
-/

namespace Scott1982

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- **Factoid 4.1.** Binary meet of elements is set-theoretic intersection. -/
def inf (x y : sys.Element) : sys.Element where
  carrier := x.carrier ∩ y.carrier
  consistent := fun Y hY =>
    x.consistent Y (Set.Subset.trans hY Set.inter_subset_left)
  closed := fun Y a hY hEnt =>
    ⟨x.closed Y a (Set.Subset.trans hY Set.inter_subset_left) hEnt,
     y.closed Y a (Set.Subset.trans hY Set.inter_subset_right) hEnt⟩

theorem inf_le_left (x y : sys.Element) : sys.inf x y ≤ x :=
  Set.inter_subset_left

theorem inf_le_right (x y : sys.Element) : sys.inf x y ≤ y :=
  Set.inter_subset_right

theorem le_inf {x y z : sys.Element} (hxy : x ≤ y) (hxz : x ≤ z) : x ≤ sys.inf y z :=
  fun _ ha => ⟨hxy ha, hxz ha⟩

/-- Meet is the greatest lower bound. -/
theorem inf_le_iff {x y z : sys.Element} : z ≤ sys.inf x y ↔ z ≤ x ∧ z ≤ y :=
  ⟨fun h => ⟨le_trans h (sys.inf_le_left x y), le_trans h (sys.inf_le_right x y)⟩,
   fun ⟨hx, hy⟩ => sys.le_inf hx hy⟩

/-- **Factoid 4.1.** `x ⊆ y` iff `x ∩ y = x`. -/
theorem le_iff_inf_eq {x y : sys.Element} : x ≤ y ↔ sys.inf x y = x := by
  constructor
  · intro h
    refine le_antisymm (sys.inf_le_left x y) ?_
    intro a ha
    exact ⟨ha, h ha⟩
  · intro heq
    have hc : x.carrier = x.carrier ∩ y.carrier :=
      Eq.symm (congrArg Element.carrier heq)
    intro a ha
    exact ((Set.ext_iff.1 hc a).1 ha).2

theorem inf_idem (x : sys.Element) : sys.inf x x = x :=
  (sys.le_iff_inf_eq (y := x)).1 (le_refl x)

theorem inf_comm (x y : sys.Element) : sys.inf x y = sys.inf y x := by
  refine le_antisymm ?_ ?_
  · exact sys.le_inf (sys.inf_le_right x y) (sys.inf_le_left x y)
  · exact sys.le_inf (sys.inf_le_right y x) (sys.inf_le_left y x)

theorem inf_assoc (x y z : sys.Element) : sys.inf (sys.inf x y) z = sys.inf x (sys.inf y z) := by
  refine le_antisymm ?_ ?_
  · refine sys.le_inf ?_ (sys.le_inf ?_ ?_)
    · exact le_trans (sys.inf_le_left _ _) (sys.inf_le_left _ _)
    · exact le_trans (sys.inf_le_left _ _) (sys.inf_le_right _ _)
    · exact sys.inf_le_right _ _
  · refine sys.le_inf (sys.le_inf ?_ ?_) ?_
    · exact sys.inf_le_left _ _
    · exact le_trans (sys.inf_le_right _ _) (sys.inf_le_left _ _)
    · exact le_trans (sys.inf_le_right _ _) (sys.inf_le_right _ _)

theorem inf_mono {x₁ x₂ y₁ y₂ : sys.Element} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    sys.inf x₁ y₁ ≤ sys.inf x₂ y₂ :=
  sys.le_inf (le_trans (sys.inf_le_left _ _) hx) (le_trans (sys.inf_le_right _ _) hy)

/-- `⊥` is a zero for meet: `⊥ ∩ x = ⊥`. -/
theorem botElement_inf (x : sys.Element) : sys.inf sys.botElement x = sys.botElement :=
  (sys.le_iff_inf_eq (x := sys.botElement) (y := x)).1 (sys.botElement_le x)

theorem inf_botElement (x : sys.Element) : sys.inf x sys.botElement = sys.botElement := by
  rw [sys.inf_comm, sys.botElement_inf]

end InfoSys

end Scott1982

-- Vendor 1982 — Scott1982.Factoid42 (from vendor/scott1982/Scott1982/Factoid42.lean)

/-!
# Factoid 4.2 — conditional completeness for meets

**Factoid 4.2 (Scott §4).** For any *non-empty* family of elements, the set-theoretic
intersection of the family is again an element. Thus `|A|` is a conditionally complete
inf-semilattice.
-/

namespace Scott1982

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- Carrier intersection of a family of elements. -/
def familyInfCarrier (S : Set sys.Element) : Set α :=
  {a | ∀ x ∈ S, a ∈ x.carrier}

/-- **Factoid 4.2.** Meet of a nonempty family of elements (set-theoretic intersection). -/
def familyInf (S : Set sys.Element) (hne : S.Nonempty) : sys.Element where
  carrier := sys.familyInfCarrier S
  consistent := by
    intro Y hY
    obtain ⟨x₀, hx₀⟩ := hne
    have hYx : (Y : Set α) ⊆ x₀.carrier := fun a ha => (hY ha) x₀ hx₀
    exact x₀.consistent Y hYx
  closed := by
    intro Y a hY hEnt x hx
    have hYx : (Y : Set α) ⊆ x.carrier := fun b hb => (hY hb) x hx
    exact x.closed Y a hYx hEnt

theorem familyInf_le (S : Set sys.Element) (hne : S.Nonempty) {x : sys.Element}
    (hx : x ∈ S) : sys.familyInf S hne ≤ x :=
  fun _a ha => ha x hx

theorem le_familyInf (S : Set sys.Element) (hne : S.Nonempty) {z : sys.Element}
    (h : ∀ x ∈ S, z ≤ x) : z ≤ sys.familyInf S hne :=
  fun _a ha x hx => h x hx ha

/-- `familyInf` is the greatest lower bound of the family. -/
theorem familyInf_le_iff (S : Set sys.Element) (hne : S.Nonempty) {z : sys.Element} :
    z ≤ sys.familyInf S hne ↔ ∀ x ∈ S, z ≤ x :=
  ⟨fun hz _x hx => le_trans hz (sys.familyInf_le S hne hx), sys.le_familyInf S hne⟩

/-- Binary meet agrees with the two-element family meet. -/
theorem familyInf_pair (x y : sys.Element) :
    sys.familyInf ({x, y} : Set sys.Element) ⟨x, Set.mem_insert x {y}⟩ = sys.inf x y := by
  refine le_antisymm ?_ ?_
  · exact sys.le_inf
      (sys.familyInf_le _ _ (Set.mem_insert x {y}))
      (sys.familyInf_le _ _ (Set.mem_insert_of_mem _ rfl))
  · apply sys.le_familyInf
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hy
    · exact sys.inf_le_left _ _
    · have : z = y := hy
      subst this
      exact sys.inf_le_right _ _

end InfoSys

end Scott1982

-- Vendor 1982 — Scott1982.Factoid43 (from vendor/scott1982/Scott1982/Factoid43.lean)

/-!
# Factoid 4.3 — consistent joins

**Factoid 4.3 (Scott §4).** The join of a family of elements exists in `|A|` iff the
union of their carriers is finitely consistent; in that case the join is the deductive
closure of the union. Binary case: `x ⊔ y` exists iff some element bounds both.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- A (possibly infinite) set of tokens is *finitely consistent* when every finite subset
lies in `Con`. -/
def IsFinitelyConsistent (U : Set α) : Prop :=
  ∀ Y : Finset α, (Y : Set α) ⊆ U → Y ∈ sys.Con

/-- Witness: some finite `w ⊆ U` entails every member of `Y ⊆ deductiveClosure U`. -/
theorem exists_entSet_of_subset_deductive
    (U : Set α) (hU : sys.IsFinitelyConsistent U) (Y : Finset α)
    (hY : (Y : Set α) ⊆ {a | ∃ u : Finset α, (u : Set α) ⊆ U ∧ sys.Ent u a}) :
    ∃ w : Finset α, (w : Set α) ⊆ U ∧ sys.EntSet w Y := by
  induction Y using Finset.induction_on with
  | empty =>
    exact ⟨∅, fun _ ha => False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 ha)),
      fun _ ha => False.elim (Finset.notMem_empty _ ha)⟩
  | insert a s _ha ih =>
    have ha' : ∃ u : Finset α, (u : Set α) ⊆ U ∧ sys.Ent u a :=
      hY (Finset.mem_coe.2 (Finset.mem_insert_self a s))
    have hs' : (s : Set α) ⊆ {b | ∃ u : Finset α, (u : Set α) ⊆ U ∧ sys.Ent u b} := by
      intro b hb
      exact hY (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hb)))
    obtain ⟨ua, hua, hEnta⟩ := ha'
    obtain ⟨us, hus, hEnts⟩ := ih hs'
    refine ⟨ua ∪' us, ?_, ?_⟩
    · intro z hz
      rcases mem_funion.mp (Finset.mem_coe.1 hz) with h | h
      · exact hua (Finset.mem_coe.2 h)
      · exact hus (Finset.mem_coe.2 h)
    · intro b hb
      have hwU : (ua ∪' us : Set α) ⊆ U := by
        intro z hz
        rcases mem_funion.mp (Finset.mem_coe.1 hz) with h | h
        · exact hua (Finset.mem_coe.2 h)
        · exact hus (Finset.mem_coe.2 h)
      have hw : ua ∪' us ∈ sys.Con := hU _ hwU
      rcases Finset.mem_insert.mp hb with rfl | hb'
      · exact sys.ent_trans hw (hU ua hua)
          (fun y hy => sys.ent_refl hw (mem_funion.mpr (Or.inl hy))) hEnta
      · exact sys.ent_trans hw (hU us hus)
          (fun y hy => sys.ent_refl hw (mem_funion.mpr (Or.inr hy))) (hEnts b hb')

/-- Deductive closure of a finitely consistent set. -/
def deductiveClosure (U : Set α) (hU : sys.IsFinitelyConsistent U) : sys.Element where
  carrier := {a | ∃ u : Finset α, (u : Set α) ⊆ U ∧ sys.Ent u a}
  consistent := by
    intro Y hY
    obtain ⟨w, hwU, hEnt⟩ := sys.exists_entSet_of_subset_deductive U hU Y hY
    have hw : w ∈ sys.Con := hU w hwU
    exact sys.con_subset (proposition_2_3_ii sys hw hEnt) (subset_funion_right _ _)
  closed := by
    intro Y a hY hEnt
    obtain ⟨w, hwU, hEntY⟩ := sys.exists_entSet_of_subset_deductive U hU Y hY
    have hw : w ∈ sys.Con := hU w hwU
    have hYcon : Y ∈ sys.Con :=
      sys.con_subset (proposition_2_3_ii sys hw hEntY) (subset_funion_right _ _)
    exact ⟨w, hwU, sys.ent_trans hw hYcon hEntY hEnt⟩

theorem subset_deductiveClosure (U : Set α) (hU : sys.IsFinitelyConsistent U) :
    U ⊆ (sys.deductiveClosure U hU).carrier := by
  intro a ha
  refine ⟨{a}, ?_, sys.ent_refl (hU {a} ?_) (Finset.mem_singleton_self a)⟩
  · intro b hb
    have : b = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
    subst this
    exact ha
  · intro b hb
    have : b = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
    subst this
    exact ha

/-- Carrier union of a family of elements. -/
def familyUnionCarrier (S : Set sys.Element) : Set α :=
  {a | ∃ x ∈ S, a ∈ x.carrier}

/-- Join of a family whose carrier-union is finitely consistent. -/
def familySup (S : Set sys.Element)
    (hU : sys.IsFinitelyConsistent (sys.familyUnionCarrier S)) : sys.Element :=
  sys.deductiveClosure (sys.familyUnionCarrier S) hU

theorem le_familySup (S : Set sys.Element)
    (hU : sys.IsFinitelyConsistent (sys.familyUnionCarrier S)) {x : sys.Element}
    (hx : x ∈ S) : x ≤ sys.familySup S hU := by
  intro a ha
  exact sys.subset_deductiveClosure _ hU ⟨x, hx, ha⟩

theorem familySup_le (S : Set sys.Element)
    (hU : sys.IsFinitelyConsistent (sys.familyUnionCarrier S)) {z : sys.Element}
    (h : ∀ x ∈ S, x ≤ z) : sys.familySup S hU ≤ z := by
  intro a ha
  obtain ⟨u, huU, hEnt⟩ := ha
  have huZ : (u : Set α) ⊆ z.carrier := by
    intro b hb
    obtain ⟨x, hx, hb'⟩ := huU hb
    exact h x hx hb'
  exact z.closed u a huZ hEnt

/-- An upper bound of `S` forces the carrier-union to be finitely consistent. -/
theorem finitelyConsistent_of_upperBound (S : Set sys.Element) {z : sys.Element}
    (h : ∀ x ∈ S, x ≤ z) : sys.IsFinitelyConsistent (sys.familyUnionCarrier S) := by
  intro Y hY
  have hYZ : (Y : Set α) ⊆ z.carrier := by
    intro a ha
    obtain ⟨x, hx, ha'⟩ := hY ha
    exact h x hx ha'
  exact z.consistent Y hYZ

/-- Join exists iff the union is finitely consistent. -/
theorem exists_isLUB_iff (S : Set sys.Element) :
    (∃ z : sys.Element, (∀ x ∈ S, x ≤ z) ∧ ∀ w, (∀ x ∈ S, x ≤ w) → z ≤ w) ↔
      Nonempty (sys.IsFinitelyConsistent (sys.familyUnionCarrier S)) := by
  constructor
  · rintro ⟨z, hub, _⟩
    exact ⟨sys.finitelyConsistent_of_upperBound S hub⟩
  · rintro ⟨hU⟩
    refine ⟨sys.familySup S hU, fun x hx => sys.le_familySup S hU hx,
      fun w hw => sys.familySup_le S hU hw⟩

/-- Binary join via deductive closure of `x.carrier ∪ y.carrier`, when consistent. -/
def join (x y : sys.Element)
    (h : sys.IsFinitelyConsistent (x.carrier ∪ y.carrier)) : sys.Element :=
  sys.deductiveClosure (x.carrier ∪ y.carrier) h

theorem le_join_left (x y : sys.Element)
    (h : sys.IsFinitelyConsistent (x.carrier ∪ y.carrier)) : x ≤ sys.join x y h :=
  fun _a ha => sys.subset_deductiveClosure _ h (Or.inl ha)

theorem le_join_right (x y : sys.Element)
    (h : sys.IsFinitelyConsistent (x.carrier ∪ y.carrier)) : y ≤ sys.join x y h :=
  fun _a ha => sys.subset_deductiveClosure _ h (Or.inr ha)

theorem join_le (x y z : sys.Element)
    (h : sys.IsFinitelyConsistent (x.carrier ∪ y.carrier))
    (hx : x ≤ z) (hy : y ≤ z) : sys.join x y h ≤ z := by
  intro a ha
  obtain ⟨u, huU, hEnt⟩ := ha
  have huZ : (u : Set α) ⊆ z.carrier := by
    intro b hb
    rcases huU hb with hb' | hb'
    · exact hx hb'
    · exact hy hb'
  exact z.closed u a huZ hEnt

/-- Binary join exists iff some element bounds both. -/
theorem exists_join_iff (x y : sys.Element) :
    (∃ z : sys.Element, x ≤ z ∧ y ≤ z) ↔
      Nonempty (sys.IsFinitelyConsistent (x.carrier ∪ y.carrier)) := by
  constructor
  · rintro ⟨z, hx, hy⟩
    exact ⟨fun Y hY => z.consistent Y (fun a ha => by
      rcases hY ha with h | h
      · exact hx h
      · exact hy h)⟩
  · rintro ⟨h⟩
    exact ⟨sys.join x y h, sys.le_join_left x y h, sys.le_join_right x y h⟩

end InfoSys

end Scott1982

-- Vendor 1982 — Scott1982.Factoid44 (from vendor/scott1982/Scott1982/Factoid44.lean)

/-!
# Factoid 4.4 — directed (and chain) unions are elements

**Factoid 4.4 (Scott §4).** The union of a nonempty directed family of elements is again
an element (hence a lub). In particular, unions of increasing chains are elements, so
`|A|` is a cpo under inclusion.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- Upward-directed family of elements: any two have a common upper bound in the family. -/
def IsDirected (S : Set sys.Element) : Prop :=
  ∀ (x y : sys.Element), x ∈ S → y ∈ S → ∃ z ∈ S, x ≤ z ∧ y ≤ z

/-- A chain: any two elements are comparable. -/
def IsChain (S : Set sys.Element) : Prop :=
  ∀ (x y : sys.Element), x ∈ S → y ∈ S → x ≤ y ∨ y ≤ x

theorem IsDirected_of_IsChain {S : Set sys.Element} (h : sys.IsChain S) : sys.IsDirected S := by
  intro x y hx hy
  rcases h x y hx hy with hxy | hyx
  · exact ⟨y, hy, hxy, le_rfl⟩
  · exact ⟨x, hx, le_rfl, hyx⟩

/-- Given `Y` whose tokens each lie in some member of a nonempty directed family, find a
single member containing all of `Y`. -/
theorem exists_mem_of_subset_directedUnion (S : Set sys.Element) (hne : S.Nonempty)
    (hdir : sys.IsDirected S) (Y : Finset α)
    (hY : (Y : Set α) ⊆ sys.familyUnionCarrier S) :
    ∃ z ∈ S, (Y : Set α) ⊆ z.carrier := by
  induction Y using Finset.induction_on with
  | empty =>
    obtain ⟨z, hz⟩ := hne
    exact ⟨z, hz, fun _ ha => False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 ha))⟩
  | insert a s _ha ih =>
    have ha' : ∃ x ∈ S, a ∈ x.carrier :=
      hY (Finset.mem_coe.2 (Finset.mem_insert_self a s))
    have hs' : (s : Set α) ⊆ sys.familyUnionCarrier S := by
      intro b hb
      exact hY (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hb)))
    obtain ⟨xa, hxa, haS⟩ := ha'
    obtain ⟨xs, hxs, hsS⟩ := ih hs'
    obtain ⟨z, hz, hxa_le, hxs_le⟩ := hdir xa xs hxa hxs
    refine ⟨z, hz, ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp (Finset.mem_coe.1 hb) with rfl | hb'
    · exact hxa_le haS
    · exact hxs_le (hsS (Finset.mem_coe.2 hb'))

/-- Directed families are finitely consistent on their carrier union. -/
theorem finitelyConsistent_of_directed (S : Set sys.Element) (hne : S.Nonempty)
    (hdir : sys.IsDirected S) :
    sys.IsFinitelyConsistent (sys.familyUnionCarrier S) := by
  intro Y hY
  obtain ⟨z, _hz, hYZ⟩ := sys.exists_mem_of_subset_directedUnion S hne hdir Y hY
  exact z.consistent Y hYZ

/-- **Factoid 4.4.** Union of a nonempty directed family is an element (as `familySup`). -/
def directedSup (S : Set sys.Element) (hne : S.Nonempty) (hdir : sys.IsDirected S) :
    sys.Element :=
  sys.familySup S (sys.finitelyConsistent_of_directed S hne hdir)

theorem le_directedSup (S : Set sys.Element) (hne : S.Nonempty) (hdir : sys.IsDirected S)
    {x : sys.Element} (hx : x ∈ S) : x ≤ sys.directedSup S hne hdir :=
  sys.le_familySup S (sys.finitelyConsistent_of_directed S hne hdir) hx

theorem directedSup_le (S : Set sys.Element) (hne : S.Nonempty) (hdir : sys.IsDirected S)
    {z : sys.Element} (h : ∀ x ∈ S, x ≤ z) : sys.directedSup S hne hdir ≤ z :=
  sys.familySup_le S (sys.finitelyConsistent_of_directed S hne hdir) h

/-- For directed families, the lub carrier equals the raw union (already deductively closed). -/
theorem directedSup_carrier_eq_union (S : Set sys.Element) (hne : S.Nonempty)
    (hdir : sys.IsDirected S) :
    (sys.directedSup S hne hdir).carrier = sys.familyUnionCarrier S := by
  let hU := sys.finitelyConsistent_of_directed S hne hdir
  refine Set.Subset.antisymm ?_ (sys.subset_deductiveClosure _ hU)
  intro a ha
  obtain ⟨u, huU, hEnt⟩ := (ha : a ∈ (sys.deductiveClosure _ hU).carrier)
  obtain ⟨z, hz, huZ⟩ := sys.exists_mem_of_subset_directedUnion S hne hdir u huU
  exact ⟨z, hz, z.closed u a huZ hEnt⟩

/-- Chain unions are elements. -/
def chainSup (S : Set sys.Element) (hne : S.Nonempty) (hchain : sys.IsChain S) : sys.Element :=
  sys.directedSup S hne (sys.IsDirected_of_IsChain hchain)

end InfoSys

end Scott1982

-- Vendor 1982 — Scott1982.Factoid45 (from vendor/scott1982/Scott1982/Factoid45.lean)

/-!
# Factoid 4.5 — algebraicity via finite elements

**Factoid 4.5 (Scott §4).** Finite elements `ū` are compact, and every element is the
directed lub of the finite elements below it (algebraicity). The carrier identity
`x = ⋃{ū | u ⊆ x}` is Factoid 3.6; here we package directedness, the lub form, and
compactness.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- `⊥ = ∅̄`. -/
theorem botElement_eq_closure_empty :
    sys.botElement = sys.closure (∅ : Finset α) sys.con_empty := by
  refine le_antisymm ?_ ?_
  · intro a ha
    -- ha : Ent {bot} a; show Ent ∅ a
    exact sys.ent_trans sys.con_empty (sys.con_sing sys.bot)
      (fun y hy => by
        have : y = sys.bot := Finset.mem_singleton.mp hy
        subst this
        exact sys.ent_bot sys.con_empty)
      ha
  · intro a ha
    -- ha : Ent ∅ a; show Ent {bot} a
    exact sys.ent_trans (sys.con_sing sys.bot) sys.con_empty
      (fun _ hy => False.elim (Finset.notMem_empty _ hy)) ha

/-- Finite approximations of `x`: the set `{ū | u ∈ Con, u ⊆ x}`. -/
def finiteApproximants (x : sys.Element) : Set sys.Element :=
  {y | ∃ (u : Finset α) (hu : u ∈ sys.Con), ↑u ⊆ x.carrier ∧ y = sys.closure u hu}

theorem nonempty_finiteApproximants (x : sys.Element) :
    (sys.finiteApproximants x).Nonempty := by
  refine ⟨sys.botElement, ∅, sys.con_empty, ?_, sys.botElement_eq_closure_empty⟩
  intro a ha
  exact False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 ha))

theorem directed_finiteApproximants (x : sys.Element) :
    sys.IsDirected (sys.finiteApproximants x) := by
  intro y₁ y₂ hy₁ hy₂
  obtain ⟨u, hu, huX, rfl⟩ := hy₁
  obtain ⟨v, hv, hvX, rfl⟩ := hy₂
  obtain ⟨w, hw, hwX, huw, hvw⟩ := sys.closures_directed x hu hv huX hvX
  exact ⟨sys.closure w hw, ⟨w, hw, hwX, rfl⟩, huw, hvw⟩

/-- **Factoid 4.5 / algebraicity.** `x` is the directed lub of its finite approximants. -/
theorem eq_directedSup_finiteApproximants (x : sys.Element) :
    x = sys.directedSup (sys.finiteApproximants x)
      (sys.nonempty_finiteApproximants x) (sys.directed_finiteApproximants x) := by
  refine le_antisymm ?_ ?_
  · -- x ≤ directedSup: every token of x lies in some ū ⊆ x
    intro a ha
    have : a ∈ sys.approxUnion x := (sys.mem_element_iff_mem_closure x a).1 ha
    obtain ⟨u, hu, huX, ha'⟩ := this
    rw [sys.directedSup_carrier_eq_union]
    exact ⟨sys.closure u hu, ⟨u, hu, huX, rfl⟩, ha'⟩
  · -- directedSup ≤ x: each approximant is ≤ x
    apply sys.directedSup_le
    intro y hy
    obtain ⟨u, hu, huX, rfl⟩ := hy
    exact sys.closure_le_element x hu huX

/-- Compactness of finite elements: if `ū ≤ ⊔ S` for directed nonempty `S`, then
`ū ≤` some member of `S`. -/
theorem compact_closure (S : Set sys.Element) (hne : S.Nonempty) (hdir : sys.IsDirected S)
    {u : Finset α} (hu : u ∈ sys.Con)
    (hle : sys.closure u hu ≤ sys.directedSup S hne hdir) :
    ∃ z ∈ S, sys.closure u hu ≤ z := by
  have huU : (u : Set α) ⊆ sys.familyUnionCarrier S := by
    intro a ha
    have : a ∈ (sys.directedSup S hne hdir).carrier :=
      hle (sys.subset_closure hu (Finset.mem_coe.2 ha))
    rwa [sys.directedSup_carrier_eq_union S hne hdir] at this
  obtain ⟨z, hz, huZ⟩ := sys.exists_mem_of_subset_directedUnion S hne hdir u huU
  exact ⟨z, hz, sys.closure_le_element z hu huZ⟩

end InfoSys

end Scott1982

-- Vendor 1982 — Scott1982.Factoid46 (from vendor/scott1982/Scott1982/Factoid46.lean)

/-!
# Factoid 4.6 — Scott topology and continuous maps

**Factoid 4.6 (Scott §4).** Basic opens `[u] = {x | u ⊆ x}` form a neighborhood basis;
`|A|` is `T₀`. Approximable maps induce Scott-continuous functions on elements, and
conversely every Scott-continuous map arises from an approximable relation
(`u f v ↔ ↑v ⊆ f(ū)`).
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- **Scott §4.** Basic open `[u] = {x ∈ |A| | u ⊆ x}`. -/
def basicOpen (A : InfoSys α) (u : Finset α) : Set A.Element :=
  {x | ↑u ⊆ x.carrier}

theorem mem_basicOpen {A : InfoSys α} {u : Finset α} {x : A.Element} :
    x ∈ A.basicOpen u ↔ ↑u ⊆ x.carrier := Iff.rfl

/-- Intersection of basic opens: `[u] ∩ [v] = [u ∪' v]`. -/
theorem basicOpen_inter (A : InfoSys α) (u v : Finset α) :
    A.basicOpen u ∩ A.basicOpen v = A.basicOpen (u ∪' v) := by
  ext x
  constructor
  · intro ⟨hu, hv⟩ a ha
    rcases mem_funion.mp (Finset.mem_coe.1 ha) with h | h
    · exact hu (Finset.mem_coe.2 h)
    · exact hv (Finset.mem_coe.2 h)
  · intro huv
    refine ⟨?_, ?_⟩
    · intro a ha
      exact huv (Finset.mem_coe.2 (mem_funion.mpr (Or.inl (Finset.mem_coe.1 ha))))
    · intro a ha
      exact huv (Finset.mem_coe.2 (mem_funion.mpr (Or.inr (Finset.mem_coe.1 ha))))

/-- **T₀:** elements with the same basic-open neighborhoods are equal. -/
theorem eq_of_basicOpen_eq (A : InfoSys α) {x y : A.Element}
    (h : ∀ u : Finset α, x ∈ A.basicOpen u ↔ y ∈ A.basicOpen u) : x = y := by
  refine le_antisymm ?_ ?_
  · intro a ha
    have : x ∈ A.basicOpen {a} := by
      intro b hb
      have : b = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
      subst this
      exact ha
    exact ((h {a}).1 this) (Finset.mem_coe.2 (Finset.mem_singleton_self a))
  · intro a ha
    have : y ∈ A.basicOpen {a} := by
      intro b hb
      have : b = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
      subst this
      exact ha
    exact ((h {a}).2 this) (Finset.mem_coe.2 (Finset.mem_singleton_self a))

/-- Image of a nonempty set under a function is nonempty. -/
theorem nonempty_image {X Y : Type*} {S : Set X} (hne : S.Nonempty) (f : X → Y) :
    (f '' S).Nonempty :=
  hne.image f

/-- Monotone images preserve directedness. -/
theorem directed_image {A : InfoSys α} {B : InfoSys β} {S : Set A.Element}
    (hdir : A.IsDirected S) (f : A.Element → B.Element)
    (hmono : ∀ {x y}, x ≤ y → f x ≤ f y) : B.IsDirected (f '' S) := by
  intro x y hx hy
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  obtain ⟨z₀, hz₀, hxz, hyz⟩ := hdir x₀ y₀ hx₀ hy₀
  exact ⟨f z₀, ⟨z₀, hz₀, rfl⟩, hmono hxz, hmono hyz⟩

/-- Scott-continuous map of domains: monotone and preserves directed lubs. -/
structure ScottContinuous (A : InfoSys α) (B : InfoSys β) where
  toFun : A.Element → B.Element
  mono' : ∀ {x y : A.Element}, x ≤ y → toFun x ≤ toFun y
  map_directedSup :
    ∀ (S : Set A.Element) (hne : S.Nonempty) (hdir : A.IsDirected S),
      toFun (A.directedSup S hne hdir) =
        B.directedSup (toFun '' S) (nonempty_image hne toFun)
          (directed_image hdir toFun mono')

namespace ScottContinuous

variable {A : InfoSys α} {B : InfoSys β}

theorem mono (f : ScottContinuous A B) {x y : A.Element} (h : x ≤ y) :
    f.toFun x ≤ f.toFun y :=
  f.mono' h

end ScottContinuous

namespace ApproximableMap

variable {A : InfoSys α} {B : InfoSys β}

/-- Approximable maps preserve directed lubs (Scott continuity on elements). -/
theorem toElement_directedSup (f : ApproximableMap A B)
    (S : Set A.Element) (hne : S.Nonempty) (hdir : A.IsDirected S) :
    f.toElement (A.directedSup S hne hdir) =
      B.directedSup (f.toElement '' S) (nonempty_image hne f.toElement)
        (directed_image hdir f.toElement f.toElement_mono) := by
  refine le_antisymm ?_ ?_
  · intro Y ⟨u, hu, hrel⟩
    have huU : (u : Set α) ⊆ A.familyUnionCarrier S := by
      intro a ha
      have : a ∈ (A.directedSup S hne hdir).carrier := hu ha
      rwa [A.directedSup_carrier_eq_union S hne hdir] at this
    obtain ⟨z, hz, huZ⟩ := A.exists_mem_of_subset_directedUnion S hne hdir u huU
    have : Y ∈ (f.toElement z).carrier := ⟨u, huZ, hrel⟩
    rw [B.directedSup_carrier_eq_union]
    exact ⟨f.toElement z, ⟨z, hz, rfl⟩, this⟩
  · apply B.directedSup_le
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact f.toElement_mono (A.le_directedSup S hne hdir hx)

/-- **Factoid 4.6 (→).** Every approximable map is Scott-continuous on elements. -/
def toScottContinuous (f : ApproximableMap A B) : ScottContinuous A B where
  toFun := f.toElement
  mono' := f.toElement_mono
  map_directedSup := f.toElement_directedSup

/-- Relation recovered from a Scott-continuous map: `u f v ↔ ↑v ⊆ g(ū)`. -/
def ofScottContinuous (g : ScottContinuous A B) : ApproximableMap A B where
  rel u v := ∃ hu : u ∈ A.Con, v ∈ B.Con ∧ ↑v ⊆ (g.toFun (A.closure u hu)).carrier
  rel_dom := fun ⟨hu, _, _⟩ => hu
  rel_cod := fun ⟨_, hv, _⟩ => hv
  empty_rel := by
    refine ⟨A.con_empty, B.con_empty, ?_⟩
    intro b hb
    exact False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 hb))
  union_right := by
    intro u v v' ⟨hu, hv, hsub⟩ ⟨_hu', hv', hsub'⟩
    refine ⟨hu, ?_, ?_⟩
    · have hsubUV : ↑(v ∪' v') ⊆ (g.toFun (A.closure u hu)).carrier := by
        intro b hb
        rcases mem_funion.mp (Finset.mem_coe.1 hb) with h | h
        · exact hsub (Finset.mem_coe.2 h)
        · exact hsub' (Finset.mem_coe.2 h)
      exact (g.toFun (A.closure u hu)).consistent (v ∪' v') hsubUV
    · intro b hb
      rcases mem_funion.mp (Finset.mem_coe.1 hb) with h | h
      · exact hsub (Finset.mem_coe.2 h)
      · exact hsub' (Finset.mem_coe.2 h)
  mono := by
    intro u u' v v' ⟨hu, hv, hsub⟩ hEntUU' hEntVV' hu' hv'
    refine ⟨hu', hv', ?_⟩
    have hclos : A.closure u hu ≤ A.closure u' hu' :=
      A.closure_le_of_entSet hu hu' hEntUU'
    intro b hb
    have hEntb : B.Ent v b := hEntVV' b hb
    have hb_in : b ∈ (g.toFun (A.closure u hu)).carrier :=
      (g.toFun (A.closure u hu)).closed v b hsub hEntb
    exact g.mono hclos hb_in

/-- **Factoid 4.6 (←).** Scott-continuous maps recover as `toElement` of the induced
approximable relation. -/
theorem toElement_ofScottContinuous (g : ScottContinuous A B) (x : A.Element) :
    (ofScottContinuous g).toElement x = g.toFun x := by
  refine le_antisymm ?_ ?_
  · intro Y ⟨u, hu, ⟨huCon, _, hsub⟩⟩
    have : A.closure u huCon ≤ x := A.closure_le_element x huCon hu
    exact g.mono this (hsub (Finset.mem_coe.2 (Finset.mem_singleton_self Y)))
  · intro Y hY
    let S := A.finiteApproximants x
    have hne := A.nonempty_finiteApproximants x
    have hdir := A.directed_finiteApproximants x
    have hx : x = A.directedSup S hne hdir := A.eq_directedSup_finiteApproximants x
    have hdirImg := directed_image hdir g.toFun g.mono'
    have hneImg := nonempty_image hne g.toFun
    have hg : g.toFun x = B.directedSup (g.toFun '' S) hneImg hdirImg := by
      have h1 : g.toFun x = g.toFun (A.directedSup S hne hdir) := congrArg g.toFun hx
      have h2 : g.toFun (A.directedSup S hne hdir) =
          B.directedSup (g.toFun '' S) hneImg hdirImg :=
        g.map_directedSup S hne hdir
      exact h1.trans h2
    have hY' : Y ∈ (B.directedSup (g.toFun '' S) hneImg hdirImg).carrier := by
      rw [← hg]; exact hY
    have hY'' : Y ∈ B.familyUnionCarrier (g.toFun '' S) := by
      rwa [← B.directedSup_carrier_eq_union (g.toFun '' S) hneImg hdirImg]
    obtain ⟨z, hz, hYz⟩ := hY''
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨u, hu, huX, rfl⟩ := hy
    refine ⟨u, huX, ⟨hu, B.con_sing Y, ?_⟩⟩
    intro b hb
    have : b = Y := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
    subst this
    exact hYz

end ApproximableMap

end InfoSys

end Scott1982

-- Vendor 1972 — Scott1972.ContinuousLattice.WayBelow (from vendor/scott1972/Scott1972/ContinuousLattice/WayBelow.lean)

/-!
# The induced (Scott) topology and the way-below relation (Scott 1972, §2)

This file formalizes the core of Scott's §2 *Continuous Lattices*: the topology a complete
lattice carries intrinsically (Scott's "induced topology", today the **Scott topology**),
the **way-below relation** `≪`, the basic properties of `≪` (Scott's Proposition 2.2), and
the definition of a **continuous lattice** (Scott's Definition 2.3).

Scott defines the induced topology on a partially ordered set `D` by declaring `U` open iff

* (i)  `U` is an upper set; and
* (ii) whenever `S ⊆ D` is directed (and, in this paper, non-empty), `⊔S` exists and
       `⊔S ∈ U`, then `S ∩ U ≠ ∅`.

He then defines `x ≪ y` ("`x` is way below `y`") to mean `y ∈ interior {z | x ⊑ z}`, the
interior being taken in this induced topology. We encode "Scott-open" as the predicate
`ScottOpen` and `≪` as `WayBelow`, witnessing the interior by a Scott-open neighbourhood
contained in the principal up-set `Set.Ici x = {z | x ≤ z}`. This is faithful to Scott's
topological definition (rather than the order-theoretic shortcut), and as a result Scott's
Proposition 2.2 (vi) and (vii) fall straight out of the open-set axioms.

This is the classical/topological version of the theory, so we reason classically.
-/

namespace Scott1972.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]

/-- **Scott 1972, §2, the induced topology.** `U` is *Scott-open* when it is an upper set and
is inaccessible by suprema of non-empty directed sets: if a non-empty directed `S` has its
supremum in `U`, then some member of `S` already lies in `U`. -/
def ScottOpen (U : Set D) : Prop :=
  letI : LE D :=
    (CompleteLattice.toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder.toLE
  letI : SupSet D :=
    (CompleteLattice.toCompleteSemilatticeSup (α := D)).toSupSet
  IsUpperSet U ∧
    ∀ ⦃S : Set D⦄, S.Nonempty → DirectedOn (· ≤ ·) S → sSup S ∈ U → (S ∩ U).Nonempty

theorem ScottOpen.isUpperSet {U : Set D} (h : ScottOpen U) : IsUpperSet U := h.1

theorem scottOpen_univ : ScottOpen (Set.univ : Set D) := by
  refine ⟨isUpperSet_univ, fun S hS _ _ => ?_⟩
  obtain ⟨s, hs⟩ := hS
  exact ⟨s, hs, Set.mem_univ s⟩

theorem scottOpen_inter {U V : Set D} (hU : ScottOpen U) (hV : ScottOpen V) :
    ScottOpen (U ∩ V) := by
  refine ⟨hU.1.inter hV.1, fun S hS hSdir hmem => ?_⟩
  obtain ⟨s₁, hs₁S, hs₁U⟩ := hU.2 hS hSdir hmem.1
  obtain ⟨s₂, hs₂S, hs₂V⟩ := hV.2 hS hSdir hmem.2
  obtain ⟨s₃, hs₃S, h₁, h₂⟩ := hSdir s₁ hs₁S s₂ hs₂S
  exact ⟨s₃, hs₃S, hU.1 h₁ hs₁U, hV.1 h₂ hs₂V⟩

theorem scottOpen_sUnion {C : Set (Set D)} (hC : ∀ U ∈ C, ScottOpen U) :
    ScottOpen (⋃₀ C) := by
  refine ⟨isUpperSet_sUnion fun U hU => (hC U hU).1, fun S hS hSdir hmem => ?_⟩
  obtain ⟨U, hUC, hUmem⟩ := hmem
  obtain ⟨s, hsS, hsU⟩ := (hC U hUC).2 hS hSdir hUmem
  exact ⟨s, hsS, U, hUC, hsU⟩

/-- **Scott 1972, §2.** The *way-below* relation: `x ≪ y` iff `y` lies in the interior of the
principal up-set `Set.Ici x` for the induced topology, witnessed by a Scott-open
neighbourhood of `y` contained in `Set.Ici x`. -/
def WayBelow (x y : D) : Prop :=
  letI : LE D :=
    (CompleteLattice.toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder.toLE
  letI : Preorder D :=
    (CompleteLattice.toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder
  ∃ U : Set D, ScottOpen U ∧ y ∈ U ∧ U ⊆ Set.Ici x

@[inherit_doc] scoped infix:50 " ≪ " => WayBelow

/-- **Scott 1972, Proposition 2.2(v).** `x ≪ y` implies `x ≤ y`. -/
theorem WayBelow.le {x y : D} (h : x ≪ y) : x ≤ y := by
  obtain ⟨U, _, hyU, hsub⟩ := h
  exact hsub hyU

/-- **Scott 1972, Proposition 2.2(i).** `⊥ ≪ x` for every `x`. -/
theorem bot_wayBelow (x : D) : (⊥ : D) ≪ x :=
  ⟨Set.univ, scottOpen_univ, Set.mem_univ x, fun _ _ => bot_le⟩

/-- **Scott 1972, Proposition 2.2(iii).** `x ≪ y` and `y ≤ z` imply `x ≪ z` (monotone on the
right). -/
theorem WayBelow.trans_le {x y z : D} (h : x ≪ y) (hyz : y ≤ z) : x ≪ z := by
  obtain ⟨U, hU, hyU, hsub⟩ := h
  exact ⟨U, hU, hU.1 hyz hyU, hsub⟩

/-- **Scott 1972, Proposition 2.2(iv).** `x ≤ y` and `y ≪ z` imply `x ≪ z` (monotone on the
left). -/
theorem WayBelow.le_trans {x y z : D} (hxy : x ≤ y) (h : y ≪ z) : x ≪ z := by
  obtain ⟨U, hU, hzU, hsub⟩ := h
  refine ⟨U, hU, hzU, fun w hw => ?_⟩
  have hyw : y ≤ w := Set.mem_Ici.1 (hsub hw)
  exact Set.mem_Ici.2 (hxy.trans hyw)

/-- **Scott 1972, Proposition 2.2(ii).** `x ≪ z` and `y ≪ z` imply `x ⊔ y ≪ z`. -/
theorem WayBelow.sup {x y z : D} (hx : x ≪ z) (hy : y ≪ z) : x ⊔ y ≪ z := by
  obtain ⟨U, hU, hzU, hUsub⟩ := hx
  obtain ⟨V, hV, hzV, hVsub⟩ := hy
  refine ⟨U ∩ V, scottOpen_inter hU hV, ⟨hzU, hzV⟩, fun w hw => ?_⟩
  exact Set.mem_Ici.2 (sup_le (hUsub hw.1) (hVsub hw.2))

/-- Auxiliary: the up-set `{z | x ≪ z}` is itself Scott-open. (This is *not* Scott's
Proposition 2.2(vi) — see `wayBelow_self_iff_scottOpen_Ici` for that — but it is a standard
and useful fact, the openness of the sets `↟x`.) -/
theorem scottOpen_wayBelow (x : D) : ScottOpen {z | x ≪ z} := by
  refine ⟨fun a b hab ha => ha.trans_le hab, fun S hS hSdir hmem => ?_⟩
  obtain ⟨U, hU, hsupU, hsub⟩ := hmem
  obtain ⟨s, hsS, hsU⟩ := hU.2 hS hSdir hsupU
  exact ⟨s, hsS, ⟨U, hU, hsU, hsub⟩⟩

/-- **Scott 1972, Proposition 2.2(vi).** `x ≪ x` iff the principal up-set `{z | x ⊑ z}` (i.e.
`Set.Ici x`) is Scott-open. This characterizes the *compact* (finite, isolated) elements:
`x` is compact exactly when `↑x` is open. -/
theorem wayBelow_self_iff_scottOpen_Ici {x : D} : x ≪ x ↔ ScottOpen (Set.Ici x) := by
  constructor
  · rintro ⟨U, hU, hxU, hsub⟩
    -- `Ici x = U`: `Ici x ⊆ U` since `U` is upper and `x ∈ U`; `U ⊆ Ici x` is `hsub`.
    have hIci : Set.Ici x = U :=
      le_antisymm (fun w hw => hU.1 (Set.mem_Ici.1 hw) hxU) hsub
    rw [hIci]; exact hU
  · intro hopen
    exact ⟨Set.Ici x, hopen, Set.self_mem_Ici, le_refl _⟩

/-- **Scott 1972, Proposition 2.2(vii).** For a non-empty directed set `S`, `x ≪ ⊔S` iff
`x ≪ y` for some `y ∈ S`. The forward direction is exactly inaccessibility of a Scott-open
set; the backward direction is monotonicity on the right. -/
theorem wayBelow_sSup_iff {x : D} {S : Set D} (hS : S.Nonempty)
    (hSdir : DirectedOn (· ≤ ·) S) : x ≪ sSup S ↔ ∃ y ∈ S, x ≪ y := by
  constructor
  · rintro ⟨U, hU, hsupU, hsub⟩
    obtain ⟨s, hsS, hsU⟩ := hU.2 hS hSdir hsupU
    exact ⟨s, hsS, U, hU, hsU, hsub⟩
  · rintro ⟨y, hyS, hxy⟩
    exact hxy.trans_le (le_sSup hyS)

/-- **Scott 1972, Definition 2.3.** A complete lattice `D` is a *continuous lattice* when every
element is the supremum of the elements way below it: `y = ⊔ {x | x ≪ y}`. -/
def IsContinuousLattice (D : Type u) [CompleteLattice D] : Prop :=
  letI : LE D :=
    (CompleteLattice.toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder.toLE
  ∀ y : D, IsLUB {x | x ≪ y} y

/-- In a continuous lattice, `y` is the actual supremum of `{x | x ≪ y}`. -/
theorem IsContinuousLattice.sSup_wayBelow (h : IsContinuousLattice D) (y : D) :
    sSup {x | x ≪ y} = y :=
  (h y).sSup_eq

/-- The set `{x | x ≪ y}` of elements way below `y` is directed: it is closed under binary
joins by Proposition 2.2(ii) (`WayBelow.sup`). This holds in *any* complete lattice. -/
theorem directedOn_wayBelow (y : D) : DirectedOn (· ≤ ·) {x | x ≪ y} :=
  fun a ha b hb => ⟨a ⊔ b, ha.sup hb, le_sup_left, le_sup_right⟩

/-- **Interpolation property of `≪`.** In a continuous lattice, the way-below relation
interpolates: `a ≪ c` implies there is some `b` with `a ≪ b ≪ c`.

The proof runs Scott's standard argument: the set `M = {m | ∃ x, m ≪ x ∧ x ≪ c}` is directed
(using directedness of `{· ≪ x}` twice) and has supremum `c` (using continuity twice). Hence
`a ≪ c = ⊔M` with `M` directed forces `a ≪ m` for some `m ∈ M`, say `m ≪ x ≪ c`; then
`a ≪ m ≤ x` gives `a ≪ x ≪ c`, so `b := x` works. -/
theorem wayBelow_interpolate (hD : IsContinuousLattice D) {a c : D} (hac : a ≪ c) :
    ∃ b, a ≪ b ∧ b ≪ c := by
  set M : Set D := {m | ∃ x, m ≪ x ∧ x ≪ c} with hM
  have hMdir : DirectedOn (· ≤ ·) M := by
    rintro m₁ ⟨x₁, hm₁x₁, hx₁c⟩ m₂ ⟨x₂, hm₂x₂, hx₂c⟩
    obtain ⟨x₃, hx₃c, hx₁₃, hx₂₃⟩ := directedOn_wayBelow c x₁ hx₁c x₂ hx₂c
    obtain ⟨m₃, hm₃x₃, hm₁m₃, hm₂m₃⟩ :=
      directedOn_wayBelow x₃ m₁ (hm₁x₁.trans_le hx₁₃) m₂ (hm₂x₂.trans_le hx₂₃)
    exact ⟨m₃, ⟨x₃, hm₃x₃, hx₃c⟩, hm₁m₃, hm₂m₃⟩
  have hMne : M.Nonempty := ⟨⊥, a, bot_wayBelow a, hac⟩
  have hsupM : sSup M = c := by
    refine le_antisymm (sSup_le ?_) ?_
    · rintro m ⟨x, hmx, hxc⟩
      exact hmx.le.trans hxc.le
    · rw [← hD.sSup_wayBelow c]
      refine sSup_le fun x hxc => ?_
      rw [← hD.sSup_wayBelow x]
      exact sSup_le fun m hmx => le_sSup ⟨x, hmx, hxc⟩
  rw [← hsupM] at hac
  obtain ⟨m, ⟨x, hmx, hxc⟩, ham⟩ := (wayBelow_sSup_iff hMne hMdir).1 hac
  exact ⟨x, ham.trans_le hmx.le, hxc⟩

/-- In a continuous lattice the sets `↟a = {z | a ≪ z}` form a basis of the Scott topology:
every Scott-open `U` containing `z` contains some basic neighbourhood `↟a` of `z`. Indeed
`z = ⊔{a | a ≪ z}` is a directed supremum lying in the open set `U`, so some `a ≪ z` already
lies in `U`, and then `↟a ⊆ ↑a ⊆ U`. -/
theorem exists_wayBelow_subset (hD : IsContinuousLattice D) {U : Set D} (hU : ScottOpen U)
    {z : D} (hz : z ∈ U) : ∃ a, a ≪ z ∧ {w | a ≪ w} ⊆ U := by
  have hne : {a | a ≪ z}.Nonempty := ⟨⊥, bot_wayBelow z⟩
  have hsup : sSup {a | a ≪ z} ∈ U := by rw [hD.sSup_wayBelow z]; exact hz
  obtain ⟨a, haz, haU⟩ := hU.2 hne (directedOn_wayBelow z) hsup
  exact ⟨a, haz, fun w hw => hU.1 hw.le haU⟩

/-- A strengthening of `exists_wayBelow_subset`: the witness `a ≪ z` can be taken with the whole
principal up-set `Set.Ici a` (not merely `↟a`) inside `U`. The element `a` produced lies in the
open `U`, which is upper, so `↑a ⊆ U`. -/
theorem exists_wayBelow_Ici_subset (hD : IsContinuousLattice D) {U : Set D} (hU : ScottOpen U)
    {z : D} (hz : z ∈ U) : ∃ a, a ≪ z ∧ Set.Ici a ⊆ U := by
  have hne : {a | a ≪ z}.Nonempty := ⟨⊥, bot_wayBelow z⟩
  have hsup : sSup {a | a ≪ z} ∈ U := by rw [hD.sSup_wayBelow z]; exact hz
  obtain ⟨a, haz, haU⟩ := hU.2 hne (directedOn_wayBelow z) hsup
  exact ⟨a, haz, fun w hw => hU.1 (Set.mem_Ici.1 hw) haU⟩

/-- The infimum of a Scott-open neighbourhood of `y` is way below `y`: the open set is itself
the required witness. Scott uses this in moving between Definition 2.3 and Proposition 2.4. -/
theorem sInf_wayBelow {U : Set D} (hU : ScottOpen U) {y : D} (hy : y ∈ U) :
    sInf U ≪ y :=
  ⟨U, hU, hy, fun _ hz => Set.mem_Ici.2 (sInf_le hz)⟩

/-- **Scott 1972, Proposition 2.4.** A complete lattice is continuous iff every element is the
supremum of the infima of its open neighbourhoods: `y = ⊔ {⊓U : y ∈ U open}`. This is Scott's
alternate form of Definition 2.3. -/
theorem isContinuousLattice_iff_isLUB_sInf_nhds :
    IsContinuousLattice D ↔
      ∀ y : D, IsLUB {a : D | ∃ U, ScottOpen U ∧ y ∈ U ∧ a = sInf U} y := by
  constructor
  · intro h y
    refine ⟨?_, ?_⟩
    · rintro a ⟨U, hU, hyU, rfl⟩
      exact (sInf_wayBelow hU hyU).le
    · intro b hb
      refine (h y).2 ?_
      intro x hx
      obtain ⟨U, hU, hyU, hsub⟩ := hx
      have hxle : x ≤ sInf U := le_sInf fun _ hz => Set.mem_Ici.1 (hsub hz)
      exact hxle.trans (hb ⟨U, hU, hyU, rfl⟩)
  · intro h y
    refine ⟨fun x hx => hx.le, ?_⟩
    intro b hb
    refine (h y).2 ?_
    rintro a ⟨U, hU, hyU, rfl⟩
    exact hb (sInf_wayBelow hU hyU)

end Scott1972.ContinuousLattice

-- Vendor 1982 — Scott1982.FunctionSpace (from vendor/scott1982/Scott1982/FunctionSpace.lean)

/-!
# Function space — Definition 7.1

**Scott 1982, Definition 7.1.** Tokens of `A → B` are pairs `(u, v)` of consistent
sets. Consistency of a finite set `w` of such pairs asks that whenever a selection of
inputs is jointly consistent, the corresponding outputs are jointly consistent.
Entailment is the least approximable map generated by `w`:
`w ⊢ (u', v')` iff the union of those `vᵢ` whose `uᵢ` are entailed by `u'` entails `v'`.

Constructively we package the right-hand side of (iv) as an existential witness: some
`s ⊆ w` of pairs whose inputs are entailed by `u'` and whose output-union entails `v'`
(avoiding an undecidable `filter` on `EntSet`).
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

/-- Token type of the function space `A → B` (Scott 7.1(i)). -/
def FunToken (A : InfoSys α) (B : InfoSys β) : Type _ :=
  {p : Finset α × Finset β // p.1 ∈ A.Con ∧ p.2 ∈ B.Con}

instance (A : InfoSys α) (B : InfoSys β) : DecidableEq (FunToken A B) :=
  fun p q =>
    match decidableEq_finset p.val.1 q.val.1, decidableEq_finset p.val.2 q.val.2 with
    | isTrue h1, isTrue h2 => isTrue (Subtype.ext (Prod.ext h1 h2))
    | isFalse n1, _ =>
        isFalse fun h => n1 (congrArg (fun r : FunToken A B => r.val.1) h)
    | isTrue _, isFalse n2 =>
        isFalse fun h => n2 (congrArg (fun r : FunToken A B => r.val.2) h)

variable (A : InfoSys α) (B : InfoSys β)

/-- The empty pair is a function-space token. -/
theorem funBot_property : (∅ : Finset α) ∈ A.Con ∧ (∅ : Finset β) ∈ B.Con :=
  ⟨A.con_empty, B.con_empty⟩

/-- Function-space bottom `Δ_{A→B} = (∅, ∅)` (Scott 7.1(ii)). -/
def funBot : FunToken A B :=
  ⟨(∅, ∅), funBot_property A B⟩

theorem funion_left_comm (a b c : Finset α) :
    a ∪' (b ∪' c) = b ∪' (a ∪' c) := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inr (mem_funion.mpr (Or.inl h)))
    · rcases mem_funion.mp h with h | h
      · exact mem_funion.mpr (Or.inl h)
      · exact mem_funion.mpr (Or.inr (mem_funion.mpr (Or.inr h)))
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inr (mem_funion.mpr (Or.inl h)))
    · rcases mem_funion.mp h with h | h
      · exact mem_funion.mpr (Or.inl h)
      · exact mem_funion.mpr (Or.inr (mem_funion.mpr (Or.inr h)))

theorem funion_left_comm' (a b c : Finset β) :
    a ∪' (b ∪' c) = b ∪' (a ∪' c) := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inr (mem_funion.mpr (Or.inl h)))
    · rcases mem_funion.mp h with h | h
      · exact mem_funion.mpr (Or.inl h)
      · exact mem_funion.mpr (Or.inr (mem_funion.mpr (Or.inr h)))
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inr (mem_funion.mpr (Or.inl h)))
    · rcases mem_funion.mp h with h | h
      · exact mem_funion.mpr (Or.inl h)
      · exact mem_funion.mpr (Or.inr (mem_funion.mpr (Or.inr h)))

private theorem FunctionSpace_funion_assoc (a b c : Finset α) :
    (a ∪' b) ∪' c = a ∪' (b ∪' c) := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h
    · rcases mem_funion.mp h with h | h
      · exact mem_funion.mpr (Or.inl h)
      · exact mem_funion.mpr (Or.inr (mem_funion.mpr (Or.inl h)))
    · exact mem_funion.mpr (Or.inr (mem_funion.mpr (Or.inr h)))
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inl (mem_funion.mpr (Or.inl h)))
    · rcases mem_funion.mp h with h | h
      · exact mem_funion.mpr (Or.inl (mem_funion.mpr (Or.inr h)))
      · exact mem_funion.mpr (Or.inr h)

private theorem FunctionSpace_funion_comm (a b : Finset α) : a ∪' b = b ∪' a := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inr h)
    · exact mem_funion.mpr (Or.inl h)
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inr h)
    · exact mem_funion.mpr (Or.inl h)

private theorem FunctionSpace_funion_assoc' (a b c : Finset β) :
    (a ∪' b) ∪' c = a ∪' (b ∪' c) := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h
    · rcases mem_funion.mp h with h | h
      · exact mem_funion.mpr (Or.inl h)
      · exact mem_funion.mpr (Or.inr (mem_funion.mpr (Or.inl h)))
    · exact mem_funion.mpr (Or.inr (mem_funion.mpr (Or.inr h)))
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inl (mem_funion.mpr (Or.inl h)))
    · rcases mem_funion.mp h with h | h
      · exact mem_funion.mpr (Or.inl (mem_funion.mpr (Or.inr h)))
      · exact mem_funion.mpr (Or.inr h)

private theorem FunctionSpace_funion_comm' (a b : Finset β) : a ∪' b = b ∪' a := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inr h)
    · exact mem_funion.mpr (Or.inl h)
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inr h)
    · exact mem_funion.mpr (Or.inl h)

instance instLeftCommutativeFunInput :
    LeftCommutative fun p : FunToken A B => (funion p.val.1 : Finset α → Finset α) :=
  ⟨fun p q s => funion_left_comm p.val.1 q.val.1 s⟩

instance instLeftCommutativeFunOutput :
    LeftCommutative fun p : FunToken A B => (funion p.val.2 : Finset β → Finset β) :=
  ⟨fun p q s => funion_left_comm' p.val.2 q.val.2 s⟩

/-- Union of input components of a finite set of function-space tokens. -/
def funInputUnion (s : Finset (FunToken A B)) : Finset α :=
  Multiset.foldr (fun p : FunToken A B => funion p.val.1) (∅ : Finset α) s.1

/-- Union of output components of a finite set of function-space tokens. -/
def funOutputUnion (s : Finset (FunToken A B)) : Finset β :=
  Multiset.foldr (fun p : FunToken A B => funion p.val.2) (∅ : Finset β) s.1

private theorem FunctionSpace_mem_foldr_funInput (t : Multiset (FunToken A B)) (x : α) :
    x ∈ Multiset.foldr (fun p : FunToken A B => funion p.val.1) (∅ : Finset α) t ↔
      ∃ p ∈ t, x ∈ p.val.1 := by
  refine Multiset.induction_on t ?_ ?_
  · constructor
    · intro hx
      exact False.elim (Finset.notMem_empty x hx)
    · rintro ⟨_, hp, _⟩
      exact False.elim (by cases hp)
  · intro p t ih
    simp only [Multiset.foldr_cons, mem_funion, ih, Multiset.mem_cons]
    constructor
    · rintro (hx | ⟨q, hq, hx⟩)
      · exact ⟨p, Or.inl rfl, hx⟩
      · exact ⟨q, Or.inr hq, hx⟩
    · rintro ⟨q, hq, hx⟩
      rcases hq with rfl | hq
      · exact Or.inl hx
      · exact Or.inr ⟨q, hq, hx⟩

private theorem FunctionSpace_mem_foldr_funOutput (t : Multiset (FunToken A B)) (y : β) :
    y ∈ Multiset.foldr (fun p : FunToken A B => funion p.val.2) (∅ : Finset β) t ↔
      ∃ p ∈ t, y ∈ p.val.2 := by
  refine Multiset.induction_on t ?_ ?_
  · constructor
    · intro hy
      exact False.elim (Finset.notMem_empty y hy)
    · rintro ⟨_, hp, _⟩
      exact False.elim (by cases hp)
  · intro p t ih
    simp only [Multiset.foldr_cons, mem_funion, ih, Multiset.mem_cons]
    constructor
    · rintro (hy | ⟨q, hq, hy⟩)
      · exact ⟨p, Or.inl rfl, hy⟩
      · exact ⟨q, Or.inr hq, hy⟩
    · rintro ⟨q, hq, hy⟩
      rcases hq with rfl | hq
      · exact Or.inl hy
      · exact Or.inr ⟨q, hq, hy⟩

theorem mem_funInputUnion {s : Finset (FunToken A B)} {x : α} :
    x ∈ funInputUnion A B s ↔ ∃ p ∈ s, x ∈ p.val.1 := by
  simpa [funInputUnion] using FunctionSpace_mem_foldr_funInput A B s.1 x

theorem mem_funOutputUnion {s : Finset (FunToken A B)} {y : β} :
    y ∈ funOutputUnion A B s ↔ ∃ p ∈ s, y ∈ p.val.2 := by
  simpa [funOutputUnion] using FunctionSpace_mem_foldr_funOutput A B s.1 y

theorem funInputUnion_empty : funInputUnion A B (∅ : Finset (FunToken A B)) = ∅ :=
  rfl

theorem funOutputUnion_empty : funOutputUnion A B (∅ : Finset (FunToken A B)) = ∅ :=
  rfl

theorem funInputUnion_singleton (p : FunToken A B) :
    funInputUnion A B {p} = p.val.1 := by
  ext x
  constructor
  · intro hx
    rcases (mem_funInputUnion A B).1 hx with ⟨q, hq, hx'⟩
    have : q = p := Finset.mem_singleton.mp hq
    subst this
    exact hx'
  · intro hx
    exact (mem_funInputUnion A B).2 ⟨p, Finset.mem_singleton_self p, hx⟩

theorem funOutputUnion_singleton (p : FunToken A B) :
    funOutputUnion A B {p} = p.val.2 := by
  ext y
  constructor
  · intro hy
    rcases (mem_funOutputUnion A B).1 hy with ⟨q, hq, hy'⟩
    have : q = p := Finset.mem_singleton.mp hq
    subst this
    exact hy'
  · intro hy
    exact (mem_funOutputUnion A B).2 ⟨p, Finset.mem_singleton_self p, hy⟩

theorem funInputUnion_funion (s t : Finset (FunToken A B)) :
    funInputUnion A B (s ∪' t) = funInputUnion A B s ∪' funInputUnion A B t := by
  ext x
  constructor
  · intro hx
    rcases (mem_funInputUnion A B).1 hx with ⟨p, hp, hx'⟩
    rcases mem_funion.mp hp with hp | hp
    · exact mem_funion.mpr (Or.inl ((mem_funInputUnion A B).2 ⟨p, hp, hx'⟩))
    · exact mem_funion.mpr (Or.inr ((mem_funInputUnion A B).2 ⟨p, hp, hx'⟩))
  · intro hx
    rcases mem_funion.mp hx with hx | hx
    · rcases (mem_funInputUnion A B).1 hx with ⟨p, hp, hx'⟩
      exact (mem_funInputUnion A B).2 ⟨p, mem_funion.mpr (Or.inl hp), hx'⟩
    · rcases (mem_funInputUnion A B).1 hx with ⟨p, hp, hx'⟩
      exact (mem_funInputUnion A B).2 ⟨p, mem_funion.mpr (Or.inr hp), hx'⟩

theorem funOutputUnion_funion (s t : Finset (FunToken A B)) :
    funOutputUnion A B (s ∪' t) = funOutputUnion A B s ∪' funOutputUnion A B t := by
  ext y
  constructor
  · intro hy
    rcases (mem_funOutputUnion A B).1 hy with ⟨p, hp, hy'⟩
    rcases mem_funion.mp hp with hp | hp
    · exact mem_funion.mpr (Or.inl ((mem_funOutputUnion A B).2 ⟨p, hp, hy'⟩))
    · exact mem_funion.mpr (Or.inr ((mem_funOutputUnion A B).2 ⟨p, hp, hy'⟩))
  · intro hy
    rcases mem_funion.mp hy with hy | hy
    · rcases (mem_funOutputUnion A B).1 hy with ⟨p, hp, hy'⟩
      exact (mem_funOutputUnion A B).2 ⟨p, mem_funion.mpr (Or.inl hp), hy'⟩
    · rcases (mem_funOutputUnion A B).1 hy with ⟨p, hp, hy'⟩
      exact (mem_funOutputUnion A B).2 ⟨p, mem_funion.mpr (Or.inr hp), hy'⟩

theorem funInputUnion_insert (s : Finset (FunToken A B)) (p : FunToken A B) :
    funInputUnion A B (insert p s) = p.val.1 ∪' funInputUnion A B s := by
  have h : insert p s = ({p} : Finset (FunToken A B)) ∪' s := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_insert.mp hq with hqp | hq
      · exact mem_funion.mpr (Or.inl (hqp ▸ Finset.mem_singleton_self p))
      · exact mem_funion.mpr (Or.inr hq)
    · intro hq
      rcases mem_funion.mp hq with hq | hq
      · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hq))
      · exact Finset.mem_insert_of_mem hq
  rw [h, funInputUnion_funion, funInputUnion_singleton]

theorem funOutputUnion_insert (s : Finset (FunToken A B)) (p : FunToken A B) :
    funOutputUnion A B (insert p s) = p.val.2 ∪' funOutputUnion A B s := by
  have h : insert p s = ({p} : Finset (FunToken A B)) ∪' s := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_insert.mp hq with hqp | hq
      · exact mem_funion.mpr (Or.inl (hqp ▸ Finset.mem_singleton_self p))
      · exact mem_funion.mpr (Or.inr hq)
    · intro hq
      rcases mem_funion.mp hq with hq | hq
      · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hq))
      · exact Finset.mem_insert_of_mem hq
  rw [h, funOutputUnion_funion, funOutputUnion_singleton]

/-- Consistency for the function space (Scott 7.1(iii)). -/
def FunCon (w : Finset (FunToken A B)) : Prop :=
  ∀ s ⊆ w, funInputUnion A B s ∈ A.Con → funOutputUnion A B s ∈ B.Con

/-- Entailment for the function space (Scott 7.1(iv), constructive witness form).
Includes `FunCon` so `ent_con` has the ambient consistency hypothesis. -/
def FunEnt (w : Finset (FunToken A B)) (p : FunToken A B) : Prop :=
  FunCon A B w ∧
    ∃ s ⊆ w, (∀ q ∈ s, A.EntSet p.val.1 q.val.1) ∧
      B.EntSet (funOutputUnion A B s) p.val.2

theorem entSet_inputUnion_of_ent {u' : Finset α} {s : Finset (FunToken A B)}
    (h : ∀ q ∈ s, A.EntSet u' q.val.1) :
    A.EntSet u' (funInputUnion A B s) := by
  intro x hx
  rcases (mem_funInputUnion A B).1 hx with ⟨q, hq, hx'⟩
  exact h q hq x hx'

private theorem FunctionSpace_funInputUnion_con_of_ent {u' : Finset α} {s : Finset (FunToken A B)}
    (hu' : u' ∈ A.Con) (h : ∀ q ∈ s, A.EntSet u' q.val.1) :
    funInputUnion A B s ∈ A.Con :=
  A.con_subset (proposition_2_3_ii A hu' (entSet_inputUnion_of_ent A B h))
    (subset_funion_right _ _)

private theorem FunctionSpace_insert_filter_ne {p : FunToken A B} {t : Finset (FunToken A B)}
    (hp : p ∈ t) : insert p (t.filter (· ≠ p)) = t := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact (Finset.mem_filter.mp hq).1
  · intro hq
    if h : q = p then
      exact Finset.mem_insert.mpr (Or.inl h)
    else
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hq, h⟩))

private theorem FunctionSpace_filter_ne_subset_of_subset_insert {p : FunToken A B}
    {t w : Finset (FunToken A B)} (ht : t ⊆ insert p w) :
    t.filter (· ≠ p) ⊆ w := by
  intro q hq
  have ⟨hqt, hne⟩ := Finset.mem_filter.mp hq
  have : q ∈ insert p w := ht hqt
  rcases Finset.mem_insert.mp this with rfl | hqW
  · exact False.elim (hne rfl)
  · exact hqW

/-- Combine entailment witnesses along a finite set of tokens (for `ent_trans`). -/
private theorem FunctionSpace_exists_combined_witness {u' : Finset α} {s : Finset (FunToken A B)}
    {v : Finset (FunToken A B)}
    (hv : FunCon A B v) (hu' : u' ∈ A.Con)
    (hEntIn : ∀ q ∈ s, A.EntSet u' q.val.1)
    (hWit : ∀ q ∈ s, ∃ s_q ⊆ v, (∀ r ∈ s_q, A.EntSet q.val.1 r.val.1) ∧
      B.EntSet (funOutputUnion A B s_q) q.val.2) :
    ∃ S ⊆ v, (∀ r ∈ S, A.EntSet u' r.val.1) ∧
      B.EntSet (funOutputUnion A B S) (funOutputUnion A B s) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
    · intro _ hq
      exact False.elim (Finset.notMem_empty _ hq)
    · intro y hy
      exact False.elim (Finset.notMem_empty y hy)
  | insert q s' hqnot ih =>
    have hEntIn' : ∀ r ∈ s', A.EntSet u' r.val.1 := fun r hr =>
      hEntIn r (Finset.mem_insert_of_mem hr)
    have hWit' : ∀ r ∈ s', ∃ s_r ⊆ v, (∀ t ∈ s_r, A.EntSet r.val.1 t.val.1) ∧
        B.EntSet (funOutputUnion A B s_r) r.val.2 := fun r hr =>
      hWit r (Finset.mem_insert_of_mem hr)
    obtain ⟨S', hS'sub, hS'in, hS'out⟩ := ih hEntIn' hWit'
    obtain ⟨Sq, hSqsub, hSqin, hSqout⟩ := hWit q (Finset.mem_insert_self q s')
    refine ⟨S' ∪' Sq, funion_subset_iff.mpr ⟨hS'sub, hSqsub⟩, ?_, ?_⟩
    · intro r hr
      rcases mem_funion.mp hr with hr | hr
      · exact hS'in r hr
      · have hEnt_q : A.EntSet u' q.val.1 := hEntIn q (Finset.mem_insert_self q s')
        have hEnt_r : A.EntSet q.val.1 r.val.1 := hSqin r hr
        exact proposition_2_3_iv A hu' q.property.1 hEnt_q hEnt_r
    · rw [funOutputUnion_funion, funOutputUnion_insert]
      have hinS' : funInputUnion A B S' ∈ A.Con :=
        FunctionSpace_funInputUnion_con_of_ent A B hu' hS'in
      have houtS' : funOutputUnion A B S' ∈ B.Con := hv S' hS'sub hinS'
      have hinSq : funInputUnion A B Sq ∈ A.Con :=
        FunctionSpace_funInputUnion_con_of_ent A B q.property.1 hSqin
      have houtSq : funOutputUnion A B Sq ∈ B.Con := hv Sq hSqsub hinSq
      have hinUnion : funInputUnion A B (S' ∪' Sq) ∈ A.Con := by
        rw [funInputUnion_funion]
        have hEnt : A.EntSet u' (funInputUnion A B S' ∪' funInputUnion A B Sq) :=
          proposition_2_3_vi A
            (entSet_inputUnion_of_ent A B hS'in)
            (proposition_2_3_iv A hu' q.property.1
              (hEntIn q (Finset.mem_insert_self q s'))
              (entSet_inputUnion_of_ent A B hSqin))
        exact A.con_subset (proposition_2_3_ii A hu' hEnt) (subset_funion_right _ _)
      have houtUnion : funOutputUnion A B S' ∪' funOutputUnion A B Sq ∈ B.Con := by
        have : funOutputUnion A B (S' ∪' Sq) ∈ B.Con := hv _ (funion_subset_iff.mpr ⟨hS'sub, hSqsub⟩) hinUnion
        rwa [funOutputUnion_funion] at this
      have hEnt1 : B.EntSet (funOutputUnion A B S' ∪' funOutputUnion A B Sq)
          (funOutputUnion A B s') :=
        proposition_2_3_v B houtS' houtUnion (subset_funion_left _ _) hS'out
          (Finset.Subset.refl _)
      have hEnt2 : B.EntSet (funOutputUnion A B S' ∪' funOutputUnion A B Sq) q.val.2 :=
        proposition_2_3_v B houtSq houtUnion (subset_funion_right _ _) hSqout
          (Finset.Subset.refl _)
      exact proposition_2_3_vi B hEnt2 hEnt1

/-- Downward closure of function-space consistency. -/
theorem functionSystem_con_subset {w w' : Finset (FunToken A B)}
    (hw : FunCon A B w) (hw' : w' ⊆ w) : FunCon A B w' :=
  fun s hs hin => hw s (fun _ hq => hw' (hs hq)) hin

/-- Singletons are consistent in the function space. -/
theorem functionSystem_con_sing (p : FunToken A B) : FunCon A B {p} := by
  intro s hs _hin
  have hsub : funOutputUnion A B s ⊆ p.val.2 := by
    intro y hy
    rcases (mem_funOutputUnion A B).1 hy with ⟨q, hq, hy'⟩
    have hq' : q = p := Finset.mem_singleton.mp (hs hq)
    cases hq'
    exact hy'
  exact B.con_subset p.property.2 hsub

/-- Adding an entailed function-space token preserves consistency. -/
theorem functionSystem_ent_con {w : Finset (FunToken A B)} {p : FunToken A B}
    (hEnt : FunEnt A B w p) : FunCon A B (insert p w) := by
  obtain ⟨hw, s, hs, hEntIn, hEntOut⟩ := hEnt
  intro t ht hin
  if hp : p ∈ t then
    let t' := t.filter (· ≠ p)
    have ht_eq : insert p t' = t := FunctionSpace_insert_filter_ne A B hp
    have ht'sub : t' ⊆ w := FunctionSpace_filter_ne_subset_of_subset_insert A B ht
    have hin' : p.val.1 ∪' funInputUnion A B t' ∈ A.Con := by
      rwa [← ht_eq, funInputUnion_insert] at hin
    have hsub : s ∪' t' ⊆ w := funion_subset_iff.mpr ⟨hs, ht'sub⟩
    have hEnt_in_s : A.EntSet p.val.1 (funInputUnion A B s) :=
      entSet_inputUnion_of_ent A B hEntIn
    have hEnt_big : A.EntSet (p.val.1 ∪' funInputUnion A B t') (funInputUnion A B s) :=
      proposition_2_3_v A p.property.1 hin' (subset_funion_left _ _) hEnt_in_s
        (Finset.Subset.refl _)
    have hbig : (p.val.1 ∪' funInputUnion A B t') ∪' funInputUnion A B s ∈ A.Con :=
      proposition_2_3_ii A hin' hEnt_big
    have hin_st' : funInputUnion A B s ∪' funInputUnion A B t' ∈ A.Con := by
      have heq :
          (p.val.1 ∪' funInputUnion A B t') ∪' funInputUnion A B s =
            p.val.1 ∪' (funInputUnion A B s ∪' funInputUnion A B t') := by
        rw [FunctionSpace_funion_assoc, FunctionSpace_funion_comm (funInputUnion A B t')]
      have hbig' : p.val.1 ∪' (funInputUnion A B s ∪' funInputUnion A B t') ∈ A.Con := by
        rwa [heq] at hbig
      exact A.con_subset hbig' (subset_funion_right _ _)
    have hin_union : funInputUnion A B (s ∪' t') ∈ A.Con := by
      rwa [funInputUnion_funion]
    have hout_union : funOutputUnion A B s ∪' funOutputUnion A B t' ∈ B.Con := by
      have : funOutputUnion A B (s ∪' t') ∈ B.Con := hw _ hsub hin_union
      rwa [funOutputUnion_funion] at this
    have hout_s : funOutputUnion A B s ∈ B.Con :=
      B.con_subset hout_union (subset_funion_left _ _)
    have hEnt_out' : B.EntSet (funOutputUnion A B s ∪' funOutputUnion A B t') p.val.2 :=
      proposition_2_3_v B hout_s hout_union (subset_funion_left _ _) hEntOut
        (Finset.Subset.refl _)
    have hfinal :
        (funOutputUnion A B s ∪' funOutputUnion A B t') ∪' p.val.2 ∈ B.Con :=
      proposition_2_3_ii B hout_union hEnt_out'
    have hout_t : p.val.2 ∪' funOutputUnion A B t' ∈ B.Con := by
      have heq :
          (funOutputUnion A B s ∪' funOutputUnion A B t') ∪' p.val.2 =
            funOutputUnion A B s ∪' (p.val.2 ∪' funOutputUnion A B t') := by
        rw [FunctionSpace_funion_assoc', FunctionSpace_funion_comm' (funOutputUnion A B t')]
      have hfinal' :
          funOutputUnion A B s ∪' (p.val.2 ∪' funOutputUnion A B t') ∈ B.Con := by
        rwa [heq] at hfinal
      exact B.con_subset hfinal' (subset_funion_right _ _)
    have : funOutputUnion A B t ∈ B.Con := by
      rwa [← ht_eq, funOutputUnion_insert]
    exact this
  else
    have ht' : t ⊆ w := by
      intro q hq
      have : q ∈ insert p w := ht hq
      rcases Finset.mem_insert.mp this with rfl | hqW
      · exact False.elim (hp hq)
      · exact hqW
    exact hw t ht' hin

/-- The function-space bottom is entailed by every consistent set. -/
theorem functionSystem_ent_bot {w : Finset (FunToken A B)} (hw : FunCon A B w) :
    FunEnt A B w (funBot A B) :=
  ⟨hw, ∅, Finset.empty_subset _,
    fun q hq => False.elim (Finset.notMem_empty q hq),
    fun y hy => False.elim (Finset.notMem_empty y hy)⟩

/-- Function-space entailment is reflexive on members. -/
theorem functionSystem_ent_refl {w : Finset (FunToken A B)} {p : FunToken A B}
    (hw : FunCon A B w) (hp : p ∈ w) : FunEnt A B w p :=
  ⟨hw, {p},
    fun q hq => by
      cases Finset.mem_singleton.mp hq
      exact hp,
    fun q hq => by
      cases Finset.mem_singleton.mp hq
      exact proposition_2_3_iii A p.property.1,
    by
      rw [funOutputUnion_singleton]
      exact proposition_2_3_iii B p.property.2⟩

/-- Function-space entailment is transitive. -/
theorem functionSystem_ent_trans {u v : Finset (FunToken A B)} {c : FunToken A B}
    (hv : FunCon A B v) (hu : FunCon A B u)
    (hEnts : ∀ y ∈ u, FunEnt A B v y) (hEnt : FunEnt A B u c) :
    FunEnt A B v c := by
  obtain ⟨_, s, hs, hEntIn, hEntOut⟩ := hEnt
  refine ⟨hv, ?_⟩
  have hWit : ∀ q ∈ s, ∃ s_q ⊆ v, (∀ r ∈ s_q, A.EntSet q.val.1 r.val.1) ∧
      B.EntSet (funOutputUnion A B s_q) q.val.2 := by
    intro q hq
    exact (hEnts q (hs hq)).2
  obtain ⟨S, hSsub, hSin, hSout⟩ :=
    FunctionSpace_exists_combined_witness A B hv c.property.1 hEntIn hWit
  refine ⟨S, hSsub, hSin, ?_⟩
  have hin_s : funInputUnion A B s ∈ A.Con :=
    FunctionSpace_funInputUnion_con_of_ent A B c.property.1 hEntIn
  have hout_s : funOutputUnion A B s ∈ B.Con := hu s hs hin_s
  have hin_S : funInputUnion A B S ∈ A.Con :=
    FunctionSpace_funInputUnion_con_of_ent A B c.property.1 hSin
  have hout_S : funOutputUnion A B S ∈ B.Con := hv S hSsub hin_S
  exact proposition_2_3_iv B hout_S hout_s hSout hEntOut

/-- **Definition 7.1.** The function-space information system `A → B`. -/
def functionSystem : InfoSys (FunToken A B) where
  bot := funBot A B
  Con := {w | FunCon A B w}
  Ent := FunEnt A B
  con_subset := functionSystem_con_subset A B
  con_sing := functionSystem_con_sing A B
  ent_con := functionSystem_ent_con A B
  ent_bot := functionSystem_ent_bot A B
  ent_refl := functionSystem_ent_refl A B
  ent_trans := functionSystem_ent_trans A B

end InfoSys

end Scott1982

-- Vendor 1982 — Scott1982.Proposition53 (from vendor/scott1982/Scott1982/Proposition53.lean)

/-!
# Proposition 5.3 — images, order, and the closure bridge

**Scott 1982, Proposition 5.3.** Remaining clauses after Def 5.2 / `toElement`:
singleton reduction (Scott’s remark before Def 5.2); (v) the bridge
`u f v ↔ v̄ ⊆ f(ū)`; (iii) pointwise order; (ii) extensionality via elements.
(i) and (iv) are already `toElement` / `toElement_mono` in `Approximable.lean`.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable {A : InfoSys α} {B : InfoSys β}

private theorem Proposition53_singleton_funion_eq (a : β) (s : Finset β) :
    ({a} : Finset β) ∪' s = insert a s := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with ha | hs
    · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp ha))
    · exact Finset.mem_insert_of_mem hs
  · intro hx
    rcases Finset.mem_insert.mp hx with ha | hs
    · exact mem_funion.mpr (Or.inl (Finset.mem_singleton.mpr ha))
    · exact mem_funion.mpr (Or.inr hs)

/-- **Singleton reduction** (Scott, before Def 5.2). -/
theorem rel_iff_forall_singleton (f : ApproximableMap A B)
    {u : Finset α} {v : Finset β} (hu : u ∈ A.Con) (hv : v ∈ B.Con) :
    f.rel u v ↔ ∀ Y ∈ v, f.rel u ({Y} : Finset β) := by
  constructor
  · intro hrel Y hY
    exact f.mono hrel (proposition_2_3_iii A hu)
      (fun Z hZ => by
        rw [Finset.mem_singleton] at hZ
        subst hZ
        exact B.ent_refl hv hY)
      hu (B.con_sing Y)
  · intro hsing
    induction v using Finset.induction_on with
    | empty =>
      exact f.mono f.empty_rel (A.entSet_empty u) (B.entSet_empty ∅) hu B.con_empty
    | insert a s ha ih =>
      have hv' : insert a s ∈ B.Con := hv
      have hsCon : s ∈ B.Con := B.con_subset hv' (Finset.subset_insert a s)
      have h1 : f.rel u {a} := hsing a (Finset.mem_insert_self a s)
      have h2 : f.rel u s :=
        ih hsCon fun Y hY => hsing Y (Finset.mem_insert_of_mem hY)
      have hU : f.rel u ({a} ∪' s) := f.union_right h1 h2
      simpa [Proposition53_singleton_funion_eq] using hU

/-- **Proposition 5.3(v).** `u f v` iff `v̄ ⊆ f(ū)`. -/
theorem rel_iff_closure_le (f : ApproximableMap A B)
    {u : Finset α} {v : Finset β} (hu : u ∈ A.Con) (hv : v ∈ B.Con) :
    f.rel u v ↔ B.closure v hv ≤ f.toElement (A.closure u hu) := by
  constructor
  · intro hrel Y hY
    refine ⟨u, A.subset_closure hu, ?_⟩
    exact f.mono hrel (proposition_2_3_iii A hu)
      (fun Z hZ => by
        rw [Finset.mem_singleton] at hZ
        subst hZ
        exact hY)
      hu (B.con_sing Y)
  · intro hsub
    have hv_sub : ↑v ⊆ (f.toElement (A.closure u hu)).carrier :=
      fun y hy => hsub (B.subset_closure hv hy)
    obtain ⟨u', hu', hrel'⟩ := exists_rel_of_subset_image f (A.closure u hu) v hv_sub
    have hEnt : A.EntSet u u' := fun y hy => hu' (Finset.mem_coe.2 hy)
    exact f.mono hrel' hEnt (proposition_2_3_iii B hv) hu hv

/-- Relation inclusion of approximable maps. -/
def Le (f g : ApproximableMap A B) : Prop := ∀ ⦃u v⦄, f.rel u v → g.rel u v

/-- **Proposition 5.3(iii).** `f ⊆ g` iff `f(x) ⊆ g(x)` for all elements `x`. -/
theorem le_iff_toElement_le (f g : ApproximableMap A B) :
    Le f g ↔ ∀ x : A.Element, f.toElement x ≤ g.toElement x := by
  constructor
  · intro hfg x Y ⟨u, hu, hrel⟩
    exact ⟨u, hu, hfg hrel⟩
  · intro hpoint u v hrel
    have hu : u ∈ A.Con := f.rel_dom hrel
    have hv : v ∈ B.Con := f.rel_cod hrel
    have hbridge : B.closure v hv ≤ f.toElement (A.closure u hu) :=
      (f.rel_iff_closure_le hu hv).1 hrel
    have hsub : B.closure v hv ≤ g.toElement (A.closure u hu) :=
      le_trans hbridge (hpoint (A.closure u hu))
    exact (g.rel_iff_closure_le hu hv).2 hsub

/-- **Proposition 5.3(ii).** `f = g` iff `f(x) = g(x)` for all elements `x`. -/
theorem ext_iff_toElement (f g : ApproximableMap A B) :
    f = g ↔ ∀ x : A.Element, f.toElement x = g.toElement x := by
  constructor
  · intro h x
    rw [h]
  · intro hpoint
    refine ApproximableMap.ext fun u v => ?_
    constructor
    · intro hrel
      exact (le_iff_toElement_le f g).2 (fun x => (hpoint x) ▸ le_rfl) hrel
    · intro hrel
      exact (le_iff_toElement_le g f).2 (fun x => (hpoint x).symm ▸ le_rfl) hrel

end ApproximableMap

end InfoSys

end Scott1982

-- Vendor 1982 — Scott1982.Proposition54 (from vendor/scott1982/Scott1982/Proposition54.lean)

/-!
# Proposition 5.4 — the identity approximable mapping

**Scott 1982, Proposition 5.4.** `u I_A v ↔ u ⊢_A v`, and `I_A(x) = x`.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

/-- **Proposition 5.4(i).** Identity approximable mapping given by entailment. -/
def idMap : ApproximableMap A A where
  rel u v := u ∈ A.Con ∧ v ∈ A.Con ∧ A.EntSet u v
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨A.con_empty, A.con_empty, A.entSet_empty ∅⟩
  union_right := by
    rintro u v v' ⟨hu, _hv, huv⟩ ⟨_, _hv', huv'⟩
    have hEnt : A.EntSet u (v ∪' v') := proposition_2_3_vi (sys := A) huv huv'
    have hBig : u ∪' (v ∪' v') ∈ A.Con :=
      proposition_2_3_ii (sys := A) (u := u) (v := v ∪' v') hu hEnt
    have hCon : v ∪' v' ∈ A.Con :=
      A.con_subset hBig (subset_funion_right u (v ∪' v'))
    exact ⟨hu, hCon, hEnt⟩
  mono := by
    rintro u u' v v' ⟨hu, hv, huv⟩ hEntu hEntv hu' hv'
    refine ⟨hu', hv', ?_⟩
    exact proposition_2_3_iv A hu' hv
      (proposition_2_3_iv A hu' hu hEntu huv) hEntv

/-- **Proposition 5.4(ii).** `I_A(x) = x`. -/
theorem idMap_toElement (x : A.Element) : (idMap A).toElement x = x := by
  apply le_antisymm
  · intro Y ⟨u, hu, hrel⟩
    -- hrel.2.2 : EntSet u {Y}, so Ent u Y
    have hEnt : A.Ent u Y := hrel.2.2 Y (Finset.mem_singleton_self Y)
    exact x.closed u Y hu hEnt
  · intro Y hY
    refine ⟨{Y}, ?_, ?_⟩
    · intro z hz
      have hz' : z ∈ ({Y} : Finset α) := Finset.mem_coe.1 hz
      rw [Finset.mem_singleton] at hz'
      rw [hz']
      exact hY
    · refine ⟨A.con_sing Y, A.con_sing Y, ?_⟩
      exact proposition_2_3_iii A (A.con_sing Y)

end InfoSys

end Scott1982

-- Vendor 1982 — Scott1982.Proposition55 (from vendor/scott1982/Scott1982/Proposition55.lean)

/-!
# Proposition 5.5 — composition of approximable mappings

**Scott 1982, Proposition 5.5.** `u (g ∘ f) w ↔ ∃ v, u f v ∧ v g w`, and
`(g ∘ f)(x) = g(f(x))`.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable {A : InfoSys α} {B : InfoSys β} {C : InfoSys γ}

/-- **Proposition 5.5(i).** Composition of approximable mappings. -/
def comp (g : ApproximableMap B C) (f : ApproximableMap A B) : ApproximableMap A C where
  rel u w := ∃ v, f.rel u v ∧ g.rel v w
  rel_dom := fun ⟨_, hf, _⟩ => f.rel_dom hf
  rel_cod := fun ⟨_, _, hg⟩ => g.rel_cod hg
  empty_rel := ⟨∅, f.empty_rel, g.empty_rel⟩
  union_right := by
    rintro u w w' ⟨v, hf, hg⟩ ⟨v', hf', hg'⟩
    -- Need common middle: use union_right on f to get u f (v ∪' v'), then g.
    have hfU : f.rel u (v ∪' v') := f.union_right hf hf'
    have hvU : v ∪' v' ∈ B.Con := f.rel_cod hfU
    have hEntv : B.EntSet (v ∪' v') v :=
      fun y hy => B.ent_refl hvU (subset_funion_left v v' hy)
    have hEntv' : B.EntSet (v ∪' v') v' :=
      fun y hy => B.ent_refl hvU (subset_funion_right v v' hy)
    have hg1 : g.rel (v ∪' v') w :=
      g.mono hg hEntv (proposition_2_3_iii C (g.rel_cod hg)) hvU (g.rel_cod hg)
    have hg2 : g.rel (v ∪' v') w' :=
      g.mono hg' hEntv' (proposition_2_3_iii C (g.rel_cod hg')) hvU (g.rel_cod hg')
    exact ⟨v ∪' v', hfU, g.union_right hg1 hg2⟩
  mono := by
    rintro u u' w w' ⟨v, hf, hg⟩ hEntu hEntw hu' hw'
    refine ⟨v, ?_, ?_⟩
    · exact f.mono hf hEntu (proposition_2_3_iii B (f.rel_cod hf)) hu' (f.rel_cod hf)
    · exact g.mono hg (proposition_2_3_iii B (f.rel_cod hf)) hEntw (f.rel_cod hf) hw'

/-- **Proposition 5.5(ii).** `(g ∘ f)(x) = g(f(x))`. -/
theorem comp_toElement (g : ApproximableMap B C) (f : ApproximableMap A B) (x : A.Element) :
    (comp g f).toElement x = g.toElement (f.toElement x) := by
  apply le_antisymm
  · intro Z ⟨u, hu, ⟨v, hf, hg⟩⟩
    -- Z ∈ g(f(x)): need ∃ v' ⊆ f(x), v' g {Z}. Have v with u f v and v g {Z}?
    -- hg : g.rel v w where w should be {Z}. Our rel is to w = {Z} from toElement def.
    -- Actually ⟨u, hu, hrel⟩ where hrel : ∃ v, f.rel u v ∧ g.rel v {Z}
    refine ⟨v, ?_, hg⟩
    intro b hb
    -- b ∈ v ⇒ need b ∈ f(x). Since u f v and u ⊆ x, use: u f {b} by mono, so b ∈ f(x).
    have hb' : b ∈ v := Finset.mem_coe.1 hb
    have hsing : f.rel u {b} :=
      f.mono hf (proposition_2_3_iii A (f.rel_dom hf))
        (fun z hz => by
          rw [Finset.mem_singleton] at hz; subst hz
          exact B.ent_refl (f.rel_cod hf) hb')
        (f.rel_dom hf) (B.con_sing b)
    exact ⟨u, hu, hsing⟩
  · intro Z ⟨v, hv, hg⟩
    -- Z ∈ g(f(x)) with v ⊆ f(x), v g {Z}.
    -- Need u ⊆ x with u (g∘f) {Z}. From v ⊆ f(x), get u with u f v (exists_rel).
    obtain ⟨u, hu, hf⟩ := exists_rel_of_subset_image f x v hv
    exact ⟨u, hu, ⟨v, hf, hg⟩⟩

end ApproximableMap

end InfoSys

end Scott1982

-- Vendor 1982 — Scott1982.Product (from vendor/scott1982/Scott1982/Product.lean)

/-!
# Product of information systems — Definition 6.1

**Scott 1982, Definition 6.1.** Tokens of `A × B` are pairs of the form
`(X, Δ_B)` or `(Δ_A, Y)`, with `Δ = (Δ_A, Δ_B)`. Consistency and entailment act
independently on the two projections `fst u` and `snd u`.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Scott 6.1(i): a product token is `(X, Δ_B)` or `(Δ_A, Y)`. -/
def IsProdToken (A : InfoSys α) (B : InfoSys β) (p : α × β) : Prop :=
  p.1 = A.bot ∨ p.2 = B.bot

instance (A : InfoSys α) (B : InfoSys β) (p : α × β) : Decidable (IsProdToken A B p) :=
  if h1 : p.1 = A.bot then isTrue (Or.inl h1)
  else if h2 : p.2 = B.bot then isTrue (Or.inr h2)
  else isFalse fun h => h.elim h1 h2

/-- Token type of the product system `A × B`. -/
def ProdToken (A : InfoSys α) (B : InfoSys β) : Type _ :=
  {p : α × β // IsProdToken A B p}

instance instDecidableEqProdToken (A : InfoSys α) (B : InfoSys β) :
    DecidableEq (ProdToken A B) :=
  Subtype.instDecidableEq

variable (A : InfoSys α) (B : InfoSys β)

/-- Product bottom `Δ_{A×B} = (Δ_A, Δ_B)`. -/
def prodBot : ProdToken A B :=
  ⟨(A.bot, B.bot), Or.inl rfl⟩

private instance Product_instLeftCommutativeFstInsert :
    LeftCommutative fun p : ProdToken A B => (insert p.val.1 : Finset α → Finset α) :=
  ⟨fun p q s => insert_comm' p.val.1 q.val.1 s⟩

private instance Product_instLeftCommutativeSndInsert :
    LeftCommutative fun p : ProdToken A B => (insert p.val.2 : Finset β → Finset β) :=
  ⟨fun p q s => insert_comm' p.val.2 q.val.2 s⟩

/-- Left projection of a finite set of product tokens (Scott 6.1). -/
def fstFinset (u : Finset (ProdToken A B)) : Finset α :=
  Multiset.foldr (fun p : ProdToken A B => insert p.val.1) (∅ : Finset α)
    (u.filter (fun p => p.val.2 = B.bot)).1

/-- Right projection of a finite set of product tokens (Scott 6.1). -/
def sndFinset (u : Finset (ProdToken A B)) : Finset β :=
  Multiset.foldr (fun p : ProdToken A B => insert p.val.2) (∅ : Finset β)
    (u.filter (fun p => p.val.1 = A.bot)).1

private theorem Product_mem_foldr_fst (s : Multiset (ProdToken A B)) (x : α) :
    x ∈ Multiset.foldr (fun p : ProdToken A B => insert p.val.1) (∅ : Finset α) s ↔
      ∃ p ∈ s, p.val.1 = x := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hx
      exact False.elim (Finset.notMem_empty x hx)
    · rintro ⟨p, hp, _⟩
      exact False.elim (by cases hp)
  · intro p t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (hx | ⟨q, hq, hq1⟩)
      · exact ⟨p, Or.inl rfl, hx.symm⟩
      · exact ⟨q, Or.inr hq, hq1⟩
    · rintro ⟨q, hq, hq1⟩
      rcases hq with rfl | hq
      · exact Or.inl hq1.symm
      · exact Or.inr ⟨q, hq, hq1⟩

private theorem Product_mem_foldr_snd (s : Multiset (ProdToken A B)) (y : β) :
    y ∈ Multiset.foldr (fun p : ProdToken A B => insert p.val.2) (∅ : Finset β) s ↔
      ∃ p ∈ s, p.val.2 = y := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hy
      exact False.elim (Finset.notMem_empty y hy)
    · rintro ⟨p, hp, _⟩
      exact False.elim (by cases hp)
  · intro p t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (hy | ⟨q, hq, hq2⟩)
      · exact ⟨p, Or.inl rfl, hy.symm⟩
      · exact ⟨q, Or.inr hq, hq2⟩
    · rintro ⟨q, hq, hq2⟩
      rcases hq with rfl | hq
      · exact Or.inl hq2.symm
      · exact Or.inr ⟨q, hq, hq2⟩

theorem mem_fstFinset {u : Finset (ProdToken A B)} {x : α} :
    x ∈ fstFinset A B u ↔ ∃ p ∈ u, p.val.2 = B.bot ∧ p.val.1 = x := by
  unfold fstFinset
  rw [Product_mem_foldr_fst]
  constructor
  · rintro ⟨p, hp, hx⟩
    have hp' := Finset.mem_filter.mp hp
    exact ⟨p, hp'.1, hp'.2, hx⟩
  · rintro ⟨p, hp, hbot, hx⟩
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hbot⟩, hx⟩

theorem mem_sndFinset {u : Finset (ProdToken A B)} {y : β} :
    y ∈ sndFinset A B u ↔ ∃ p ∈ u, p.val.1 = A.bot ∧ p.val.2 = y := by
  unfold sndFinset
  rw [Product_mem_foldr_snd]
  constructor
  · rintro ⟨p, hp, hy⟩
    have hp' := Finset.mem_filter.mp hp
    exact ⟨p, hp'.1, hp'.2, hy⟩
  · rintro ⟨p, hp, hbot, hy⟩
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hbot⟩, hy⟩

theorem fstFinset_empty : fstFinset A B (∅ : Finset (ProdToken A B)) = ∅ := by
  ext x
  constructor
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨_, hp, _, _⟩
    exact False.elim (Finset.notMem_empty _ hp)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem sndFinset_empty : sndFinset A B (∅ : Finset (ProdToken A B)) = ∅ := by
  ext y
  constructor
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨_, hp, _, _⟩
    exact False.elim (Finset.notMem_empty _ hp)
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

theorem fstFinset_mono {u v : Finset (ProdToken A B)} (h : v ⊆ u) :
    fstFinset A B v ⊆ fstFinset A B u := by
  intro x hx
  rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
  exact (mem_fstFinset A B).2 ⟨p, h hp, hbot, hx'⟩

theorem sndFinset_mono {u v : Finset (ProdToken A B)} (h : v ⊆ u) :
    sndFinset A B v ⊆ sndFinset A B u := by
  intro y hy
  rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
  exact (mem_sndFinset A B).2 ⟨p, h hp, hbot, hy'⟩

theorem fstFinset_insert_left (u : Finset (ProdToken A B)) (p : ProdToken A B)
    (hp : p.val.2 = B.bot) :
    fstFinset A B (insert p u) = insert p.val.1 (fstFinset A B u) := by
  ext x
  constructor
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨q, hq, hbot, hx'⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_insert.mpr (Or.inl hx'.symm)
    · exact Finset.mem_insert.mpr (Or.inr ((mem_fstFinset A B).2 ⟨q, hq, hbot, hx'⟩))
  · intro hx
    rcases Finset.mem_insert.mp hx with hx' | hx'
    · exact (mem_fstFinset A B).2 ⟨p, Finset.mem_insert_self p u, hp, hx'.symm⟩
    · rcases (mem_fstFinset A B).1 hx' with ⟨q, hq, hbot, hxq⟩
      exact (mem_fstFinset A B).2 ⟨q, Finset.mem_insert_of_mem hq, hbot, hxq⟩

theorem fstFinset_insert_not_left (u : Finset (ProdToken A B)) (p : ProdToken A B)
    (hp : p.val.2 ≠ B.bot) :
    fstFinset A B (insert p u) = fstFinset A B u := by
  ext x
  constructor
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨q, hq, hbot, hx'⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact False.elim (hp hbot)
    · exact (mem_fstFinset A B).2 ⟨q, hq, hbot, hx'⟩
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨q, hq, hbot, hx'⟩
    exact (mem_fstFinset A B).2 ⟨q, Finset.mem_insert_of_mem hq, hbot, hx'⟩

theorem sndFinset_insert_right (u : Finset (ProdToken A B)) (p : ProdToken A B)
    (hp : p.val.1 = A.bot) :
    sndFinset A B (insert p u) = insert p.val.2 (sndFinset A B u) := by
  ext y
  constructor
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨q, hq, hbot, hy'⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_insert.mpr (Or.inl hy'.symm)
    · exact Finset.mem_insert.mpr (Or.inr ((mem_sndFinset A B).2 ⟨q, hq, hbot, hy'⟩))
  · intro hy
    rcases Finset.mem_insert.mp hy with hy' | hy'
    · exact (mem_sndFinset A B).2 ⟨p, Finset.mem_insert_self p u, hp, hy'.symm⟩
    · rcases (mem_sndFinset A B).1 hy' with ⟨q, hq, hbot, hyq⟩
      exact (mem_sndFinset A B).2 ⟨q, Finset.mem_insert_of_mem hq, hbot, hyq⟩

theorem sndFinset_insert_not_right (u : Finset (ProdToken A B)) (p : ProdToken A B)
    (hp : p.val.1 ≠ A.bot) :
    sndFinset A B (insert p u) = sndFinset A B u := by
  ext y
  constructor
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨q, hq, hbot, hy'⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact False.elim (hp hbot)
    · exact (mem_sndFinset A B).2 ⟨q, hq, hbot, hy'⟩
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨q, hq, hbot, hy'⟩
    exact (mem_sndFinset A B).2 ⟨q, Finset.mem_insert_of_mem hq, hbot, hy'⟩

theorem fstFinset_singleton_left (p : ProdToken A B) (hp : p.val.2 = B.bot) :
    fstFinset A B {p} = {p.val.1} := by
  rw [show ({p} : Finset _) = insert p ∅ from rfl, fstFinset_insert_left A B ∅ p hp,
    fstFinset_empty]
  rfl

theorem sndFinset_singleton_right (p : ProdToken A B) (hp : p.val.1 = A.bot) :
    sndFinset A B {p} = {p.val.2} := by
  rw [show ({p} : Finset _) = insert p ∅ from rfl, sndFinset_insert_right A B ∅ p hp,
    sndFinset_empty]
  rfl

theorem fstFinset_funion (u v : Finset (ProdToken A B)) :
    fstFinset A B (u ∪' v) = fstFinset A B u ∪' fstFinset A B v := by
  ext x
  constructor
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
    rcases mem_funion.mp hp with hp | hp
    · exact mem_funion.mpr (Or.inl ((mem_fstFinset A B).2 ⟨p, hp, hbot, hx'⟩))
    · exact mem_funion.mpr (Or.inr ((mem_fstFinset A B).2 ⟨p, hp, hbot, hx'⟩))
  · intro hx
    rcases mem_funion.mp hx with hx | hx
    · rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
      exact (mem_fstFinset A B).2 ⟨p, mem_funion.mpr (Or.inl hp), hbot, hx'⟩
    · rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
      exact (mem_fstFinset A B).2 ⟨p, mem_funion.mpr (Or.inr hp), hbot, hx'⟩

theorem sndFinset_funion (u v : Finset (ProdToken A B)) :
    sndFinset A B (u ∪' v) = sndFinset A B u ∪' sndFinset A B v := by
  ext y
  constructor
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
    rcases mem_funion.mp hp with hp | hp
    · exact mem_funion.mpr (Or.inl ((mem_sndFinset A B).2 ⟨p, hp, hbot, hy'⟩))
    · exact mem_funion.mpr (Or.inr ((mem_sndFinset A B).2 ⟨p, hp, hbot, hy'⟩))
  · intro hy
    rcases mem_funion.mp hy with hy | hy
    · rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
      exact (mem_sndFinset A B).2 ⟨p, mem_funion.mpr (Or.inl hp), hbot, hy'⟩
    · rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
      exact (mem_sndFinset A B).2 ⟨p, mem_funion.mpr (Or.inr hp), hbot, hy'⟩

/-- Consistency for the product system (Scott 6.1(iii)). -/
def ProdCon (u : Finset (ProdToken A B)) : Prop :=
  fstFinset A B u ∈ A.Con ∧ sndFinset A B u ∈ B.Con

/-- Entailment for the product system (Scott 6.1(iv'), (iv'')).
Includes `ProdCon` so both projections stay available for `ent_con`. -/
def ProdEnt (u : Finset (ProdToken A B)) (p : ProdToken A B) : Prop :=
  ProdCon A B u ∧
    (p.val.2 = B.bot → A.Ent (fstFinset A B u) p.val.1) ∧
      (p.val.1 = A.bot → B.Ent (sndFinset A B u) p.val.2)

/-- **Definition 6.1.** The product information system `A × B`. -/
def productSystem : InfoSys (ProdToken A B) where
  bot := prodBot A B
  Con := {u | ProdCon A B u}
  Ent := ProdEnt A B
  con_subset := by
    intro u v hu hv
    exact ⟨A.con_subset hu.1 (fstFinset_mono A B hv),
      B.con_subset hu.2 (sndFinset_mono A B hv)⟩
  con_sing := by
    intro p
    refine ⟨?_, ?_⟩
    · rcases p.property with h1 | h2
      · by_cases h2 : p.val.2 = B.bot
        · have hpeq : p = prodBot A B := Subtype.ext (Prod.ext h1 h2)
          subst hpeq
          rw [fstFinset_singleton_left A B (prodBot A B) rfl]
          exact A.con_sing A.bot
        · have hfst : fstFinset A B {p} = ∅ := by
            ext x
            constructor
            · intro hx
              rcases (mem_fstFinset A B).1 hx with ⟨q, hq, hbot', _⟩
              have hq' : q = p := Finset.mem_singleton.mp hq
              subst hq'
              exact False.elim (h2 hbot')
            · intro hx
              exact False.elim (Finset.notMem_empty x hx)
          rw [hfst]
          exact A.con_empty
      · rw [fstFinset_singleton_left A B p h2]
        exact A.con_sing p.val.1
    · rcases p.property with h1 | h2
      · rw [sndFinset_singleton_right A B p h1]
        exact B.con_sing p.val.2
      · by_cases h1 : p.val.1 = A.bot
        · have hpeq : p = prodBot A B := Subtype.ext (Prod.ext h1 h2)
          subst hpeq
          rw [sndFinset_singleton_right A B (prodBot A B) rfl]
          exact B.con_sing B.bot
        · have hsnd : sndFinset A B {p} = ∅ := by
            ext y
            constructor
            · intro hy
              rcases (mem_sndFinset A B).1 hy with ⟨q, hq, hbot', _⟩
              have hq' : q = p := Finset.mem_singleton.mp hq
              subst hq'
              exact False.elim (h1 hbot')
            · intro hy
              exact False.elim (Finset.notMem_empty y hy)
          rw [hsnd]
          exact B.con_empty
  ent_con := by
    intro u p ⟨⟨hfst, hsnd⟩, hL, hR⟩
    refine ⟨?_, ?_⟩
    · by_cases hp2 : p.val.2 = B.bot
      · rw [fstFinset_insert_left A B u p hp2]
        exact A.ent_con (hL hp2)
      · rw [fstFinset_insert_not_left A B u p hp2]
        exact hfst
    · by_cases hp1 : p.val.1 = A.bot
      · rw [sndFinset_insert_right A B u p hp1]
        exact B.ent_con (hR hp1)
      · rw [sndFinset_insert_not_right A B u p hp1]
        exact hsnd
  ent_bot := by
    intro u hu
    exact ⟨hu, fun _ => A.ent_bot hu.1, fun _ => B.ent_bot hu.2⟩
  ent_refl := by
    intro u p hu hp
    refine ⟨hu, ?_, ?_⟩
    · intro hbot
      exact A.ent_refl hu.1 ((mem_fstFinset A B).2 ⟨p, hp, hbot, rfl⟩)
    · intro hbot
      exact B.ent_refl hu.2 ((mem_sndFinset A B).2 ⟨p, hp, hbot, rfl⟩)
  ent_trans := by
    intro u v c hv hu hEnts hEntc
    refine ⟨hv, ?_, ?_⟩
    · intro hbot
      have hfst : ∀ y ∈ fstFinset A B u, A.Ent (fstFinset A B v) y := by
        intro y hy
        rcases (mem_fstFinset A B).1 hy with ⟨q, hq, hq2, rfl⟩
        exact (hEnts q hq).2.1 hq2
      exact A.ent_trans hv.1 hu.1 hfst (hEntc.2.1 hbot)
    · intro hbot
      have hsnd : ∀ y ∈ sndFinset A B u, B.Ent (sndFinset A B v) y := by
        intro y hy
        rcases (mem_sndFinset A B).1 hy with ⟨q, hq, hq1, rfl⟩
        exact (hEnts q hq).2.2 hq1
      exact B.ent_trans hv.2 hu.2 hsnd (hEntc.2.2 hbot)

end InfoSys

end Scott1982

-- Vendor 1982 — Scott1982.Proposition62 (from vendor/scott1982/Scott1982/Proposition62.lean)

/-!
# Proposition 6.2 — product projections and pairing

**Scott 1982, Proposition 6.2.** Approximable `fst`, `snd`, and unique pairing
`⟨f, g⟩` with `fst ∘ ⟨f, g⟩ = f` and `snd ∘ ⟨f, g⟩ = g`.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

/-- Left-tagged product token `(X, Δ_B)`. -/
def mkLeft (x : α) : ProdToken A B :=
  ⟨(x, B.bot), Or.inr rfl⟩

/-- Right-tagged product token `(Δ_A, Y)`. -/
def mkRight (y : β) : ProdToken A B :=
  ⟨(A.bot, y), Or.inl rfl⟩

private instance Proposition62_instLeftCommutativeMkLeftInsert :
    LeftCommutative fun x : α =>
      (insert (mkLeft A B x) : Finset (ProdToken A B) → Finset (ProdToken A B)) :=
  ⟨fun x y s => insert_comm' (mkLeft A B x) (mkLeft A B y) s⟩

private instance Proposition62_instLeftCommutativeMkRightInsert :
    LeftCommutative fun y : β =>
      (insert (mkRight A B y) : Finset (ProdToken A B) → Finset (ProdToken A B)) :=
  ⟨fun x y s => insert_comm' (mkRight A B x) (mkRight A B y) s⟩

/-- Embed a finite set of `A`-tokens as left product tokens. -/
def liftLeft (v : Finset α) : Finset (ProdToken A B) :=
  Multiset.foldr (fun x : α => insert (mkLeft A B x)) (∅ : Finset (ProdToken A B)) v.1

/-- Embed a finite set of `B`-tokens as right product tokens. -/
def liftRight (w : Finset β) : Finset (ProdToken A B) :=
  Multiset.foldr (fun y : β => insert (mkRight A B y)) (∅ : Finset (ProdToken A B)) w.1

private theorem Proposition62_mem_foldr_liftLeft (s : Multiset α) (p : ProdToken A B) :
    p ∈ Multiset.foldr (fun x : α => insert (mkLeft A B x)) (∅ : Finset (ProdToken A B)) s ↔
      ∃ x ∈ s, p = mkLeft A B x := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hp
      exact False.elim (Finset.notMem_empty p hp)
    · rintro ⟨_, hx, _⟩
      exact False.elim (by cases hx)
  · intro x t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (hp | ⟨y, hy, hp⟩)
      · exact ⟨x, Or.inl rfl, hp⟩
      · exact ⟨y, Or.inr hy, hp⟩
    · rintro ⟨y, hy, hp⟩
      rcases hy with rfl | hy
      · exact Or.inl hp
      · exact Or.inr ⟨y, hy, hp⟩

private theorem Proposition62_mem_foldr_liftRight (s : Multiset β) (p : ProdToken A B) :
    p ∈ Multiset.foldr (fun y : β => insert (mkRight A B y)) (∅ : Finset (ProdToken A B)) s ↔
      ∃ y ∈ s, p = mkRight A B y := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hp
      exact False.elim (Finset.notMem_empty p hp)
    · rintro ⟨_, hy, _⟩
      exact False.elim (by cases hy)
  · intro y t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (hp | ⟨z, hz, hp⟩)
      · exact ⟨y, Or.inl rfl, hp⟩
      · exact ⟨z, Or.inr hz, hp⟩
    · rintro ⟨z, hz, hp⟩
      rcases hz with rfl | hz
      · exact Or.inl hp
      · exact Or.inr ⟨z, hz, hp⟩
theorem mem_liftLeft {v : Finset α} {p : ProdToken A B} :
    p ∈ liftLeft A B v ↔ ∃ x ∈ v, p = mkLeft A B x := by
  unfold liftLeft
  exact Proposition62_mem_foldr_liftLeft A B v.1 p

theorem mem_liftRight {w : Finset β} {p : ProdToken A B} :
    p ∈ liftRight A B w ↔ ∃ y ∈ w, p = mkRight A B y := by
  unfold liftRight
  exact Proposition62_mem_foldr_liftRight A B w.1 p

theorem fstFinset_liftLeft (v : Finset α) : fstFinset A B (liftLeft A B v) = v := by
  ext x
  constructor
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
    rcases (mem_liftLeft A B).1 hp with ⟨y, hy, hp'⟩
    subst hp'
    exact (show y = x from hx').symm ▸ hy
  · intro hx
    exact (mem_fstFinset A B).2
      ⟨mkLeft A B x, (mem_liftLeft A B).2 ⟨x, hx, rfl⟩, rfl, rfl⟩

theorem sndFinset_liftRight (w : Finset β) : sndFinset A B (liftRight A B w) = w := by
  ext y
  constructor
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
    rcases (mem_liftRight A B).1 hp with ⟨z, hz, hp'⟩
    subst hp'
    exact (show z = y from hy').symm ▸ hz
  · intro hy
    exact (mem_sndFinset A B).2
      ⟨mkRight A B y, (mem_liftRight A B).2 ⟨y, hy, rfl⟩, rfl, rfl⟩

theorem sndFinset_liftLeft (v : Finset α) :
    sndFinset A B (liftLeft A B v) ⊆ ({B.bot} : Finset β) := by
  intro y hy
  rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
  rcases (mem_liftLeft A B).1 hp with ⟨x, _, hp'⟩
  subst hp'
  -- mkLeft x has first component x; filter requires x = A.bot, and second is B.bot
  have : y = B.bot := hy'.symm
  exact Finset.mem_singleton.mpr this

theorem fstFinset_liftRight (w : Finset β) :
    fstFinset A B (liftRight A B w) ⊆ ({A.bot} : Finset α) := by
  intro x hx
  rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
  rcases (mem_liftRight A B).1 hp with ⟨y, _, hp'⟩
  subst hp'
  have : x = A.bot := hx'.symm
  exact Finset.mem_singleton.mpr this

theorem ProdCon_liftLeft {v : Finset α} (hv : v ∈ A.Con) :
    ProdCon A B (liftLeft A B v) := by
  refine ⟨?_, ?_⟩
  · rw [fstFinset_liftLeft]
    exact hv
  · exact B.con_subset (B.con_sing B.bot) (sndFinset_liftLeft A B v)

theorem ProdCon_liftRight {w : Finset β} (hw : w ∈ B.Con) :
    ProdCon A B (liftRight A B w) := by
  refine ⟨?_, ?_⟩
  · exact A.con_subset (A.con_sing A.bot) (fstFinset_liftRight A B w)
  · rw [sndFinset_liftRight]
    exact hw

theorem ProdCon_empty : ProdCon A B (∅ : Finset (ProdToken A B)) :=
  ⟨by rw [fstFinset_empty]; exact A.con_empty,
    by rw [sndFinset_empty]; exact B.con_empty⟩

/-- Product entailment of a set projects to component entailment on `fst`. -/
theorem entSet_fst_of_prodEntSet {u v : Finset (ProdToken A B)}
    (h : (productSystem A B).EntSet u v) :
    A.EntSet (fstFinset A B u) (fstFinset A B v) := by
  intro x hx
  rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, rfl⟩
  exact (h p hp).2.1 hbot

/-- Product entailment of a set projects to component entailment on `snd`. -/
theorem entSet_snd_of_prodEntSet {u v : Finset (ProdToken A B)}
    (h : (productSystem A B).EntSet u v) :
    B.EntSet (sndFinset A B u) (sndFinset A B v) := by
  intro y hy
  rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, rfl⟩
  exact (h p hp).2.2 hbot

namespace ApproximableMap

variable {C : InfoSys γ}

/-- **Proposition 6.2(1).** Approximable first projection. -/
def fstMap : ApproximableMap (productSystem A B) A where
  rel u v := u ∈ (productSystem A B).Con ∧ v ∈ A.Con ∧ A.EntSet (fstFinset A B u) v
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨ProdCon_empty A B, A.con_empty, by
    rw [fstFinset_empty]; exact A.entSet_empty ∅⟩
  union_right := by
    rintro u v v' ⟨hu, hv, huv⟩ ⟨_, hv', huv'⟩
    have hEnt : A.EntSet (fstFinset A B u) (v ∪' v') :=
      proposition_2_3_vi (sys := A) huv huv'
    have hBig : fstFinset A B u ∪' (v ∪' v') ∈ A.Con :=
      proposition_2_3_ii (sys := A) hu.1 hEnt
    have hCon : v ∪' v' ∈ A.Con :=
      A.con_subset hBig (subset_funion_right _ _)
    exact ⟨hu, hCon, hEnt⟩
  mono := by
    rintro u u' v v' ⟨hu, hv, huv⟩ hEntu hEntv hu' hv'
    refine ⟨hu', hv', ?_⟩
    exact proposition_2_3_iv A hu'.1 hv
      (proposition_2_3_iv A hu'.1 hu.1 (entSet_fst_of_prodEntSet A B hEntu) huv) hEntv

/-- **Proposition 6.2(2).** Approximable second projection. -/
def sndMap : ApproximableMap (productSystem A B) B where
  rel u w := u ∈ (productSystem A B).Con ∧ w ∈ B.Con ∧ B.EntSet (sndFinset A B u) w
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨ProdCon_empty A B, B.con_empty, by
    rw [sndFinset_empty]; exact B.entSet_empty ∅⟩
  union_right := by
    rintro u w w' ⟨hu, hw, huw⟩ ⟨_, hw', huw'⟩
    have hEnt : B.EntSet (sndFinset A B u) (w ∪' w') :=
      proposition_2_3_vi (sys := B) huw huw'
    have hBig : sndFinset A B u ∪' (w ∪' w') ∈ B.Con :=
      proposition_2_3_ii (sys := B) hu.2 hEnt
    have hCon : w ∪' w' ∈ B.Con :=
      B.con_subset hBig (subset_funion_right _ _)
    exact ⟨hu, hCon, hEnt⟩
  mono := by
    rintro u u' w w' ⟨hu, hw, huw⟩ hEntu hEntw hu' hw'
    refine ⟨hu', hw', ?_⟩
    exact proposition_2_3_iv B hu'.2 hw
      (proposition_2_3_iv B hu'.2 hu.2 (entSet_snd_of_prodEntSet A B hEntu) huw) hEntw

/-- Helper: `g` relates `s` to any subset of `{Δ_B}` once it relates to `∅`. -/
private theorem Proposition62_rel_bot_subset {D : InfoSys β} {s : Finset γ} {w : Finset β}
    (g : ApproximableMap C D) (hs : s ∈ C.Con)
    (hg : g.rel s (∅ : Finset β)) (hw : w ⊆ ({D.bot} : Finset β)) :
    g.rel s w := by
  have hwCon : w ∈ D.Con := D.con_subset (D.con_sing D.bot) hw
  have hEnt : D.EntSet (∅ : Finset β) w := by
    intro y hy
    have : y = D.bot := Finset.mem_singleton.mp (hw hy)
    subst this
    exact D.ent_bot D.con_empty
  exact g.mono hg (proposition_2_3_iii C hs) hEnt hs hwCon

/-- Helper: `f` relates `s` to any subset of `{Δ_A}` once it relates to `∅`. -/
private theorem Proposition62_rel_bot_subset_left {D : InfoSys α} {s : Finset γ} {v : Finset α}
    (f : ApproximableMap C D) (hs : s ∈ C.Con)
    (hf : f.rel s (∅ : Finset α)) (hv : v ⊆ ({D.bot} : Finset α)) :
    f.rel s v := by
  have hvCon : v ∈ D.Con := D.con_subset (D.con_sing D.bot) hv
  have hEnt : D.EntSet (∅ : Finset α) v := by
    intro x hx
    have : x = D.bot := Finset.mem_singleton.mp (hv hx)
    subst this
    exact D.ent_bot D.con_empty
  exact f.mono hf (proposition_2_3_iii C hs) hEnt hs hvCon

/-- **Proposition 6.2(3).** Pairing of approximable maps. -/
def pairMap (f : ApproximableMap C A) (g : ApproximableMap C B) :
    ApproximableMap C (productSystem A B) where
  rel s u := f.rel s (fstFinset A B u) ∧ g.rel s (sndFinset A B u)
  rel_dom h := f.rel_dom h.1
  rel_cod h := ⟨f.rel_cod h.1, g.rel_cod h.2⟩
  empty_rel := by
    rw [fstFinset_empty, sndFinset_empty]
    exact ⟨f.empty_rel, g.empty_rel⟩
  union_right := by
    rintro s u u' ⟨hf, hg⟩ ⟨hf', hg'⟩
    rw [fstFinset_funion A B u u', sndFinset_funion A B u u']
    exact ⟨f.union_right hf hf', g.union_right hg hg'⟩
  mono := by
    rintro s s' u u' ⟨hf, hg⟩ hEnts hEntu hs' hu'
    refine ⟨?_, ?_⟩
    · exact f.mono hf hEnts (entSet_fst_of_prodEntSet A B hEntu) hs' hu'.1
    · exact g.mono hg hEnts (entSet_snd_of_prodEntSet A B hEntu) hs' hu'.2

/-- Product elements are determined by their projections (Scott’s uniqueness lemma). -/
theorem element_eq_of_fst_snd (z z' : (productSystem A B).Element)
    (hfst : (fstMap A B).toElement z = (fstMap A B).toElement z')
    (hsnd : (sndMap A B).toElement z = (sndMap A B).toElement z') :
    z = z' := by
  apply le_antisymm
  · intro p hp
    have hpz : (↑({p} : Finset (ProdToken A B)) : Set _) ⊆ z.carrier := by
      intro q hq
      have : q = p := Finset.mem_singleton.mp (Finset.mem_coe.1 hq)
      subst this
      exact hp
    have hCon : ProdCon A B {p} := z.consistent {p} hpz
    rcases p.property with h1 | h2
    · -- right-tagged (or bottom): use `snd`
      have hy : p.val.2 ∈ ((sndMap A B).toElement z).carrier := by
        refine ⟨{p}, hpz, ?_⟩
        refine ⟨hCon, B.con_sing p.val.2, ?_⟩
        intro y hy
        have : y = p.val.2 := Finset.mem_singleton.mp hy
        subst this
        exact B.ent_refl hCon.2 ((mem_sndFinset A B).2 ⟨p, Finset.mem_singleton_self p, h1, rfl⟩)
      have hy' : p.val.2 ∈ ((sndMap A B).toElement z').carrier := by
        rw [← hsnd]
        exact hy
      rcases hy' with ⟨u, hu, ⟨huCon, _, hEnt⟩⟩
      have hEntp : (productSystem A B).Ent u p := by
        refine ⟨huCon, ?_, ?_⟩
        · intro _
          simpa [h1] using A.ent_bot huCon.1
        · intro _
          exact hEnt p.val.2 (Finset.mem_singleton_self _)
      exact z'.closed u p hu hEntp
    · -- left-tagged: use `fst`
      have hx : p.val.1 ∈ ((fstMap A B).toElement z).carrier := by
        refine ⟨{p}, hpz, ?_⟩
        refine ⟨hCon, A.con_sing p.val.1, ?_⟩
        intro x hx
        have : x = p.val.1 := Finset.mem_singleton.mp hx
        subst this
        exact A.ent_refl hCon.1 ((mem_fstFinset A B).2 ⟨p, Finset.mem_singleton_self p, h2, rfl⟩)
      have hx' : p.val.1 ∈ ((fstMap A B).toElement z').carrier := by
        rw [← hfst]
        exact hx
      rcases hx' with ⟨u, hu, ⟨huCon, _, hEnt⟩⟩
      have hEntp : (productSystem A B).Ent u p := by
        refine ⟨huCon, ?_, ?_⟩
        · intro _
          exact hEnt p.val.1 (Finset.mem_singleton_self _)
        · intro _
          simpa [h2] using B.ent_bot huCon.2
      exact z'.closed u p hu hEntp
  · intro p hp
    have hpz : (↑({p} : Finset (ProdToken A B)) : Set _) ⊆ z'.carrier := by
      intro q hq
      have : q = p := Finset.mem_singleton.mp (Finset.mem_coe.1 hq)
      subst this
      exact hp
    have hCon : ProdCon A B {p} := z'.consistent {p} hpz
    rcases p.property with h1 | h2
    · have hy : p.val.2 ∈ ((sndMap A B).toElement z').carrier := by
        refine ⟨{p}, hpz, ?_⟩
        refine ⟨hCon, B.con_sing p.val.2, ?_⟩
        intro y hy
        have : y = p.val.2 := Finset.mem_singleton.mp hy
        subst this
        exact B.ent_refl hCon.2 ((mem_sndFinset A B).2 ⟨p, Finset.mem_singleton_self p, h1, rfl⟩)
      have hy' : p.val.2 ∈ ((sndMap A B).toElement z).carrier := by
        rw [hsnd]
        exact hy
      rcases hy' with ⟨u, hu, ⟨huCon, _, hEnt⟩⟩
      have hEntp : (productSystem A B).Ent u p := by
        refine ⟨huCon, ?_, ?_⟩
        · intro _
          simpa [h1] using A.ent_bot huCon.1
        · intro _
          exact hEnt p.val.2 (Finset.mem_singleton_self _)
      exact z.closed u p hu hEntp
    · have hx : p.val.1 ∈ ((fstMap A B).toElement z').carrier := by
        refine ⟨{p}, hpz, ?_⟩
        refine ⟨hCon, A.con_sing p.val.1, ?_⟩
        intro x hx
        have : x = p.val.1 := Finset.mem_singleton.mp hx
        subst this
        exact A.ent_refl hCon.1 ((mem_fstFinset A B).2 ⟨p, Finset.mem_singleton_self p, h2, rfl⟩)
      have hx' : p.val.1 ∈ ((fstMap A B).toElement z).carrier := by
        rw [hfst]
        exact hx
      rcases hx' with ⟨u, hu, ⟨huCon, _, hEnt⟩⟩
      have hEntp : (productSystem A B).Ent u p := by
        refine ⟨huCon, ?_, ?_⟩
        · intro _
          exact hEnt p.val.1 (Finset.mem_singleton_self _)
        · intro _
          simpa [h2] using B.ent_bot huCon.2
      exact z.closed u p hu hEntp

/-- `fst ∘ ⟨f, g⟩ = f`. -/
theorem comp_fstMap_pairMap (f : ApproximableMap C A) (g : ApproximableMap C B) :
    comp (fstMap A B) (pairMap A B f g) = f := by
  refine ApproximableMap.ext fun s v => ?_
  constructor
  · rintro ⟨u, ⟨hf, hg⟩, ⟨hu, hv, hEnt⟩⟩
    exact f.mono hf (proposition_2_3_iii C (f.rel_dom hf)) hEnt (f.rel_dom hf) hv
  · intro hf
    refine ⟨liftLeft A B v, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [fstFinset_liftLeft]
        exact hf
      · have hs : s ∈ C.Con := f.rel_dom hf
        have hg0 : g.rel s (∅ : Finset β) :=
          g.mono g.empty_rel (C.entSet_empty s) (B.entSet_empty ∅) hs B.con_empty
        exact Proposition62_rel_bot_subset g hs hg0 (sndFinset_liftLeft A B v)
    · refine ⟨ProdCon_liftLeft A B (f.rel_cod hf), f.rel_cod hf, ?_⟩
      rw [fstFinset_liftLeft]
      exact proposition_2_3_iii A (f.rel_cod hf)

/-- `snd ∘ ⟨f, g⟩ = g`. -/
theorem comp_sndMap_pairMap (f : ApproximableMap C A) (g : ApproximableMap C B) :
    comp (sndMap A B) (pairMap A B f g) = g := by
  refine ApproximableMap.ext fun s w => ?_
  constructor
  · rintro ⟨u, ⟨hf, hg⟩, ⟨hu, hw, hEnt⟩⟩
    exact g.mono hg (proposition_2_3_iii C (g.rel_dom hg)) hEnt (g.rel_dom hg) hw
  · intro hg
    refine ⟨liftRight A B w, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · have hs : s ∈ C.Con := g.rel_dom hg
        have hf0 : f.rel s (∅ : Finset α) :=
          f.mono f.empty_rel (C.entSet_empty s) (A.entSet_empty ∅) hs A.con_empty
        exact Proposition62_rel_bot_subset_left f hs hf0 (fstFinset_liftRight A B w)
      · rw [sndFinset_liftRight]
        exact hg
    · refine ⟨ProdCon_liftRight A B (g.rel_cod hg), g.rel_cod hg, ?_⟩
      rw [sndFinset_liftRight]
      exact proposition_2_3_iii B (g.rel_cod hg)

/-- Uniqueness of pairing (Scott Prop 6.2). -/
theorem pairMap_unique (f : ApproximableMap C A) (g : ApproximableMap C B)
    (h : ApproximableMap C (productSystem A B))
    (hfst : comp (fstMap A B) h = f) (hsnd : comp (sndMap A B) h = g) :
    h = pairMap A B f g :=
  (ext_iff_toElement h (pairMap A B f g)).2 fun x =>
    element_eq_of_fst_snd A B (h.toElement x) ((pairMap A B f g).toElement x)
      (by
        have h1 : (fstMap A B).toElement (h.toElement x) = f.toElement x := by
          rw [← comp_toElement, hfst]
        have h2 : (fstMap A B).toElement ((pairMap A B f g).toElement x) = f.toElement x := by
          rw [← comp_toElement, comp_fstMap_pairMap]
        exact h1.trans h2.symm)
      (by
        have h1 : (sndMap A B).toElement (h.toElement x) = g.toElement x := by
          rw [← comp_toElement, hsnd]
        have h2 : (sndMap A B).toElement ((pairMap A B f g).toElement x) = g.toElement x := by
          rw [← comp_toElement, comp_sndMap_pairMap]
        exact h1.trans h2.symm)

end ApproximableMap

end InfoSys

end Scott1982

-- Vendor 1982 — Scott1982.Theorem72 (from vendor/scott1982/Scott1982/Theorem72.lean)

/-!
# Theorem 7.2 — function space elements, apply, and curry

**Scott 1982, Theorem 7.2.** Approximable maps `A → B` are exactly the elements of
`|A → B|`. There is approximable `apply : (B → C) × B → C` with `apply(g,y) = g(y)`,
and for each `h : A × B → C` a unique `curry h : A → (B → C)` satisfying
`h = apply ∘ ⟨(curry h) ∘ fst, snd⟩`.

(`A → B` as an `InfoSys` is already Def 7.1 / `functionSystem`.)
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

/-- Consistency of a packaged function-space token. -/
theorem mkFunToken_property (u : Finset α) (v : Finset β) (hu : u ∈ A.Con) (hv : v ∈ B.Con) :
    u ∈ A.Con ∧ v ∈ B.Con :=
  ⟨hu, hv⟩

/-- Package a consistent pair as a function-space token. -/
def mkFunToken (u : Finset α) (v : Finset β) (hu : u ∈ A.Con) (hv : v ∈ B.Con) :
    FunToken A B :=
  ⟨(u, v), mkFunToken_property A B u v hu hv⟩

theorem mkFunToken_eq (p : FunToken A B) :
    mkFunToken A B p.val.1 p.val.2 p.property.1 p.property.2 = p :=
  Subtype.ext rfl

private theorem Theorem72_funion_self (u : Finset α) : u ∪' u = u := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h <;> exact h
  · intro hx
    exact mem_funion.mpr (Or.inl hx)

private theorem funion_comm_β (u v : Finset β) : u ∪' v = v ∪' u := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inr h)
    · exact mem_funion.mpr (Or.inl h)
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inr h)
    · exact mem_funion.mpr (Or.inl h)

theorem rel_input_output_union (f : ApproximableMap A B)
    (s : Finset (FunToken A B))
    (hrel : ∀ q ∈ s, f.rel q.val.1 q.val.2)
    (hin : funInputUnion A B s ∈ A.Con) :
    f.rel (funInputUnion A B s) (funOutputUnion A B s) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [funInputUnion_empty, funOutputUnion_empty]
    exact f.empty_rel
  | insert q s' _hq ih =>
    have hrel' : ∀ r ∈ s', f.rel r.val.1 r.val.2 := fun r hr =>
      hrel r (Finset.mem_insert_of_mem hr)
    have hin' : funInputUnion A B s' ∈ A.Con :=
      A.con_subset hin (by
        rw [funInputUnion_insert]
        exact subset_funion_right _ _)
    have ih' := ih hrel' hin'
    have hqrel : f.rel q.val.1 q.val.2 := hrel q (Finset.mem_insert_self q s')
    have hinU : q.val.1 ∪' funInputUnion A B s' ∈ A.Con := by
      rwa [funInputUnion_insert] at hin
    have hEnt_q : A.EntSet (q.val.1 ∪' funInputUnion A B s') q.val.1 :=
      fun x hx => A.ent_refl hinU (subset_funion_left _ _ hx)
    have hEnt_s : A.EntSet (q.val.1 ∪' funInputUnion A B s') (funInputUnion A B s') :=
      fun x hx => A.ent_refl hinU (subset_funion_right _ _ hx)
    have h1 : f.rel (q.val.1 ∪' funInputUnion A B s') q.val.2 :=
      f.mono hqrel hEnt_q (proposition_2_3_iii B q.property.2) hinU q.property.2
    have h2 : f.rel (q.val.1 ∪' funInputUnion A B s') (funOutputUnion A B s') :=
      f.mono ih' hEnt_s (proposition_2_3_iii B (f.rel_cod ih')) hinU (f.rel_cod ih')
    rw [funInputUnion_insert, funOutputUnion_insert]
    exact f.union_right h1 h2

open ApproximableMap

theorem funCon_of_approxMap (f : ApproximableMap A B) (w : Finset (FunToken A B))
    (hw : ∀ p ∈ w, f.rel p.val.1 p.val.2) : FunCon A B w :=
  fun s hs hin =>
    f.rel_cod (rel_input_output_union A B f s (fun q hq => hw q (hs hq)) hin)

/-- Consistency of the token-set of an approximable map. -/
theorem approxMap_toElement_consistent (f : ApproximableMap A B)
    (Y : Finset (FunToken A B))
    (hY : (Y : Set (FunToken A B)) ⊆ {p : FunToken A B | f.rel p.val.1 p.val.2}) :
    Y ∈ (functionSystem A B).Con :=
  funCon_of_approxMap A B f Y fun _ hp => hY (Finset.mem_coe.2 hp)

/-- Deductive closure of the token-set of an approximable map. -/
theorem approxMap_toElement_closed (f : ApproximableMap A B)
    (Y : Finset (FunToken A B)) (p : FunToken A B)
    (hY : (Y : Set (FunToken A B)) ⊆ {p : FunToken A B | f.rel p.val.1 p.val.2})
    (hEnt : (functionSystem A B).Ent Y p) :
    p ∈ {q : FunToken A B | f.rel q.val.1 q.val.2} := by
  obtain ⟨_hCon, s, hs, hEntIn, hEntOut⟩ := hEnt
  have hrel : ∀ q ∈ s, f.rel q.val.1 q.val.2 := fun q hq =>
    hY (Finset.mem_coe.2 (hs hq))
  have hin_s : funInputUnion A B s ∈ A.Con :=
    A.con_subset
      (proposition_2_3_ii A p.property.1 (entSet_inputUnion_of_ent A B hEntIn))
      (subset_funion_right _ _)
  have hIO := rel_input_output_union A B f s hrel hin_s
  have hU : f.rel p.val.1 (funOutputUnion A B s) :=
    f.mono hIO (entSet_inputUnion_of_ent A B hEntIn)
      (proposition_2_3_iii B (f.rel_cod hIO)) p.property.1 (f.rel_cod hIO)
  exact f.mono hU (proposition_2_3_iii A p.property.1) hEntOut p.property.1 p.property.2

/-- **Theorem 7.2.** Approximable map as an element of `|A → B|`. -/
def approxMap_toElement (f : ApproximableMap A B) : (functionSystem A B).Element where
  carrier := {p : FunToken A B | f.rel p.val.1 p.val.2}
  consistent := approxMap_toElement_consistent A B f
  closed := approxMap_toElement_closed A B f

theorem mem_approxMap_toElement (f : ApproximableMap A B) {p : FunToken A B} :
    p ∈ (approxMap_toElement A B f).carrier ↔ f.rel p.val.1 p.val.2 :=
  Iff.rfl

/-- Domain of the relation recovered from a function-space element. -/
theorem element_toApproxMap_rel_dom (x : (functionSystem A B).Element) :
    ∀ {u : Finset α} {v : Finset β},
      (∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier) →
      u ∈ A.Con :=
  fun ⟨hu, _, _⟩ => hu

/-- Codomain of the relation recovered from a function-space element. -/
theorem element_toApproxMap_rel_cod (x : (functionSystem A B).Element) :
    ∀ {u : Finset α} {v : Finset β},
      (∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier) →
      v ∈ B.Con :=
  fun ⟨_, hv, _⟩ => hv

/-- The empty pair is related. -/
theorem element_toApproxMap_empty_rel (x : (functionSystem A B).Element) :
    ∃ (hu : (∅ : Finset α) ∈ A.Con) (hv : (∅ : Finset β) ∈ B.Con),
      mkFunToken A B ∅ ∅ hu hv ∈ x.carrier := by
  refine ⟨A.con_empty, B.con_empty, ?_⟩
  change funBot A B ∈ x.carrier
  exact factoid_3_2 (functionSystem A B) x

/-- Output-union of two related pairs remains related. -/
theorem element_toApproxMap_union_right (x : (functionSystem A B).Element) :
    ∀ {u : Finset α} {v v' : Finset β},
      (∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier) →
      (∃ (hu : u ∈ A.Con) (hv : v' ∈ B.Con), mkFunToken A B u v' hu hv ∈ x.carrier) →
      ∃ (hu : u ∈ A.Con) (hv : v ∪' v' ∈ B.Con),
        mkFunToken A B u (v ∪' v') hu hv ∈ x.carrier := by
  rintro u v v' ⟨hu, hv, hp⟩ ⟨hu', hv', hq⟩
  have hvU : v ∪' v' ∈ B.Con := by
    have hCon : FunCon A B
        (insert (mkFunToken A B u v' hu' hv') {mkFunToken A B u v hu hv}) := by
      apply x.consistent
      intro r hr
      rcases Finset.mem_insert.mp (Finset.mem_coe.1 hr) with rfl | hr
      · exact hq
      · have : r = mkFunToken A B u v hu hv := Finset.mem_singleton.mp hr
        subst this
        exact hp
    have hin : funInputUnion A B
        (insert (mkFunToken A B u v' hu' hv') {mkFunToken A B u v hu hv}) ∈ A.Con := by
      rw [funInputUnion_insert, funInputUnion_singleton]
      change u ∪' u ∈ A.Con
      rw [Theorem72_funion_self]
      exact hu
    have hout := hCon _ (Finset.Subset.refl _) hin
    rw [funOutputUnion_insert, funOutputUnion_singleton, funion_comm_β] at hout
    exact hout
  refine ⟨hu, hvU, ?_⟩
  let p := mkFunToken A B u v hu hv
  let q := mkFunToken A B u v' hu' hv'
  let r := mkFunToken A B u (v ∪' v') hu hvU
  let w : Finset (FunToken A B) := insert q {p}
  have hwsub : (↑w : Set _) ⊆ x.carrier := by
    intro t ht
    rcases Finset.mem_insert.mp (Finset.mem_coe.1 ht) with rfl | ht
    · exact hq
    · have : t = p := Finset.mem_singleton.mp ht
      subst this
      exact hp
  have hEnt : FunEnt A B w r := by
    refine ⟨x.consistent w hwsub, w, Finset.Subset.refl _, ?_, ?_⟩
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact proposition_2_3_iii A hu'
      · have : t = p := Finset.mem_singleton.mp ht
        subst this
        exact proposition_2_3_iii A hu
    · have houtEq : funOutputUnion A B w = v' ∪' v := by
        change funOutputUnion A B
          (insert (mkFunToken A B u v' hu' hv') {mkFunToken A B u v hu hv}) = v' ∪' v
        rw [funOutputUnion_insert, funOutputUnion_singleton]
        simp only [mkFunToken]
      rw [houtEq, funion_comm_β]
      exact proposition_2_3_iii B hvU
  exact x.closed w r hwsub hEnt

/-- The recovered relation is monotone for entailment. -/
theorem element_toApproxMap_mono (x : (functionSystem A B).Element) :
    ∀ {u u' : Finset α} {v v' : Finset β},
      (∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier) →
      A.EntSet u' u → B.EntSet v v' → u' ∈ A.Con → v' ∈ B.Con →
      ∃ (hu : u' ∈ A.Con) (hv : v' ∈ B.Con),
        mkFunToken A B u' v' hu hv ∈ x.carrier := by
  rintro u u' v v' ⟨hu, hv, hp⟩ hEntu hEntv hu' hv'
  refine ⟨hu', hv', ?_⟩
  let p := mkFunToken A B u v hu hv
  let r := mkFunToken A B u' v' hu' hv'
  have hwsub : (↑({p} : Finset (FunToken A B)) : Set _) ⊆ x.carrier := by
    intro t ht
    have : t = p := Finset.mem_singleton.mp (Finset.mem_coe.1 ht)
    subst this
    exact hp
  have hEnt : FunEnt A B {p} r := by
    refine ⟨x.consistent {p} hwsub, {p}, Finset.Subset.refl _, ?_, ?_⟩
    · intro t ht
      have : t = p := Finset.mem_singleton.mp ht
      subst this
      exact hEntu
    · rw [funOutputUnion_singleton]
      exact hEntv
  exact x.closed {p} r hwsub hEnt

/-- **Theorem 7.2.** Element of `|A → B|` as an approximable map. -/
def element_toApproxMap (x : (functionSystem A B).Element) : ApproximableMap A B where
  rel u v := ∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier
  rel_dom := element_toApproxMap_rel_dom A B x
  rel_cod := element_toApproxMap_rel_cod A B x
  empty_rel := element_toApproxMap_empty_rel A B x
  union_right := element_toApproxMap_union_right A B x
  mono := element_toApproxMap_mono A B x

theorem element_toApproxMap_approxMap_toElement (f : ApproximableMap A B) :
    element_toApproxMap A B (approxMap_toElement A B f) = f := by
  refine ApproximableMap.ext fun u v => ?_
  constructor
  · rintro ⟨hu, hv, hp⟩
    change f.rel u v at hp
    exact hp
  · intro hrel
    exact ⟨f.rel_dom hrel, f.rel_cod hrel, by
      change f.rel u v
      exact hrel⟩

theorem approxMap_toElement_element_toApproxMap (x : (functionSystem A B).Element) :
    approxMap_toElement A B (element_toApproxMap A B x) = x := by
  apply le_antisymm
  · intro p hp
    change (element_toApproxMap A B x).rel p.val.1 p.val.2 at hp
    obtain ⟨_, _, hmem⟩ := hp
    simpa [mkFunToken_eq A B p] using hmem
  · intro p hp
    change (element_toApproxMap A B x).rel p.val.1 p.val.2
    refine ⟨p.property.1, p.property.2, ?_⟩
    simpa [mkFunToken_eq A B p] using hp

/-- **Theorem 7.2.** Approximable `apply : (B → C) × B → C`. -/
def applyMap : ApproximableMap (productSystem (functionSystem B C) B) C where
  rel s t :=
    ∃ (hs : ProdCon (functionSystem B C) B s) (ht : t ∈ C.Con),
      FunEnt B C (fstFinset (functionSystem B C) B s)
        (mkFunToken B C (sndFinset (functionSystem B C) B s) t hs.2 ht)
  rel_dom := fun ⟨hs, _, _⟩ => hs
  rel_cod := fun ⟨_, ht, _⟩ => ht
  empty_rel := by
    have hs : ProdCon (functionSystem B C) B ∅ :=
      ⟨by rw [fstFinset_empty]; exact (functionSystem B C).con_empty,
        by rw [sndFinset_empty]; exact B.con_empty⟩
    refine ⟨hs, C.con_empty, ?_⟩
    have hfst : fstFinset (functionSystem B C) B (∅ : Finset _) = ∅ := fstFinset_empty _ _
    have hsnd : sndFinset (functionSystem B C) B (∅ : Finset _) = ∅ := sndFinset_empty _ _
    simp only [hfst, hsnd]
    exact (functionSystem B C).ent_bot (functionSystem B C).con_empty
  union_right := by
    rintro s t t' ⟨hs, ht, hEntt⟩ ⟨_, ht', hEntt'⟩
    obtain ⟨hw, s1, hs1, hIn1, hOut1⟩ := hEntt
    obtain ⟨_, s2, hs2, hIn2, hOut2⟩ := hEntt'
    have hsub : s1 ∪' s2 ⊆ fstFinset (functionSystem B C) B s :=
      funion_subset_iff.mpr ⟨hs1, hs2⟩
    have hin : funInputUnion B C (s1 ∪' s2) ∈ B.Con := by
      rw [funInputUnion_funion]
      have hEntU : B.EntSet (sndFinset (functionSystem B C) B s)
          (funInputUnion B C s1 ∪' funInputUnion B C s2) :=
        proposition_2_3_vi B
          (entSet_inputUnion_of_ent B C hIn1)
          (entSet_inputUnion_of_ent B C hIn2)
      exact B.con_subset (proposition_2_3_ii B hs.2 hEntU) (subset_funion_right _ _)
    have hout : funOutputUnion B C s1 ∪' funOutputUnion B C s2 ∈ C.Con := by
      have := hw _ hsub hin
      rwa [funOutputUnion_funion] at this
    have htt' : t ∪' t' ∈ C.Con := by
      have hEntt2 : C.EntSet (funOutputUnion B C s1 ∪' funOutputUnion B C s2) (t ∪' t') :=
        proposition_2_3_vi C
          (proposition_2_3_v C (C.con_subset hout (subset_funion_left _ _)) hout
            (subset_funion_left _ _) hOut1 (Finset.Subset.refl _))
          (proposition_2_3_v C (C.con_subset hout (subset_funion_right _ _)) hout
            (subset_funion_right _ _) hOut2 (Finset.Subset.refl _))
      exact C.con_subset (proposition_2_3_ii C hout hEntt2) (subset_funion_right _ _)
    refine ⟨hs, htt', hw, s1 ∪' s2, hsub, ?_, ?_⟩
    · intro q hq
      rcases mem_funion.mp hq with hq | hq
      · exact hIn1 q hq
      · exact hIn2 q hq
    · rw [funOutputUnion_funion]
      exact proposition_2_3_vi C
        (proposition_2_3_v C (C.con_subset hout (subset_funion_left _ _)) hout
          (subset_funion_left _ _) hOut1 (Finset.Subset.refl _))
        (proposition_2_3_v C (C.con_subset hout (subset_funion_right _ _)) hout
          (subset_funion_right _ _) hOut2 (Finset.Subset.refl _))
  mono := by
    rintro s s' t t' ⟨hs, ht, hEnt⟩ hEnts hEntt hs' ht'
    refine ⟨hs', ht', ?_⟩
    have hfst := entSet_fst_of_prodEntSet (functionSystem B C) B hEnts
    have hsnd := entSet_snd_of_prodEntSet (functionSystem B C) B hEnts
    have htok :
        (functionSystem B C).Ent (fstFinset (functionSystem B C) B s)
          (mkFunToken B C (sndFinset (functionSystem B C) B s) t hs.2 ht) := hEnt
    have hmid :
        (functionSystem B C).Ent (fstFinset (functionSystem B C) B s')
          (mkFunToken B C (sndFinset (functionSystem B C) B s) t hs.2 ht) :=
      (functionSystem B C).ent_trans hs'.1 hs.1 (fun y hy => hfst y hy) htok
    obtain ⟨hw', s1, hs1, hIn1, hOut1⟩ := hmid
    have hIn1' : ∀ q ∈ s1, B.EntSet (sndFinset (functionSystem B C) B s') q.val.1 :=
      fun q hq => proposition_2_3_iv B hs'.2 hs.2 hsnd (hIn1 q hq)
    have hin : funInputUnion B C s1 ∈ B.Con :=
      B.con_subset
        (proposition_2_3_ii B hs'.2 (entSet_inputUnion_of_ent B C hIn1'))
        (subset_funion_right _ _)
    have hout : funOutputUnion B C s1 ∈ C.Con := hw' s1 hs1 hin
    refine ⟨hw', s1, hs1, hIn1', ?_⟩
    exact proposition_2_3_iv C hout ht hOut1 hEntt

/-! ## Curry helpers -/

/-- Product token set encoding a pair of consistent sets `(u, v)`. -/
def liftPair (u : Finset α) (v : Finset β) : Finset (ProdToken A B) :=
  liftLeft A B u ∪' liftRight A B v

theorem liftLeft_funion (u u' : Finset α) :
    liftLeft A B (u ∪' u') = liftLeft A B u ∪' liftLeft A B u' := by
  ext p
  constructor
  · intro hp
    rcases (mem_liftLeft A B).1 hp with ⟨x, hx, rfl⟩
    rcases mem_funion.mp hx with hx | hx
    · exact mem_funion.mpr (Or.inl ((mem_liftLeft A B).2 ⟨x, hx, rfl⟩))
    · exact mem_funion.mpr (Or.inr ((mem_liftLeft A B).2 ⟨x, hx, rfl⟩))
  · intro hp
    rcases mem_funion.mp hp with hp | hp
    · rcases (mem_liftLeft A B).1 hp with ⟨x, hx, rfl⟩
      exact (mem_liftLeft A B).2 ⟨x, mem_funion.mpr (Or.inl hx), rfl⟩
    · rcases (mem_liftLeft A B).1 hp with ⟨x, hx, rfl⟩
      exact (mem_liftLeft A B).2 ⟨x, mem_funion.mpr (Or.inr hx), rfl⟩

theorem liftRight_funion (v v' : Finset β) :
    liftRight A B (v ∪' v') = liftRight A B v ∪' liftRight A B v' := by
  ext p
  constructor
  · intro hp
    rcases (mem_liftRight A B).1 hp with ⟨y, hy, rfl⟩
    rcases mem_funion.mp hy with hy | hy
    · exact mem_funion.mpr (Or.inl ((mem_liftRight A B).2 ⟨y, hy, rfl⟩))
    · exact mem_funion.mpr (Or.inr ((mem_liftRight A B).2 ⟨y, hy, rfl⟩))
  · intro hp
    rcases mem_funion.mp hp with hp | hp
    · rcases (mem_liftRight A B).1 hp with ⟨y, hy, rfl⟩
      exact (mem_liftRight A B).2 ⟨y, mem_funion.mpr (Or.inl hy), rfl⟩
    · rcases (mem_liftRight A B).1 hp with ⟨y, hy, rfl⟩
      exact (mem_liftRight A B).2 ⟨y, mem_funion.mpr (Or.inr hy), rfl⟩

theorem ProdCon_liftPair {u : Finset α} {v : Finset β}
    (hu : u ∈ A.Con) (hv : v ∈ B.Con) : ProdCon A B (liftPair A B u v) := by
  constructor
  · unfold liftPair
    rw [fstFinset_funion, fstFinset_liftLeft]
    have hEnt : A.EntSet u (fstFinset A B (liftRight A B v)) := fun x hx => by
      have : x = A.bot := Finset.mem_singleton.mp (fstFinset_liftRight A B v hx)
      subst this
      exact A.ent_bot hu
    exact proposition_2_3_ii A hu hEnt
  · unfold liftPair
    rw [sndFinset_funion, sndFinset_liftRight]
    have hEnt : B.EntSet v (sndFinset A B (liftLeft A B u)) := fun y hy => by
      have : y = B.bot := Finset.mem_singleton.mp (sndFinset_liftLeft A B u hy)
      subst this
      exact B.ent_bot hv
    have h := proposition_2_3_ii B hv hEnt
    rwa [funion_comm_β] at h

theorem fstFinset_liftPair (u : Finset α) (v : Finset β) :
    fstFinset A B (liftPair A B u v) =
      u ∪' fstFinset A B (liftRight A B v) := by
  unfold liftPair
  rw [fstFinset_funion, fstFinset_liftLeft]

theorem sndFinset_liftPair (u : Finset α) (v : Finset β) :
    sndFinset A B (liftPair A B u v) =
      sndFinset A B (liftLeft A B u) ∪' v := by
  unfold liftPair
  rw [sndFinset_funion, sndFinset_liftRight]

/-- Product entailment between lifted pairs from component entailments. -/
theorem entSet_liftPair {u u' : Finset α} {v v' : Finset β}
    (hu' : u' ∈ A.Con) (hv' : v' ∈ B.Con)
    (hEntu : A.EntSet u' u) (hEntv : B.EntSet v' v) :
    (productSystem A B).EntSet (liftPair A B u' v') (liftPair A B u v) := by
  intro p hp
  have hCon : ProdCon A B (liftPair A B u' v') := ProdCon_liftPair A B hu' hv'
  unfold liftPair at hp
  rcases mem_funion.mp hp with hp | hp
  · rcases (mem_liftLeft A B).1 hp with ⟨x, hx, rfl⟩
    refine ⟨hCon, ?_, ?_⟩
    · intro _
      have hsub : u' ⊆ fstFinset A B (liftPair A B u' v') := by
        intro z hz
        rw [fstFinset_liftPair]
        exact subset_funion_left _ _ hz
      exact A.ent_trans hCon.1 hu'
        (fun z hz => A.ent_refl hCon.1 (hsub hz)) (hEntu x hx)
    · intro _
      exact B.ent_bot hCon.2
  · rcases (mem_liftRight A B).1 hp with ⟨y, hy, rfl⟩
    refine ⟨hCon, ?_, ?_⟩
    · intro _
      exact A.ent_bot hCon.1
    · intro _
      have hsub : v' ⊆ sndFinset A B (liftPair A B u' v') := by
        intro z hz
        rw [sndFinset_liftPair]
        exact subset_funion_right _ _ hz
      exact B.ent_trans hCon.2 hv'
        (fun z hz => B.ent_refl hCon.2 (hsub hz)) (hEntv y hy)

/-- Combine pointwise `h`-relations along a finite set of function tokens. -/
theorem rel_of_funTokens (h : ApproximableMap (productSystem A B) C)
    (u : Finset α) (hu : u ∈ A.Con) (t : Finset (FunToken B C))
    (hps : ∀ p ∈ t, h.rel (liftPair A B u p.val.1) p.val.2)
    (hin : funInputUnion B C t ∈ B.Con) :
    h.rel (liftPair A B u (funInputUnion B C t)) (funOutputUnion B C t) := by
  induction t using Finset.induction_on with
  | empty =>
    rw [funInputUnion_empty, funOutputUnion_empty]
    have hdom : liftPair A B u ∅ ∈ (productSystem A B).Con :=
      ProdCon_liftPair A B hu B.con_empty
    exact h.mono h.empty_rel
      ((productSystem A B).entSet_empty _)
      (C.entSet_empty ∅) hdom C.con_empty
  | insert p t' hpnot ih =>
    have hps' : ∀ q ∈ t', h.rel (liftPair A B u q.val.1) q.val.2 :=
      fun q hq => hps q (Finset.mem_insert_of_mem hq)
    have hin' : funInputUnion B C t' ∈ B.Con :=
      B.con_subset hin (by
        rw [funInputUnion_insert]
        exact subset_funion_right _ _)
    have ih' := ih hps' hin'
    have hp : h.rel (liftPair A B u p.val.1) p.val.2 :=
      hps p (Finset.mem_insert_self p t')
    have hinU : p.val.1 ∪' funInputUnion B C t' ∈ B.Con := by
      rwa [funInputUnion_insert] at hin
    have hEnt_p : B.EntSet (p.val.1 ∪' funInputUnion B C t') p.val.1 :=
      fun y hy => B.ent_refl hinU (subset_funion_left _ _ hy)
    have hEnt_t : B.EntSet (p.val.1 ∪' funInputUnion B C t') (funInputUnion B C t') :=
      fun y hy => B.ent_refl hinU (subset_funion_right _ _ hy)
    have hdomU : liftPair A B u (p.val.1 ∪' funInputUnion B C t') ∈
        (productSystem A B).Con :=
      ProdCon_liftPair A B hu hinU
    have h1 : h.rel (liftPair A B u (p.val.1 ∪' funInputUnion B C t')) p.val.2 :=
      h.mono hp
        (entSet_liftPair A B hu hinU (proposition_2_3_iii A hu) hEnt_p)
        (proposition_2_3_iii C (h.rel_cod hp)) hdomU (h.rel_cod hp)
    have h2 : h.rel (liftPair A B u (p.val.1 ∪' funInputUnion B C t'))
        (funOutputUnion B C t') :=
      h.mono ih'
        (entSet_liftPair A B hu hinU (proposition_2_3_iii A hu) hEnt_t)
        (proposition_2_3_iii C (h.rel_cod ih')) hdomU (h.rel_cod ih')
    rw [funInputUnion_insert, funOutputUnion_insert]
    exact h.union_right h1 h2

theorem funCon_of_curry_pointwise (h : ApproximableMap (productSystem A B) C)
    {u : Finset α} (hu : u ∈ A.Con) {s : Finset (FunToken B C)}
    (hps : ∀ p ∈ s, h.rel (liftPair A B u p.val.1) p.val.2) :
    FunCon B C s :=
  fun t ht hin =>
    h.rel_cod (rel_of_funTokens A B C h u hu t (fun p hp => hps p (ht hp)) hin)

/-- **Theorem 7.2.** Approximable `curry h : A → (B → C)`. -/
def curryMap (h : ApproximableMap (productSystem A B) C) :
    ApproximableMap A (functionSystem B C) where
  rel u s :=
    u ∈ A.Con ∧ ∀ p ∈ s, h.rel (liftPair A B u p.val.1) p.val.2
  rel_dom hrel := hrel.1
  rel_cod hrel := funCon_of_curry_pointwise A B C h hrel.1 hrel.2
  empty_rel := ⟨A.con_empty, fun _ hp => False.elim (Finset.notMem_empty _ hp)⟩
  union_right := by
    rintro u s s' ⟨hu, hps⟩ ⟨_, hps'⟩
    refine ⟨hu, ?_⟩
    intro p hp
    rcases mem_funion.mp hp with hp | hp
    · exact hps p hp
    · exact hps' p hp
  mono := by
    rintro u u' s s' ⟨hu, hps⟩ hEntu hEnts hu' hs'
    refine ⟨hu', ?_⟩
    intro p hp
    -- FunEnt s p from EntSet
    have hEntp : FunEnt B C s p := hEnts p hp
    obtain ⟨_, t, ht, hIn, hOut⟩ := hEntp
    have hps_t : ∀ q ∈ t, h.rel (liftPair A B u q.val.1) q.val.2 :=
      fun q hq => hps q (ht hq)
    have hin : funInputUnion B C t ∈ B.Con :=
      B.con_subset
        (proposition_2_3_ii B p.property.1 (entSet_inputUnion_of_ent B C hIn))
        (subset_funion_right _ _)
    have hmid : h.rel (liftPair A B u (funInputUnion B C t)) (funOutputUnion B C t) :=
      rel_of_funTokens A B C h u hu t hps_t hin
    have hmid' : h.rel (liftPair A B u' p.val.1) (funOutputUnion B C t) :=
      h.mono hmid
        (entSet_liftPair A B hu' p.property.1 hEntu
          (entSet_inputUnion_of_ent B C hIn))
        (proposition_2_3_iii C (h.rel_cod hmid))
        (ProdCon_liftPair A B hu' p.property.1) (h.rel_cod hmid)
    exact h.mono hmid'
      (proposition_2_3_iii (productSystem A B) (ProdCon_liftPair A B hu' p.property.1))
      hOut (ProdCon_liftPair A B hu' p.property.1) p.property.2

/-- Product element `⟨x, y⟩` assembled from the two projections. -/
def pairElements (x : A.Element) (y : B.Element) : (productSystem A B).Element where
  carrier := {p : ProdToken A B |
    (p.val.2 = B.bot → p.val.1 ∈ x.carrier) ∧ (p.val.1 = A.bot → p.val.2 ∈ y.carrier)}
  consistent := by
    intro Y hY
    refine ⟨?_, ?_⟩
    · have hsub : ↑(fstFinset A B Y) ⊆ x.carrier := by
        intro a ha
        rcases (mem_fstFinset A B).1 ha with ⟨p, hp, hbot, rfl⟩
        exact (hY (Finset.mem_coe.2 hp)).1 hbot
      exact x.consistent _ hsub
    · have hsub : ↑(sndFinset A B Y) ⊆ y.carrier := by
        intro b hb
        rcases (mem_sndFinset A B).1 hb with ⟨p, hp, hbot, rfl⟩
        exact (hY (Finset.mem_coe.2 hp)).2 hbot
      exact y.consistent _ hsub
  closed := by
    intro Y p hY hEnt
    obtain ⟨hCon, hL, hR⟩ := hEnt
    refine ⟨?_, ?_⟩
    · intro hbot
      have hEntA : A.Ent (fstFinset A B Y) p.val.1 := hL hbot
      have hsub : ↑(fstFinset A B Y) ⊆ x.carrier := by
        intro a ha
        rcases (mem_fstFinset A B).1 ha with ⟨q, hq, hbot', rfl⟩
        exact (hY (Finset.mem_coe.2 hq)).1 hbot'
      exact x.closed _ _ hsub hEntA
    · intro hbot
      have hEntB : B.Ent (sndFinset A B Y) p.val.2 := hR hbot
      have hsub : ↑(sndFinset A B Y) ⊆ y.carrier := by
        intro b hb
        rcases (mem_sndFinset A B).1 hb with ⟨q, hq, hbot', rfl⟩
        exact (hY (Finset.mem_coe.2 hq)).2 hbot'
      exact y.closed _ _ hsub hEntB

theorem fstMap_pairElements (x : A.Element) (y : B.Element) :
    (fstMap A B).toElement (pairElements A B x y) = x := by
  apply le_antisymm
  · intro a ⟨s, hs, ⟨hCon, _, hEnt⟩⟩
    have hsub : ↑(fstFinset A B s) ⊆ x.carrier := by
      intro b hb
      rcases (mem_fstFinset A B).1 hb with ⟨p, hp, hbot, rfl⟩
      exact (hs (Finset.mem_coe.2 hp)).1 hbot
    exact x.closed _ a hsub (hEnt a (Finset.mem_singleton_self _))
  · intro a ha
    refine ⟨liftLeft A B {a}, ?_, ?_⟩
    · intro p hp
      rcases (mem_liftLeft A B).1 (Finset.mem_coe.1 hp) with ⟨b, hb, rfl⟩
      have : b = a := Finset.mem_singleton.mp hb
      subst this
      exact ⟨fun _ => ha, fun _ => factoid_3_2 B y⟩
    · refine ⟨ProdCon_liftLeft A B (A.con_sing a), A.con_sing a, ?_⟩
      rw [fstFinset_liftLeft]
      exact proposition_2_3_iii A (A.con_sing a)

theorem sndMap_pairElements (x : A.Element) (y : B.Element) :
    (sndMap A B).toElement (pairElements A B x y) = y := by
  apply le_antisymm
  · intro b ⟨s, hs, ⟨hCon, _, hEnt⟩⟩
    have hsub : ↑(sndFinset A B s) ⊆ y.carrier := by
      intro c hc
      rcases (mem_sndFinset A B).1 hc with ⟨p, hp, hbot, rfl⟩
      exact (hs (Finset.mem_coe.2 hp)).2 hbot
    exact y.closed _ b hsub (hEnt b (Finset.mem_singleton_self _))
  · intro b hb
    refine ⟨liftRight A B {b}, ?_, ?_⟩
    · intro p hp
      rcases (mem_liftRight A B).1 (Finset.mem_coe.1 hp) with ⟨c, hc, rfl⟩
      have : c = b := Finset.mem_singleton.mp hc
      subst this
      exact ⟨fun _ => factoid_3_2 A x, fun _ => hb⟩
    · refine ⟨ProdCon_liftRight A B (B.con_sing b), B.con_sing b, ?_⟩
      rw [sndFinset_liftRight]
      exact proposition_2_3_iii B (B.con_sing b)

/-- Tokens in `fstFinset s` for `s ⊆ ⟨x,y⟩` lie in `x`. -/
theorem mem_fst_of_subset_pairElements {x : A.Element} {y : B.Element}
    {s : Finset (ProdToken A B)}
    (hs : ↑s ⊆ (pairElements A B x y).carrier) {a : α}
    (ha : a ∈ fstFinset A B s) : a ∈ x.carrier := by
  have hCon : ProdCon A B s := (pairElements A B x y).consistent s hs
  have : a ∈ ((fstMap A B).toElement (pairElements A B x y)).carrier := by
    refine ⟨s, hs, ⟨hCon, A.con_sing a, ?_⟩⟩
    intro b hb
    have : b = a := Finset.mem_singleton.mp hb
    subst this
    exact A.ent_refl hCon.1 ha
  simpa [fstMap_pairElements] using this

/-- Tokens in `sndFinset s` for `s ⊆ ⟨x,y⟩` lie in `y`. -/
theorem mem_snd_of_subset_pairElements {x : A.Element} {y : B.Element}
    {s : Finset (ProdToken A B)}
    (hs : ↑s ⊆ (pairElements A B x y).carrier) {b : β}
    (hb : b ∈ sndFinset A B s) : b ∈ y.carrier := by
  have hCon : ProdCon A B s := (pairElements A B x y).consistent s hs
  have : b ∈ ((sndMap A B).toElement (pairElements A B x y)).carrier := by
    refine ⟨s, hs, ⟨hCon, B.con_sing b, ?_⟩⟩
    intro c hc
    have : c = b := Finset.mem_singleton.mp hc
    subst this
    exact B.ent_refl hCon.2 hb
  simpa [sndMap_pairElements] using this

theorem subset_pairElements_liftLeft {x : A.Element} {y : B.Element}
    {u : Finset α} (hu : ↑u ⊆ x.carrier) :
    ↑(liftLeft A B u) ⊆ (pairElements A B x y).carrier := by
  intro p hp
  rcases (mem_liftLeft A B).1 (Finset.mem_coe.1 hp) with ⟨a, ha, rfl⟩
  have hax : a ∈ x.carrier := hu (Finset.mem_coe.2 ha)
  have : a ∈ ((fstMap A B).toElement (pairElements A B x y)).carrier := by
    simpa [fstMap_pairElements] using hax
  rcases this with ⟨s, hs, ⟨hCon, _, hEnt⟩⟩
  exact (pairElements A B x y).closed s (mkLeft A B a) hs ⟨hCon,
    fun _ => hEnt a (Finset.mem_singleton_self _),
    fun _ => B.ent_bot hCon.2⟩

theorem subset_pairElements_liftRight {x : A.Element} {y : B.Element}
    {v : Finset β} (hv : ↑v ⊆ y.carrier) :
    ↑(liftRight A B v) ⊆ (pairElements A B x y).carrier := by
  intro p hp
  rcases (mem_liftRight A B).1 (Finset.mem_coe.1 hp) with ⟨b, hb, rfl⟩
  have hby : b ∈ y.carrier := hv (Finset.mem_coe.2 hb)
  have : b ∈ ((sndMap A B).toElement (pairElements A B x y)).carrier := by
    simpa [sndMap_pairElements] using hby
  rcases this with ⟨s, hs, ⟨hCon, _, hEnt⟩⟩
  exact (pairElements A B x y).closed s (mkRight A B b) hs ⟨hCon,
    fun _ => A.ent_bot hCon.1,
    fun _ => hEnt b (Finset.mem_singleton_self _)⟩

theorem subset_pairElements_liftPair {x : A.Element} {y : B.Element}
    {u : Finset α} {v : Finset β} (hu : ↑u ⊆ x.carrier) (hv : ↑v ⊆ y.carrier) :
    ↑(liftPair A B u v) ⊆ (pairElements A B x y).carrier := by
  intro p hp
  have hp' : p ∈ liftLeft A B u ∪' liftRight A B v := Finset.mem_coe.1 hp
  rcases mem_funion.mp hp' with hp | hp
  · exact subset_pairElements_liftLeft A B hu (Finset.mem_coe.2 hp)
  · exact subset_pairElements_liftRight A B hv (Finset.mem_coe.2 hp)

/-- **Theorem 7.2.** `apply(g, y) = g(y)`. -/
theorem applyMap_toElement (g : (functionSystem B C).Element) (y : B.Element) :
    (applyMap (B := B) (C := C)).toElement
      (pairElements (functionSystem B C) B g y) =
      (element_toApproxMap B C g).toElement y := by
  apply le_antisymm
  · intro Z ⟨s, hs, ⟨hCon, hZcon, hEnt⟩⟩
    obtain ⟨hw, t, ht, hIn, hOut⟩ := hEnt
    have ht_sub : ↑t ⊆ g.carrier := by
      intro p hp
      exact mem_fst_of_subset_pairElements (functionSystem B C) B hs (ht (Finset.mem_coe.1 hp))
    have hsnd_sub : ↑(sndFinset (functionSystem B C) B s) ⊆ y.carrier := by
      intro b hb
      exact mem_snd_of_subset_pairElements (functionSystem B C) B hs hb
    have hin : funInputUnion B C t ∈ B.Con :=
      B.con_subset
        (proposition_2_3_ii B hCon.2 (entSet_inputUnion_of_ent B C hIn))
        (subset_funion_right _ _)
    have hin_sub : ↑(funInputUnion B C t) ⊆ y.carrier := by
      intro b hb
      rcases (mem_funInputUnion B C).1 (Finset.mem_coe.1 hb) with ⟨q, hq, hb'⟩
      exact y.closed _ b hsnd_sub (hIn q hq b hb')
    have hEntZ : FunEnt B C t
        (mkFunToken B C (funInputUnion B C t) {Z} hin (C.con_sing Z)) := by
      refine ⟨fun s' hs' hin' => hw s' (fun q hq => ht (hs' hq)) hin', t, Finset.Subset.refl _, ?_, hOut⟩
      intro q hq y' hy'
      exact B.ent_refl hin ((mem_funInputUnion B C).2 ⟨q, hq, hy'⟩)
    have hmem : mkFunToken B C (funInputUnion B C t) {Z} hin (C.con_sing Z) ∈ g.carrier :=
      g.closed t _ ht_sub hEntZ
    exact ⟨funInputUnion B C t, hin_sub, ⟨hin, C.con_sing Z, hmem⟩⟩
  · intro Z ⟨v, hv, ⟨hvCon, hZcon, hmem⟩⟩
    let p : FunToken B C := mkFunToken B C v {Z} hvCon hZcon
    have hp : p ∈ g.carrier := hmem
    let s := liftPair (functionSystem B C) B {p} v
    have hsCon : ProdCon (functionSystem B C) B s :=
      ProdCon_liftPair (functionSystem B C) B ((functionSystem B C).con_sing p) hvCon
    have hs_sub : ↑s ⊆ (pairElements (functionSystem B C) B g y).carrier :=
      subset_pairElements_liftPair (functionSystem B C) B
        (by
          intro q hq
          have : q = p := Finset.mem_singleton.mp (Finset.mem_coe.1 hq)
          subst this
          exact hp)
        hv
    refine ⟨s, hs_sub, ⟨hsCon, C.con_sing Z, ?_⟩⟩
    refine ⟨?_, {p}, ?_, ?_, ?_⟩
    · -- FunCon of fst s from g.consistent
      intro t ht hin
      have ht_sub : ↑t ⊆ g.carrier := by
        intro q hq
        exact mem_fst_of_subset_pairElements (functionSystem B C) B hs_sub (ht hq)
      exact (funCon_of_approxMap B C (element_toApproxMap B C g) t
        (fun q hq => ⟨q.property.1, q.property.2, by
          simpa [mkFunToken_eq] using ht_sub (Finset.mem_coe.2 hq)⟩)) t (Finset.Subset.refl _) hin
    · -- {p} ⊆ fst s
      intro q hq
      have : q = p := Finset.mem_singleton.mp hq
      subst this
      rw [show s = liftLeft (functionSystem B C) B {p} ∪' liftRight (functionSystem B C) B v from rfl]
      rw [fstFinset_funion, fstFinset_liftLeft]
      exact subset_funion_left _ _ (Finset.mem_singleton_self _)
    · -- snd s ⊢ v = p.input
      intro q hq
      have : q = p := Finset.mem_singleton.mp hq
      subst this
      intro b hb
      have hb' : b ∈ v := hb
      -- snd s = snd(liftLeft) ∪' v entails v
      have : b ∈ sndFinset (functionSystem B C) B s := by
        rw [sndFinset_liftPair]
        exact subset_funion_right _ _ hb'
      exact B.ent_refl hsCon.2 this
    · -- output {Z} ⊢ {Z}
      rw [funOutputUnion_singleton]
      exact proposition_2_3_iii C (C.con_sing Z)

/-- The uncurrying of `k : A → (B → C)`. -/
def uncurryMap (k : ApproximableMap A (functionSystem B C)) :
    ApproximableMap (productSystem A B) C :=
  comp (applyMap (B := B) (C := C))
    (pairMap (functionSystem B C) B (comp k (fstMap A B)) (sndMap A B))

/-- **Theorem 7.2.** `h = apply ∘ ⟨(curry h) ∘ fst, snd⟩`. -/
theorem uncurry_curryMap (h : ApproximableMap (productSystem A B) C) :
    uncurryMap A B C (curryMap A B C h) = h := by
  refine ApproximableMap.ext fun s w => ?_
  constructor
  · rintro ⟨m, ⟨hk, hsnd⟩, ⟨hCon, hw, hEnt⟩⟩
    -- hk : (curry h ∘ fst).rel s (fst m) i.e. ∃ v, fst.rel s v ∧ curry.rel v (fst m)
    obtain ⟨v, hfst, ⟨hv, hcurry⟩⟩ := hk
    obtain ⟨_, t, ht, hIn, hOut⟩ := hEnt
    -- Each q ∈ t is in fst m, and curry says h.rel (liftPair v q.1) q.2
    have hps : ∀ q ∈ t, h.rel (liftPair A B v q.val.1) q.val.2 :=
      fun q hq => hcurry q (ht hq)
    have hin : funInputUnion B C t ∈ B.Con :=
      B.con_subset
        (proposition_2_3_ii B hCon.2 (entSet_inputUnion_of_ent B C hIn))
        (subset_funion_right _ _)
    have hmid : h.rel (liftPair A B v (funInputUnion B C t)) (funOutputUnion B C t) :=
      rel_of_funTokens A B C h v hv t hps hin
    -- fst.rel s v means EntSet (fst s) v; snd.rel s (snd m) means EntSet (snd s) (snd m)
    -- and snd m ⊢ funInputUnion t
    have hEntIn : B.EntSet (sndFinset A B s) (funInputUnion B C t) :=
      proposition_2_3_iv B (hsnd.1.2) hin
        (proposition_2_3_iv B (hsnd.1.2) hCon.2 hsnd.2.2
          (entSet_inputUnion_of_ent B C hIn))
        (proposition_2_3_iii B hin)
    -- Actually hsnd : sndMap.rel s (snd m) = ⟨ProdCon s, snd m ∈ Con, EntSet (snd s) (snd m)⟩
    -- Simplify:
    have hs : s ∈ (productSystem A B).Con := hfst.1
    have hEntv : A.EntSet (fstFinset A B s) v := hfst.2.2
    have hEntsnd : B.EntSet (sndFinset A B s) (sndFinset (functionSystem B C) B m) := hsnd.2.2
    have hEntIn' : B.EntSet (sndFinset A B s) (funInputUnion B C t) :=
      proposition_2_3_iv B hs.2 hin
        (proposition_2_3_iv B hs.2 hCon.2 hEntsnd (entSet_inputUnion_of_ent B C hIn))
        (proposition_2_3_iii B hin)
    have hdom : liftPair A B (fstFinset A B s) (sndFinset A B s) ∈
        (productSystem A B).Con :=
      ProdCon_liftPair A B hs.1 hs.2
    -- Relate liftPair (fst s) (snd s) to liftPair v (inputUnion) via entSet_liftPair
    have hmid' : h.rel (liftPair A B (fstFinset A B s) (sndFinset A B s))
        (funOutputUnion B C t) :=
      h.mono hmid (entSet_liftPair A B hs.1 hs.2 hEntv hEntIn')
        (proposition_2_3_iii C (h.rel_cod hmid)) hdom (h.rel_cod hmid)
    -- Need: liftPair (fst s) (snd s) is "entailed by" s as product sets, or s relates via mono from a subset relation
    -- Key: s as product tokens "contains" the information of liftPair (fst s) (snd s)
    -- Use: EntSet s (liftPair (fst s) (snd s)) then mono of h from... wait h relates liftPair to output, need s h w.
    -- Show (productSystem).EntSet s (liftPair (fst s) (snd s))
    have hEntLift : (productSystem A B).EntSet s (liftPair A B (fstFinset A B s) (sndFinset A B s)) := by
      intro p hp
      unfold liftPair at hp
      rcases mem_funion.mp hp with hp | hp
      · rcases (mem_liftLeft A B).1 hp with ⟨a, ha, rfl⟩
        refine ⟨hs, ?_, ?_⟩
        · intro _
          exact A.ent_refl hs.1 ha
        · intro _
          exact B.ent_bot hs.2
      · rcases (mem_liftRight A B).1 hp with ⟨b, hb, rfl⟩
        refine ⟨hs, ?_, ?_⟩
        · intro _
          exact A.ent_bot hs.1
        · intro _
          exact B.ent_refl hs.2 hb
    exact h.mono hmid' hEntLift hOut hs hw
  · intro hh
    have hs : s ∈ (productSystem A B).Con := h.rel_dom hh
    have hw : w ∈ C.Con := h.rel_cod hh
    let tok : FunToken B C := mkFunToken B C (sndFinset A B s) w hs.2 hw
    have hLiftCon : ProdCon A B (liftPair A B (fstFinset A B s) (sndFinset A B s)) :=
      ProdCon_liftPair A B hs.1 hs.2
    have hEntLift : (productSystem A B).EntSet
        (liftPair A B (fstFinset A B s) (sndFinset A B s)) s := by
      intro p hp
      rcases p.property with hR | hL
      · refine ⟨hLiftCon, fun _ => ?_, fun _ => ?_⟩
        · rw [hR]; exact A.ent_bot hLiftCon.1
        · have hb : p.val.2 ∈ sndFinset A B s :=
            (mem_sndFinset A B).2 ⟨p, hp, hR, rfl⟩
          have hb' : p.val.2 ∈
              sndFinset A B (liftPair A B (fstFinset A B s) (sndFinset A B s)) := by
            rw [sndFinset_liftPair]
            exact subset_funion_right _ _ hb
          exact B.ent_refl hLiftCon.2 hb'
      · refine ⟨hLiftCon, fun _ => ?_, fun _ => ?_⟩
        · have ha : p.val.1 ∈ fstFinset A B s :=
            (mem_fstFinset A B).2 ⟨p, hp, hL, rfl⟩
          have ha' : p.val.1 ∈
              fstFinset A B (liftPair A B (fstFinset A B s) (sndFinset A B s)) := by
            rw [fstFinset_liftPair]
            exact subset_funion_left _ _ ha
          exact A.ent_refl hLiftCon.1 ha'
        · rw [hL]; exact B.ent_bot hLiftCon.2
    have hrel : h.rel (liftPair A B (fstFinset A B s) (sndFinset A B s)) w :=
      h.mono hh hEntLift (proposition_2_3_iii C hw) hLiftCon hw
    have hcurry_tok : (curryMap A B C h).rel (fstFinset A B s) {tok} := by
      refine ⟨hs.1, ?_⟩
      intro p hp
      have : p = tok := Finset.mem_singleton.mp hp
      subst this
      exact hrel
    let m := liftPair (functionSystem B C) B {tok} (sndFinset A B s)
    have hmCon : ProdCon (functionSystem B C) B m :=
      ProdCon_liftPair (functionSystem B C) B ((functionSystem B C).con_sing tok) hs.2
    have hfst_m : fstFinset (functionSystem B C) B m =
        {tok} ∪' fstFinset (functionSystem B C) B
          (liftRight (functionSystem B C) B (sndFinset A B s)) := by
      change fstFinset _ _ (liftLeft _ _ {tok} ∪' liftRight _ _ _) = _
      rw [fstFinset_funion, fstFinset_liftLeft]
    have hsnd_m : sndFinset (functionSystem B C) B m =
        sndFinset (functionSystem B C) B (liftLeft (functionSystem B C) B {tok}) ∪'
          sndFinset A B s := by
      change sndFinset _ _ (liftLeft _ _ {tok} ∪' liftRight _ _ _) = _
      rw [sndFinset_funion, sndFinset_liftRight]
    have hcurry_fst : (curryMap A B C h).rel (fstFinset A B s)
        (fstFinset (functionSystem B C) B m) := by
      refine ⟨hs.1, ?_⟩
      intro p hp
      have hp' : p ∈ {tok} ∪' fstFinset (functionSystem B C) B
          (liftRight (functionSystem B C) B (sndFinset A B s)) := by
        rw [hfst_m] at hp
        exact hp
      rcases mem_funion.mp hp' with hp' | hp'
      · have : p = tok := Finset.mem_singleton.mp hp'
        subst this
        exact hrel
      · have hpbot : p = (functionSystem B C).bot :=
          Finset.mem_singleton.mp
            (fstFinset_liftRight (functionSystem B C) B (sndFinset A B s) hp')
        subst hpbot
        change h.rel (liftPair A B (fstFinset A B s) (funBot B C).val.1) (funBot B C).val.2
        simp only [funBot]
        exact h.mono h.empty_rel ((productSystem A B).entSet_empty _)
          (C.entSet_empty ∅) (ProdCon_liftPair A B hs.1 B.con_empty) C.con_empty
    refine ⟨m, ⟨?_, ?_⟩, ?_⟩
    · -- (curry ∘ fst).rel s (fst m)
      exact ⟨fstFinset A B s, ⟨hs, hs.1, proposition_2_3_iii A hs.1⟩, hcurry_fst⟩
    · -- snd.rel s (snd m)
      refine ⟨hs, hmCon.2, ?_⟩
      intro b hb
      have hb' : b ∈
          sndFinset (functionSystem B C) B (liftLeft (functionSystem B C) B {tok}) ∪'
            sndFinset A B s := by
        rwa [hsnd_m] at hb
      rcases mem_funion.mp hb' with hb' | hb'
      · have : b = B.bot := Finset.mem_singleton.mp
          (sndFinset_liftLeft (functionSystem B C) B {tok} hb')
        subst this
        exact B.ent_bot hs.2
      · exact B.ent_refl hs.2 hb'
    · -- apply.rel m w
      refine ⟨hmCon, hw, ?_⟩
      refine ⟨(curryMap A B C h).rel_cod hcurry_fst, {tok}, ?_, ?_, ?_⟩
      · intro q hq
        have : q = tok := Finset.mem_singleton.mp hq
        subst this
        have : tok ∈ fstFinset (functionSystem B C) B m := by
          rw [hfst_m]
          exact subset_funion_left _ _ (Finset.mem_singleton_self _)
        exact this
      · intro q hq
        have : q = tok := Finset.mem_singleton.mp hq
        subst this
        intro b hb
        have : b ∈ sndFinset (functionSystem B C) B m := by
          rw [hsnd_m]
          exact subset_funion_right _ _ hb
        exact B.ent_refl hmCon.2 this
      · rw [funOutputUnion_singleton]
        exact proposition_2_3_iii C hw

/-- **Theorem 7.2.** `curry` is the unique map satisfying the universal equation. -/
theorem curryMap_unique (h : ApproximableMap (productSystem A B) C)
    (k : ApproximableMap A (functionSystem B C))
    (huniv : uncurryMap A B C k = h) :
    k = curryMap A B C h := by
  have hk : uncurryMap A B C k = uncurryMap A B C (curryMap A B C h) := by
    rw [huniv, uncurry_curryMap]
  refine (ext_iff_toElement k (curryMap A B C h)).2 fun x => ?_
  have happly : ∀ y : B.Element,
      (element_toApproxMap B C (k.toElement x)).toElement y =
        (element_toApproxMap B C ((curryMap A B C h).toElement x)).toElement y := by
    intro y
    have hpair_k :
        (pairMap (functionSystem B C) B (comp k (fstMap A B)) (sndMap A B)).toElement
          (pairElements A B x y) =
        pairElements (functionSystem B C) B (k.toElement x) y := by
      apply element_eq_of_fst_snd (functionSystem B C) B
      · have h1 : (fstMap (functionSystem B C) B).toElement
            ((pairMap (functionSystem B C) B (comp k (fstMap A B)) (sndMap A B)).toElement
              (pairElements A B x y)) = k.toElement x := by
          rw [← comp_toElement, comp_fstMap_pairMap, comp_toElement, fstMap_pairElements]
        exact h1.trans (fstMap_pairElements (functionSystem B C) B (k.toElement x) y).symm
      · have h1 : (sndMap (functionSystem B C) B).toElement
            ((pairMap (functionSystem B C) B (comp k (fstMap A B)) (sndMap A B)).toElement
              (pairElements A B x y)) = y := by
          rw [← comp_toElement, comp_sndMap_pairMap, sndMap_pairElements]
        exact h1.trans (sndMap_pairElements (functionSystem B C) B (k.toElement x) y).symm
    have hpair_c :
        (pairMap (functionSystem B C) B
            (comp (curryMap A B C h) (fstMap A B)) (sndMap A B)).toElement
          (pairElements A B x y) =
        pairElements (functionSystem B C) B ((curryMap A B C h).toElement x) y := by
      apply element_eq_of_fst_snd (functionSystem B C) B
      · have h1 : (fstMap (functionSystem B C) B).toElement
            ((pairMap (functionSystem B C) B
                (comp (curryMap A B C h) (fstMap A B)) (sndMap A B)).toElement
              (pairElements A B x y)) = (curryMap A B C h).toElement x := by
          rw [← comp_toElement, comp_fstMap_pairMap, comp_toElement, fstMap_pairElements]
        exact h1.trans
          (fstMap_pairElements (functionSystem B C) B ((curryMap A B C h).toElement x) y).symm
      · have h1 : (sndMap (functionSystem B C) B).toElement
            ((pairMap (functionSystem B C) B
                (comp (curryMap A B C h) (fstMap A B)) (sndMap A B)).toElement
              (pairElements A B x y)) = y := by
          rw [← comp_toElement, comp_sndMap_pairMap, sndMap_pairElements]
        exact h1.trans
          (sndMap_pairElements (functionSystem B C) B ((curryMap A B C h).toElement x) y).symm
    have hu1 : (uncurryMap A B C k).toElement (pairElements A B x y) =
        (applyMap (B := B) (C := C)).toElement
          (pairElements (functionSystem B C) B (k.toElement x) y) := by
      simp only [uncurryMap, comp_toElement, hpair_k]
    have hu2 : (uncurryMap A B C (curryMap A B C h)).toElement (pairElements A B x y) =
        (applyMap (B := B) (C := C)).toElement
          (pairElements (functionSystem B C) B ((curryMap A B C h).toElement x) y) := by
      simp only [uncurryMap, comp_toElement, hpair_c]
    have heq : (uncurryMap A B C k).toElement (pairElements A B x y) =
        (uncurryMap A B C (curryMap A B C h)).toElement (pairElements A B x y) := by
      rw [hk]
    rw [← applyMap_toElement, ← applyMap_toElement, ← hu1, ← hu2, heq]
  have hx : element_toApproxMap B C (k.toElement x) =
      element_toApproxMap B C ((curryMap A B C h).toElement x) :=
    (ext_iff_toElement _ _).2 happly
  have : k.toElement x = (curryMap A B C h).toElement x := by
    rw [← approxMap_toElement_element_toApproxMap B C (k.toElement x),
      ← approxMap_toElement_element_toApproxMap B C ((curryMap A B C h).toElement x), hx]
  rw [this]

/-- **Theorem 7.2, first sentence (Scott 1982).** Approximable maps `A → B` are
exactly the elements of the Definition 7.1 function-space system `|A → B|`.
The `apply` / `curry` clauses of the same numbered theorem are proved above
and are not this compared declaration. -/
theorem theorem_7_2 {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) :
    (∀ f : ApproximableMap A B,
      element_toApproxMap A B (approxMap_toElement A B f) = f) ∧
    (∀ x : (functionSystem A B).Element,
      approxMap_toElement A B (element_toApproxMap A B x) = x) :=
  ⟨element_toApproxMap_approxMap_toElement A B,
    approxMap_toElement_element_toApproxMap A B⟩

end InfoSys

end Scott1982

-- Vendor 1982 — Scott1982.Sum (from vendor/scott1982/Scott1982/Sum.lean)

/-!
# Separated sum of information systems — Definition 6.3

**Scott 1982, Definition 6.3.** Tokens of `A + B` are left copies `(X, Δ)`, right
copies `(Δ, Y)`, and a fresh bottom `(Δ, Δ)`. Consistency and entailment are
disjunctive: a consistent set lives entirely on the left or entirely on the right
(or is empty / `{⊥}`).

We encode tokens as an inductive type so that `(Δ_A, Δ)`, `(Δ, Δ_B)`, and `(Δ, Δ)`
remain pairwise distinct, matching Scott’s remark after Def 6.3.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Token type of the separated sum `A + B` (Scott 6.3(i)–(ii)).
`left X` is `(X, Δ)`, `right Y` is `(Δ, Y)`, and `bot` is `(Δ, Δ)`. -/
inductive SumToken (α β : Type*) where
  | left : α → SumToken α β
  | right : β → SumToken α β
  | bot : SumToken α β

instance instDecidableEqSumToken : DecidableEq (SumToken α β)
  | .left a, .left b =>
      if h : a = b then isTrue (h ▸ rfl)
      else isFalse fun h' => h (SumToken.left.inj h')
  | .right a, .right b =>
      if h : a = b then isTrue (h ▸ rfl)
      else isFalse fun h' => h (SumToken.right.inj h')
  | .bot, .bot => isTrue rfl
  | .left _, .right _ => isFalse fun h => nomatch h
  | .left _, .bot => isFalse fun h => nomatch h
  | .right _, .left _ => isFalse fun h => nomatch h
  | .right _, .bot => isFalse fun h => nomatch h
  | .bot, .left _ => isFalse fun h => nomatch h
  | .bot, .right _ => isFalse fun h => nomatch h

variable (A : InfoSys α) (B : InfoSys β)

/-- Sum bottom `Δ_{A+B} = (Δ, Δ)`. -/
def sumBot : SumToken α β := .bot

private def Sum_lftInsert : SumToken α β → Finset α → Finset α
  | .left x => insert x
  | .right _ => id
  | .bot => id

private def Sum_rhtInsert : SumToken α β → Finset β → Finset β
  | .right y => insert y
  | .left _ => id
  | .bot => id

private instance Sum_instLeftCommutativeLftInsert :
    LeftCommutative (Sum_lftInsert : SumToken α β → Finset α → Finset α) :=
  ⟨fun p q s => by
    cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

private instance Sum_instLeftCommutativeRhtInsert :
    LeftCommutative (Sum_rhtInsert : SumToken α β → Finset β → Finset β) :=
  ⟨fun p q s => by
    cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

/-- Left projection `lft u` (Scott 6.3). -/
def lftFinset (u : Finset (SumToken α β)) : Finset α :=
  Multiset.foldr Sum_lftInsert (∅ : Finset α) u.1

/-- Right projection `rht u` (Scott 6.3). -/
def rhtFinset (u : Finset (SumToken α β)) : Finset β :=
  Multiset.foldr Sum_rhtInsert (∅ : Finset β) u.1

private theorem Sum_mem_foldr_lft (s : Multiset (SumToken α β)) (x : α) :
    x ∈ Multiset.foldr Sum_lftInsert (∅ : Finset α) s ↔ ∃ p ∈ s, p = .left x := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hx
      exact False.elim (Finset.notMem_empty x hx)
    · rintro ⟨_, hp, _⟩
      exact False.elim (by cases hp)
  · intro p t ih
    cases p with
    | left a =>
      simp only [Multiset.foldr_cons, Sum_lftInsert, Finset.mem_insert, ih, Multiset.mem_cons]
      constructor
      · rintro (hx | ⟨q, hq, hq'⟩)
        · exact ⟨.left a, Or.inl rfl, congrArg SumToken.left hx.symm⟩
        · exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · injection hq' with hx
          exact Or.inl hx.symm
        · exact Or.inr ⟨q, hq, hq'⟩
    | right b =>
      simp only [Multiset.foldr_cons, Sum_lftInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩
        exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩
    | bot =>
      simp only [Multiset.foldr_cons, Sum_lftInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩
        exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩

private theorem Sum_mem_foldr_rht (s : Multiset (SumToken α β)) (y : β) :
    y ∈ Multiset.foldr Sum_rhtInsert (∅ : Finset β) s ↔ ∃ p ∈ s, p = .right y := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hy
      exact False.elim (Finset.notMem_empty y hy)
    · rintro ⟨_, hp, _⟩
      exact False.elim (by cases hp)
  · intro p t ih
    cases p with
    | right b =>
      simp only [Multiset.foldr_cons, Sum_rhtInsert, Finset.mem_insert, ih, Multiset.mem_cons]
      constructor
      · rintro (hy | ⟨q, hq, hq'⟩)
        · exact ⟨.right b, Or.inl rfl, congrArg SumToken.right hy.symm⟩
        · exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · injection hq' with hy
          exact Or.inl hy.symm
        · exact Or.inr ⟨q, hq, hq'⟩
    | left a =>
      simp only [Multiset.foldr_cons, Sum_rhtInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩
        exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩
    | bot =>
      simp only [Multiset.foldr_cons, Sum_rhtInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩
        exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩

theorem mem_lftFinset {u : Finset (SumToken α β)} {x : α} :
    x ∈ lftFinset u ↔ SumToken.left x ∈ u := by
  unfold lftFinset
  rw [Sum_mem_foldr_lft]
  constructor
  · rintro ⟨p, hp, hp'⟩
    rwa [← hp']
  · intro hx
    exact ⟨.left x, hx, rfl⟩

theorem mem_rhtFinset {u : Finset (SumToken α β)} {y : β} :
    y ∈ rhtFinset u ↔ SumToken.right y ∈ u := by
  unfold rhtFinset
  rw [Sum_mem_foldr_rht]
  constructor
  · rintro ⟨p, hp, hp'⟩
    rwa [← hp']
  · intro hy
    exact ⟨.right y, hy, rfl⟩

theorem lftFinset_empty : lftFinset (∅ : Finset (SumToken α β)) = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim (Finset.notMem_empty _ ((mem_lftFinset).1 hx))
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem rhtFinset_empty : rhtFinset (∅ : Finset (SumToken α β)) = ∅ := by
  ext y
  constructor
  · intro hy
    exact False.elim (Finset.notMem_empty _ ((mem_rhtFinset).1 hy))
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

theorem lftFinset_mono {u v : Finset (SumToken α β)} (h : v ⊆ u) :
    lftFinset v ⊆ lftFinset u := by
  intro x hx
  exact (mem_lftFinset).2 (h ((mem_lftFinset).1 hx))

theorem rhtFinset_mono {u v : Finset (SumToken α β)} (h : v ⊆ u) :
    rhtFinset v ⊆ rhtFinset u := by
  intro y hy
  exact (mem_rhtFinset).2 (h ((mem_rhtFinset).1 hy))

theorem lftFinset_insert_left (u : Finset (SumToken α β)) (x : α) :
    lftFinset (insert (.left x) u) = insert x (lftFinset u) := by
  ext y
  constructor
  · intro hy
    have : SumToken.left y ∈ insert (.left x) u := (mem_lftFinset).1 hy
    rcases Finset.mem_insert.mp this with h | h
    · injection h with hy'
      exact Finset.mem_insert.mpr (Or.inl hy')
    · exact Finset.mem_insert.mpr (Or.inr ((mem_lftFinset).2 h))
  · intro hy
    rcases Finset.mem_insert.mp hy with hy' | hy'
    · exact (mem_lftFinset).2 (Finset.mem_insert.mpr (Or.inl (congrArg SumToken.left hy')))
    · exact (mem_lftFinset).2 (Finset.mem_insert.mpr (Or.inr ((mem_lftFinset).1 hy')))

theorem lftFinset_insert_right (u : Finset (SumToken α β)) (y : β) :
    lftFinset (insert (.right y) u) = lftFinset u := by
  ext x
  constructor
  · intro hx
    have : SumToken.left x ∈ insert (.right y) u := (mem_lftFinset).1 hx
    rcases Finset.mem_insert.mp this with h | h
    · exact False.elim (nomatch h)
    · exact (mem_lftFinset).2 h
  · intro hx
    exact (mem_lftFinset).2 (Finset.mem_insert.mpr (Or.inr ((mem_lftFinset).1 hx)))

theorem lftFinset_insert_bot (u : Finset (SumToken α β)) :
    lftFinset (insert (.bot : SumToken α β) u) = lftFinset u := by
  ext x
  constructor
  · intro hx
    have : SumToken.left x ∈ insert .bot u := (mem_lftFinset).1 hx
    rcases Finset.mem_insert.mp this with h | h
    · exact False.elim (nomatch h)
    · exact (mem_lftFinset).2 h
  · intro hx
    exact (mem_lftFinset).2 (Finset.mem_insert.mpr (Or.inr ((mem_lftFinset).1 hx)))

theorem rhtFinset_insert_right (u : Finset (SumToken α β)) (y : β) :
    rhtFinset (insert (.right y) u) = insert y (rhtFinset u) := by
  ext z
  constructor
  · intro hz
    have : SumToken.right z ∈ insert (.right y) u := (mem_rhtFinset).1 hz
    rcases Finset.mem_insert.mp this with h | h
    · injection h with hz'
      exact Finset.mem_insert.mpr (Or.inl hz')
    · exact Finset.mem_insert.mpr (Or.inr ((mem_rhtFinset).2 h))
  · intro hz
    rcases Finset.mem_insert.mp hz with hz' | hz'
    · exact (mem_rhtFinset).2 (Finset.mem_insert.mpr (Or.inl (congrArg SumToken.right hz')))
    · exact (mem_rhtFinset).2 (Finset.mem_insert.mpr (Or.inr ((mem_rhtFinset).1 hz')))

theorem rhtFinset_insert_left (u : Finset (SumToken α β)) (x : α) :
    rhtFinset (insert (.left x) u) = rhtFinset u := by
  ext y
  constructor
  · intro hy
    have : SumToken.right y ∈ insert (.left x) u := (mem_rhtFinset).1 hy
    rcases Finset.mem_insert.mp this with h | h
    · exact False.elim (nomatch h)
    · exact (mem_rhtFinset).2 h
  · intro hy
    exact (mem_rhtFinset).2 (Finset.mem_insert.mpr (Or.inr ((mem_rhtFinset).1 hy)))

theorem rhtFinset_insert_bot (u : Finset (SumToken α β)) :
    rhtFinset (insert (.bot : SumToken α β) u) = rhtFinset u := by
  ext y
  constructor
  · intro hy
    have : SumToken.right y ∈ insert .bot u := (mem_rhtFinset).1 hy
    rcases Finset.mem_insert.mp this with h | h
    · exact False.elim (nomatch h)
    · exact (mem_rhtFinset).2 h
  · intro hy
    exact (mem_rhtFinset).2 (Finset.mem_insert.mpr (Or.inr ((mem_rhtFinset).1 hy)))

theorem lftFinset_singleton_left (x : α) :
    lftFinset ({.left x} : Finset (SumToken α β)) = {x} := by
  ext y
  simp only [mem_lftFinset, Finset.mem_singleton]
  exact ⟨SumToken.left.inj, fun h => h ▸ rfl⟩

theorem rhtFinset_singleton_right (y : β) :
    rhtFinset ({.right y} : Finset (SumToken α β)) = {y} := by
  ext z
  simp only [mem_rhtFinset, Finset.mem_singleton]
  exact ⟨SumToken.right.inj, fun h => h ▸ rfl⟩

theorem lftFinset_singleton_bot :
    lftFinset ({.bot} : Finset (SumToken α β)) = ∅ := by
  ext x
  constructor
  · intro hx
    have : SumToken.left x ∈ ({.bot} : Finset _) := (mem_lftFinset).1 hx
    exact False.elim (nomatch Finset.mem_singleton.mp this)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem rhtFinset_singleton_bot :
    rhtFinset ({.bot} : Finset (SumToken α β)) = ∅ := by
  ext y
  constructor
  · intro hy
    have : SumToken.right y ∈ ({.bot} : Finset _) := (mem_rhtFinset).1 hy
    exact False.elim (nomatch Finset.mem_singleton.mp this)
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

theorem lftFinset_funion (u v : Finset (SumToken α β)) :
    lftFinset (u ∪' v) = lftFinset u ∪' lftFinset v := by
  ext x
  constructor
  · intro hx
    have : SumToken.left x ∈ u ∪' v := (mem_lftFinset).1 hx
    rcases mem_funion.mp this with h | h
    · exact mem_funion.mpr (Or.inl ((mem_lftFinset).2 h))
    · exact mem_funion.mpr (Or.inr ((mem_lftFinset).2 h))
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact (mem_lftFinset).2 (mem_funion.mpr (Or.inl ((mem_lftFinset).1 h)))
    · exact (mem_lftFinset).2 (mem_funion.mpr (Or.inr ((mem_lftFinset).1 h)))

theorem rhtFinset_funion (u v : Finset (SumToken α β)) :
    rhtFinset (u ∪' v) = rhtFinset u ∪' rhtFinset v := by
  ext y
  constructor
  · intro hy
    have : SumToken.right y ∈ u ∪' v := (mem_rhtFinset).1 hy
    rcases mem_funion.mp this with h | h
    · exact mem_funion.mpr (Or.inl ((mem_rhtFinset).2 h))
    · exact mem_funion.mpr (Or.inr ((mem_rhtFinset).2 h))
  · intro hy
    rcases mem_funion.mp hy with h | h
    · exact (mem_rhtFinset).2 (mem_funion.mpr (Or.inl ((mem_rhtFinset).1 h)))
    · exact (mem_rhtFinset).2 (mem_funion.mpr (Or.inr ((mem_rhtFinset).1 h)))

/-- Consistency for the separated sum (Scott 6.3(iii)). -/
def SumCon (u : Finset (SumToken α β)) : Prop :=
  (lftFinset u ∈ A.Con ∧ rhtFinset u = ∅) ∨
    (lftFinset u = ∅ ∧ rhtFinset u ∈ B.Con)

/-- Entailment for the separated sum (Scott 6.3(iv')–(iv''')).
Includes `SumCon` so `ent_con` can update projections. -/
def SumEnt (u : Finset (SumToken α β)) (p : SumToken α β) : Prop :=
  SumCon A B u ∧
    match p with
    | .bot => True
    | .left x => lftFinset u ≠ ∅ ∧ A.Ent (lftFinset u) x
    | .right y => rhtFinset u ≠ ∅ ∧ B.Ent (rhtFinset u) y

theorem SumCon_empty : SumCon A B (∅ : Finset (SumToken α β)) :=
  Or.inl ⟨by rw [lftFinset_empty]; exact A.con_empty, by rw [rhtFinset_empty]⟩

theorem SumCon_rht_empty_of_lft_nonempty {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (hne : lftFinset u ≠ ∅) : rhtFinset u = ∅ := by
  rcases hu with ⟨_, hr⟩ | ⟨hl, _⟩
  · exact hr
  · exact False.elim (hne hl)

theorem SumCon_lft_empty_of_rht_nonempty {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (hne : rhtFinset u ≠ ∅) : lftFinset u = ∅ := by
  rcases hu with ⟨_, hr⟩ | ⟨hl, _⟩
  · exact False.elim (hne hr)
  · exact hl

theorem SumCon_lft_con_of_lft_nonempty {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (hne : lftFinset u ≠ ∅) : lftFinset u ∈ A.Con := by
  rcases hu with ⟨hl, _⟩ | ⟨hl, _⟩
  · exact hl
  · exact False.elim (hne hl)

theorem SumCon_rht_con_of_rht_nonempty {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (hne : rhtFinset u ≠ ∅) : rhtFinset u ∈ B.Con := by
  rcases hu with ⟨_, hr⟩ | ⟨_, hr⟩
  · exact False.elim (hne hr)
  · exact hr

/-- **Definition 6.3.** The separated sum information system `A + B`. -/
def sumSystem : InfoSys (SumToken α β) where
  bot := sumBot
  Con := {u | SumCon A B u}
  Ent := SumEnt A B
  con_subset := by
    intro u v hu hv
    rcases hu with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · exact Or.inl ⟨A.con_subset hl (lftFinset_mono hv),
        Finset.Subset.antisymm (by
          intro y hy
          have : y ∈ rhtFinset u := rhtFinset_mono hv hy
          rw [hr] at this
          exact False.elim (Finset.notMem_empty y this))
          (Finset.empty_subset _)⟩
    · exact Or.inr ⟨Finset.Subset.antisymm (by
          intro x hx
          have : x ∈ lftFinset u := lftFinset_mono hv hx
          rw [hl] at this
          exact False.elim (Finset.notMem_empty x this))
          (Finset.empty_subset _),
        B.con_subset hr (rhtFinset_mono hv)⟩
  con_sing := by
    intro p
    cases p with
    | left x =>
      exact Or.inl ⟨by rw [lftFinset_singleton_left]; exact A.con_sing x,
        by
          ext y
          constructor
          · intro hy
            have : SumToken.right y ∈ ({.left x} : Finset _) := (mem_rhtFinset).1 hy
            exact False.elim (nomatch Finset.mem_singleton.mp this)
          · intro hy
            exact False.elim (Finset.notMem_empty y hy)⟩
    | right y =>
      exact Or.inr ⟨by
          ext x
          constructor
          · intro hx
            have : SumToken.left x ∈ ({.right y} : Finset _) := (mem_lftFinset).1 hx
            exact False.elim (nomatch Finset.mem_singleton.mp this)
          · intro hx
            exact False.elim (Finset.notMem_empty x hx),
        by rw [rhtFinset_singleton_right]; exact B.con_sing y⟩
    | bot =>
      exact Or.inl ⟨by rw [lftFinset_singleton_bot]; exact A.con_empty,
        rhtFinset_singleton_bot⟩
  ent_con := by
    intro u p ⟨hu, hEnt⟩
    cases p with
    | bot =>
      rcases hu with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · exact Or.inl ⟨by rw [lftFinset_insert_bot]; exact hl,
          by rw [rhtFinset_insert_bot]; exact hr⟩
      · exact Or.inr ⟨by rw [lftFinset_insert_bot]; exact hl,
          by rw [rhtFinset_insert_bot]; exact hr⟩
    | left x =>
      rcases hEnt with ⟨hne, hA⟩
      have hr : rhtFinset u = ∅ := SumCon_rht_empty_of_lft_nonempty A B hu hne
      exact Or.inl ⟨by
          rw [lftFinset_insert_left]
          exact A.ent_con hA,
        by rw [rhtFinset_insert_left]; exact hr⟩
    | right y =>
      rcases hEnt with ⟨hne, hB⟩
      have hl : lftFinset u = ∅ := SumCon_lft_empty_of_rht_nonempty A B hu hne
      exact Or.inr ⟨by rw [lftFinset_insert_right]; exact hl,
        by
          rw [rhtFinset_insert_right]
          exact B.ent_con hB⟩
  ent_bot := by
    intro u hu
    exact ⟨hu, trivial⟩
  ent_refl := by
    intro u p hu hp
    refine ⟨hu, ?_⟩
    cases p with
    | bot => exact trivial
    | left x =>
      have hx : x ∈ lftFinset u := (mem_lftFinset).2 hp
      have hne : lftFinset u ≠ ∅ := Finset.ne_empty_of_mem hx
      exact ⟨hne, A.ent_refl (SumCon_lft_con_of_lft_nonempty A B hu hne) hx⟩
    | right y =>
      have hy : y ∈ rhtFinset u := (mem_rhtFinset).2 hp
      have hne : rhtFinset u ≠ ∅ := Finset.ne_empty_of_mem hy
      exact ⟨hne, B.ent_refl (SumCon_rht_con_of_rht_nonempty A B hu hne) hy⟩
  ent_trans := by
    intro u v c hv hu hEnts hEntc
    refine ⟨hv, ?_⟩
    cases c with
    | bot => exact trivial
    | left x =>
      rcases hEntc with ⟨_, ⟨hne, hA⟩⟩
      have hlft : ∀ y ∈ lftFinset u, A.Ent (lftFinset v) y := by
        intro y hy
        have hp : SumToken.left y ∈ u := (mem_lftFinset).1 hy
        have hEy : SumEnt A B v (.left y) := hEnts _ hp
        exact hEy.2.2
      have hne' : lftFinset v ≠ ∅ := by
        obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty hne
        have hp : SumToken.left y ∈ u := (mem_lftFinset).1 hy
        exact (hEnts _ hp).2.1
      refine ⟨hne', ?_⟩
      exact A.ent_trans (SumCon_lft_con_of_lft_nonempty A B hv hne')
        (SumCon_lft_con_of_lft_nonempty A B hu hne) hlft hA
    | right y =>
      rcases hEntc with ⟨_, ⟨hne, hB⟩⟩
      have hrht : ∀ z ∈ rhtFinset u, B.Ent (rhtFinset v) z := by
        intro z hz
        have hp : SumToken.right z ∈ u := (mem_rhtFinset).1 hz
        have hEz : SumEnt A B v (.right z) := hEnts _ hp
        exact hEz.2.2
      have hne' : rhtFinset v ≠ ∅ := by
        obtain ⟨z, hz⟩ := Finset.nonempty_of_ne_empty hne
        have hp : SumToken.right z ∈ u := (mem_rhtFinset).1 hz
        exact (hEnts _ hp).2.1
      refine ⟨hne', ?_⟩
      exact B.ent_trans (SumCon_rht_con_of_rht_nonempty A B hv hne')
        (SumCon_rht_con_of_rht_nonempty A B hu hne) hrht hB

end InfoSys

end Scott1982

-- Vendor 1982 — Scott1982.Proposition64 (from vendor/scott1982/Scott1982/Proposition64.lean)

/-!
# Proposition 6.4 — sum injections and copairing

**Scott 1982, Proposition 6.4.** Approximable `inl`, `inr`, and unique copairing
`[f, g]` with `[f, g] ∘ inl = f`, `[f, g] ∘ inr = g`, and `[f, g](⊥) = ⊥`.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false

private instance Proposition64_instLeftCommutativeLiftSumLeft :
    LeftCommutative fun x : α =>
      (insert (SumToken.left (β := β) x) : Finset (SumToken α β) → Finset _) :=
  ⟨fun _ _ s => insert_comm' _ _ s⟩

private instance Proposition64_instLeftCommutativeLiftSumRight :
    LeftCommutative fun y : β =>
      (insert (SumToken.right (α := α) y) : Finset (SumToken α β) → Finset _) :=
  ⟨fun _ _ s => insert_comm' _ _ s⟩

/-- Embed `A`-tokens as left sum tokens. -/
def liftSumLeft (v : Finset α) : Finset (SumToken α β) :=
  Multiset.foldr (fun x : α => insert (SumToken.left (β := β) x))
    (∅ : Finset (SumToken α β)) v.1

/-- Embed `B`-tokens as right sum tokens. -/
def liftSumRight (w : Finset β) : Finset (SumToken α β) :=
  Multiset.foldr (fun y : β => insert (SumToken.right (α := α) y))
    (∅ : Finset (SumToken α β)) w.1

private theorem Proposition64_mem_foldr_liftSumLeft (s : Multiset α) (p : SumToken α β) :
    p ∈ Multiset.foldr (fun x : α => insert (SumToken.left (β := β) x))
        (∅ : Finset (SumToken α β)) s ↔
      ∃ x ∈ s, p = .left x := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hp
      exact False.elim (Finset.notMem_empty p hp)
    · rintro ⟨_, hx, _⟩
      exact False.elim (by cases hx)
  · intro x t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (hp | ⟨y, hy, hp⟩)
      · exact ⟨x, Or.inl rfl, hp⟩
      · exact ⟨y, Or.inr hy, hp⟩
    · rintro ⟨y, hy, hp⟩
      rcases hy with rfl | hy
      · exact Or.inl hp
      · exact Or.inr ⟨y, hy, hp⟩

private theorem Proposition64_mem_foldr_liftSumRight (s : Multiset β) (p : SumToken α β) :
    p ∈ Multiset.foldr (fun y : β => insert (SumToken.right (α := α) y))
        (∅ : Finset (SumToken α β)) s ↔
      ∃ y ∈ s, p = .right y := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hp
      exact False.elim (Finset.notMem_empty p hp)
    · rintro ⟨_, hy, _⟩
      exact False.elim (by cases hy)
  · intro y t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (hp | ⟨z, hz, hp⟩)
      · exact ⟨y, Or.inl rfl, hp⟩
      · exact ⟨z, Or.inr hz, hp⟩
    · rintro ⟨z, hz, hp⟩
      rcases hz with rfl | hz
      · exact Or.inl hp
      · exact Or.inr ⟨z, hz, hp⟩

theorem mem_liftSumLeft {v : Finset α} {p : SumToken α β} :
    p ∈ liftSumLeft (β := β) v ↔ ∃ x ∈ v, p = .left x := by
  simpa [liftSumLeft] using Proposition64_mem_foldr_liftSumLeft (β := β) v.1 p

theorem mem_liftSumRight {w : Finset β} {p : SumToken α β} :
    p ∈ liftSumRight (α := α) w ↔ ∃ y ∈ w, p = .right y := by
  simpa [liftSumRight] using Proposition64_mem_foldr_liftSumRight (α := α) w.1 p

theorem lftFinset_liftSumLeft (v : Finset α) :
    lftFinset (liftSumLeft (β := β) v) = v := by
  ext x
  simp only [mem_lftFinset, mem_liftSumLeft]
  exact ⟨fun ⟨y, hy, h⟩ => by injection h with h'; exact h' ▸ hy,
    fun hx => ⟨x, hx, rfl⟩⟩

theorem rhtFinset_liftSumLeft (v : Finset α) :
    rhtFinset (liftSumLeft (β := β) v) = ∅ := by
  ext y
  constructor
  · intro hy
    rcases (mem_liftSumLeft (β := β)).1 ((mem_rhtFinset).1 hy) with ⟨_, _, h⟩
    exact False.elim (nomatch h)
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

theorem rhtFinset_liftSumRight (w : Finset β) :
    rhtFinset (liftSumRight (α := α) w) = w := by
  ext y
  simp only [mem_rhtFinset, mem_liftSumRight]
  exact ⟨fun ⟨z, hz, h⟩ => by injection h with h'; exact h' ▸ hz,
    fun hy => ⟨y, hy, rfl⟩⟩

theorem lftFinset_liftSumRight (w : Finset β) :
    lftFinset (liftSumRight (α := α) w) = ∅ := by
  ext x
  constructor
  · intro hx
    rcases (mem_liftSumRight (α := α)).1 ((mem_lftFinset).1 hx) with ⟨_, _, h⟩
    exact False.elim (nomatch h)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem SumCon_liftSumLeft {v : Finset α} (hv : v ∈ A.Con) :
    SumCon A B (liftSumLeft (β := β) v) :=
  Or.inl ⟨by rw [lftFinset_liftSumLeft]; exact hv, rhtFinset_liftSumLeft (β := β) v⟩

theorem SumCon_liftSumRight {w : Finset β} (hw : w ∈ B.Con) :
    SumCon A B (liftSumRight (α := α) w) :=
  Or.inr ⟨lftFinset_liftSumRight (α := α) w, by rw [rhtFinset_liftSumRight]; exact hw⟩

theorem rht_eq_empty_of_sumEntSet {u u' : Finset (SumToken α β)}
    (hr : rhtFinset u = ∅) (hEnt : (sumSystem A B).EntSet u u') :
    rhtFinset u' = ∅ := by
  ext y
  constructor
  · intro hy
    exact False.elim ((hEnt _ ((mem_rhtFinset).1 hy)).2.1 hr)
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

theorem lft_eq_empty_of_sumEntSet {u u' : Finset (SumToken α β)}
    (hl : lftFinset u = ∅) (hEnt : (sumSystem A B).EntSet u u') :
    lftFinset u' = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim ((hEnt _ ((mem_lftFinset).1 hx)).2.1 hl)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem entSet_lft_of_sumEntSet {u u' : Finset (SumToken α β)}
    (hEnt : (sumSystem A B).EntSet u u') :
    A.EntSet (lftFinset u) (lftFinset u') := fun _ hx =>
  (hEnt _ ((mem_lftFinset).1 hx)).2.2

theorem entSet_rht_of_sumEntSet {u u' : Finset (SumToken α β)}
    (hEnt : (sumSystem A B).EntSet u u') :
    B.EntSet (rhtFinset u) (rhtFinset u') := fun _ hy =>
  (hEnt _ ((mem_rhtFinset).1 hy)).2.2

theorem lft_mem_Con_of_SumCon_rht_empty {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (_hr : rhtFinset u = ∅) : lftFinset u ∈ A.Con := by
  rcases hu with ⟨hl, _⟩ | ⟨hl, _⟩
  · exact hl
  · rw [hl]; exact A.con_empty

theorem rht_mem_Con_of_SumCon_lft_empty {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (_hl : lftFinset u = ∅) : rhtFinset u ∈ B.Con := by
  rcases hu with ⟨_, hr⟩ | ⟨_, hr⟩
  · rw [hr]; exact B.con_empty
  · exact hr

namespace ApproximableMap

variable {C : InfoSys γ}

/-- **Proposition 6.4(1).** Left injection. -/
def inlMap : ApproximableMap A (sumSystem A B) where
  rel v u := v ∈ A.Con ∧ SumCon A B u ∧ rhtFinset u = ∅ ∧ A.EntSet v (lftFinset u)
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨A.con_empty, SumCon_empty A B, by rw [rhtFinset_empty], A.entSet_empty ∅⟩
  union_right := by
    rintro v u u' ⟨hv, hu, hr, hEnt⟩ ⟨_, hu', hr', hEnt'⟩
    refine ⟨hv, ?_, ?_, ?_⟩
    · have hl : lftFinset (u ∪' u') ∈ A.Con := by
        rw [lftFinset_funion]
        exact A.con_subset
          (proposition_2_3_ii (sys := A) hv (proposition_2_3_vi (sys := A) hEnt hEnt'))
          (subset_funion_right _ _)
      exact Or.inl ⟨hl, by rw [rhtFinset_funion, hr, hr']; rfl⟩
    · rw [rhtFinset_funion, hr, hr']; rfl
    · rw [lftFinset_funion]; exact proposition_2_3_vi (sys := A) hEnt hEnt'
  mono := by
    rintro v v' u u' ⟨hv, hu, hr, hEnt⟩ hEntv hEntu hv' hu'
    refine ⟨hv', hu', rht_eq_empty_of_sumEntSet A B hr hEntu, ?_⟩
    exact proposition_2_3_iv (sys := A) hv'
      (lft_mem_Con_of_SumCon_rht_empty A B hu hr)
      (proposition_2_3_iv (sys := A) hv' hv hEntv hEnt)
      (entSet_lft_of_sumEntSet A B hEntu)

/-- **Proposition 6.4(2).** Right injection. -/
def inrMap : ApproximableMap B (sumSystem A B) where
  rel w u := w ∈ B.Con ∧ SumCon A B u ∧ lftFinset u = ∅ ∧ B.EntSet w (rhtFinset u)
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨B.con_empty, SumCon_empty A B, by rw [lftFinset_empty], B.entSet_empty ∅⟩
  union_right := by
    rintro w u u' ⟨hw, hu, hl, hEnt⟩ ⟨_, hu', hl', hEnt'⟩
    refine ⟨hw, ?_, ?_, ?_⟩
    · have hrC : rhtFinset (u ∪' u') ∈ B.Con := by
        rw [rhtFinset_funion]
        exact B.con_subset
          (proposition_2_3_ii (sys := B) hw (proposition_2_3_vi (sys := B) hEnt hEnt'))
          (subset_funion_right _ _)
      exact Or.inr ⟨by rw [lftFinset_funion, hl, hl']; rfl, hrC⟩
    · rw [lftFinset_funion, hl, hl']; rfl
    · rw [rhtFinset_funion]; exact proposition_2_3_vi (sys := B) hEnt hEnt'
  mono := by
    rintro w w' u u' ⟨hw, hu, hl, hEnt⟩ hEntw hEntu hw' hu'
    refine ⟨hw', hu', lft_eq_empty_of_sumEntSet A B hl hEntu, ?_⟩
    exact proposition_2_3_iv (sys := B) hw'
      (rht_mem_Con_of_SumCon_lft_empty A B hu hl)
      (proposition_2_3_iv (sys := B) hw' hw hEntw hEnt)
      (entSet_rht_of_sumEntSet A B hEntu)

private theorem Proposition64_copair_union_disj (f : ApproximableMap A C) (g : ApproximableMap B C)
    {u : Finset (SumToken α β)} {s s' : Finset γ}
    (hu : SumCon A B u) (hs : s ∈ C.Con) (hs' : s' ∈ C.Con)
    (h : C.EntSet ∅ s ∨ (lftFinset u ≠ ∅ ∧ f.rel (lftFinset u) s) ∨
      (rhtFinset u ≠ ∅ ∧ g.rel (rhtFinset u) s))
    (h' : C.EntSet ∅ s' ∨ (lftFinset u ≠ ∅ ∧ f.rel (lftFinset u) s') ∨
      (rhtFinset u ≠ ∅ ∧ g.rel (rhtFinset u) s')) :
    C.EntSet ∅ (s ∪' s') ∨
      (lftFinset u ≠ ∅ ∧ f.rel (lftFinset u) (s ∪' s')) ∨
        (rhtFinset u ≠ ∅ ∧ g.rel (rhtFinset u) (s ∪' s')) := by
  rcases h with h | ⟨hne, hf⟩ | ⟨hne, hg⟩ <;> rcases h' with h' | ⟨hne', hf'⟩ | ⟨hne', hg'⟩
  · exact Or.inl (proposition_2_3_vi (sys := C) h h')
  · have hf0 : f.rel (lftFinset u) s :=
      f.mono f.empty_rel (A.entSet_empty _) h
        (SumCon_lft_con_of_lft_nonempty A B hu hne') hs
    exact Or.inr (Or.inl ⟨hne', f.union_right hf0 hf'⟩)
  · have hg0 : g.rel (rhtFinset u) s :=
      g.mono g.empty_rel (B.entSet_empty _) h
        (SumCon_rht_con_of_rht_nonempty A B hu hne') hs
    exact Or.inr (Or.inr ⟨hne', g.union_right hg0 hg'⟩)
  · have hf0 : f.rel (lftFinset u) s' :=
      f.mono f.empty_rel (A.entSet_empty _) h'
        (SumCon_lft_con_of_lft_nonempty A B hu hne) hs'
    exact Or.inr (Or.inl ⟨hne, f.union_right hf hf0⟩)
  · exact Or.inr (Or.inl ⟨hne, f.union_right hf hf'⟩)
  · exact False.elim (hne' (SumCon_rht_empty_of_lft_nonempty A B hu hne))
  · have hg0 : g.rel (rhtFinset u) s' :=
      g.mono g.empty_rel (B.entSet_empty _) h'
        (SumCon_rht_con_of_rht_nonempty A B hu hne) hs'
    exact Or.inr (Or.inr ⟨hne, g.union_right hg hg0⟩)
  · exact False.elim (hne' (SumCon_lft_empty_of_rht_nonempty A B hu hne))
  · exact Or.inr (Or.inr ⟨hne, g.union_right hg hg'⟩)

/-- **Proposition 6.4(3).** Copairing of approximable maps. -/
def copairMap (f : ApproximableMap A C) (g : ApproximableMap B C) :
    ApproximableMap (sumSystem A B) C where
  rel u s :=
    SumCon A B u ∧ s ∈ C.Con ∧
      (C.EntSet ∅ s ∨
        (lftFinset u ≠ ∅ ∧ f.rel (lftFinset u) s) ∨
          (rhtFinset u ≠ ∅ ∧ g.rel (rhtFinset u) s))
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨SumCon_empty A B, C.con_empty, Or.inl (C.entSet_empty ∅)⟩
  union_right := by
    rintro u s s' ⟨hu, hs, h⟩ ⟨_, hs', h'⟩
    have hU := Proposition64_copair_union_disj A B f g hu hs hs' h h'
    refine ⟨hu, ?_, hU⟩
    rcases hU with hE | ⟨_, hf⟩ | ⟨_, hg⟩
    · exact C.con_subset (proposition_2_3_ii (sys := C) C.con_empty hE)
        (subset_funion_right _ _)
    · exact f.rel_cod hf
    · exact g.rel_cod hg
  mono := by
    rintro u u' s s' ⟨hu, hs, h⟩ hEntu hEnts hu' hs'
    refine ⟨hu', hs', ?_⟩
    rcases h with h | ⟨hne, hf⟩ | ⟨hne, hg⟩
    · exact Or.inl (proposition_2_3_iv (sys := C) C.con_empty hs h hEnts)
    · have hne' : lftFinset u' ≠ ∅ := by
        obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hne
        exact (hEntu _ ((mem_lftFinset).1 hx)).2.1
      exact Or.inr (Or.inl ⟨hne',
        f.mono hf (entSet_lft_of_sumEntSet A B hEntu) hEnts
          (SumCon_lft_con_of_lft_nonempty A B hu' hne') hs'⟩)
    · have hne' : rhtFinset u' ≠ ∅ := by
        obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty hne
        exact (hEntu _ ((mem_rhtFinset).1 hy)).2.1
      exact Or.inr (Or.inr ⟨hne',
        g.mono hg (entSet_rht_of_sumEntSet A B hEntu) hEnts
          (SumCon_rht_con_of_rht_nonempty A B hu' hne') hs'⟩)

theorem comp_copairMap_inlMap (f : ApproximableMap A C) (g : ApproximableMap B C) :
    comp (copairMap A B f g) (inlMap A B) = f := by
  refine ApproximableMap.ext fun v s => ?_
  constructor
  · rintro ⟨u, ⟨hv, hu, hr, hEnt⟩, ⟨_, hs, hcop⟩⟩
    rcases hcop with hE | ⟨_, hf⟩ | ⟨hne, _⟩
    · exact f.mono f.empty_rel (A.entSet_empty v) hE hv hs
    · exact f.mono hf hEnt (proposition_2_3_iii C hs) hv hs
    · exact False.elim (hne hr)
  · intro hf
    -- Always lift `insert Δ v` so the left branch of copair is nonempty (avoids
    -- classical `by_cases` on `v = ∅`).
    let vBot := insert A.bot v
    have hvBot : vBot ∈ A.Con := A.ent_con (A.ent_bot (f.rel_dom hf))
    have hEntBot : A.EntSet vBot v :=
      fun _ hx => A.ent_refl hvBot (Finset.mem_insert_of_mem hx)
    have hfBot : f.rel vBot s :=
      f.mono hf hEntBot (proposition_2_3_iii C (f.rel_cod hf)) hvBot (f.rel_cod hf)
    refine ⟨liftSumLeft (β := β) vBot, ?_, ?_⟩
    · refine ⟨f.rel_dom hf, SumCon_liftSumLeft A B hvBot,
        rhtFinset_liftSumLeft (β := β) vBot, ?_⟩
      rw [lftFinset_liftSumLeft]
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · subst hx; exact A.ent_bot (f.rel_dom hf)
      · exact A.ent_refl (f.rel_dom hf) hx
    · refine ⟨SumCon_liftSumLeft A B hvBot, f.rel_cod hf, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
      · rw [lftFinset_liftSumLeft]; exact Finset.insert_ne_empty A.bot v
      · rw [lftFinset_liftSumLeft]; exact hfBot

theorem comp_copairMap_inrMap (f : ApproximableMap A C) (g : ApproximableMap B C) :
    comp (copairMap A B f g) (inrMap A B) = g := by
  refine ApproximableMap.ext fun w s => ?_
  constructor
  · rintro ⟨u, ⟨hw, hu, hl, hEnt⟩, ⟨_, hs, hcop⟩⟩
    rcases hcop with hE | ⟨hne, _⟩ | ⟨_, hg⟩
    · exact g.mono g.empty_rel (B.entSet_empty w) hE hw hs
    · exact False.elim (hne hl)
    · exact g.mono hg hEnt (proposition_2_3_iii C hs) hw hs
  · intro hg
    let wBot := insert B.bot w
    have hwBot : wBot ∈ B.Con := B.ent_con (B.ent_bot (g.rel_dom hg))
    have hEntBot : B.EntSet wBot w :=
      fun _ hy => B.ent_refl hwBot (Finset.mem_insert_of_mem hy)
    have hgBot : g.rel wBot s :=
      g.mono hg hEntBot (proposition_2_3_iii C (g.rel_cod hg)) hwBot (g.rel_cod hg)
    refine ⟨liftSumRight (α := α) wBot, ?_, ?_⟩
    · refine ⟨g.rel_dom hg, SumCon_liftSumRight A B hwBot,
        lftFinset_liftSumRight (α := α) wBot, ?_⟩
      rw [rhtFinset_liftSumRight]
      intro y hy
      rcases Finset.mem_insert.mp hy with hy | hy
      · subst hy; exact B.ent_bot (g.rel_dom hg)
      · exact B.ent_refl (g.rel_dom hg) hy
    · refine ⟨SumCon_liftSumRight A B hwBot, g.rel_cod hg, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
      · rw [rhtFinset_liftSumRight]; exact Finset.insert_ne_empty B.bot w
      · rw [rhtFinset_liftSumRight]; exact hgBot

theorem copairMap_botElement (f : ApproximableMap A C) (g : ApproximableMap B C) :
    (copairMap A B f g).toElement (sumSystem A B).botElement = C.botElement := by
  apply le_antisymm
  · intro Y ⟨u, hu, ⟨huCon, hs, hcop⟩⟩
    have onlyBot : ∀ p ∈ u, p = SumToken.bot (α := α) (β := β) := by
      intro p hp
      have hEnt : (sumSystem A B).Ent {sumBot} p := hu (Finset.mem_coe.2 hp)
      cases p with
      | bot => rfl
      | left x =>
        exact False.elim (by
          have hne := hEnt.2.1
          have : lftFinset ({sumBot} : Finset (SumToken α β)) = ∅ := lftFinset_singleton_bot
          exact hne this)
      | right y =>
        exact False.elim (by
          have hne := hEnt.2.1
          have : rhtFinset ({sumBot} : Finset (SumToken α β)) = ∅ := rhtFinset_singleton_bot
          exact hne this)
    have hl : lftFinset u = ∅ := by
      ext x; constructor
      · intro hx; exact False.elim (nomatch onlyBot _ ((mem_lftFinset).1 hx))
      · intro hx; exact False.elim (Finset.notMem_empty x hx)
    have hr : rhtFinset u = ∅ := by
      ext y; constructor
      · intro hy; exact False.elim (nomatch onlyBot _ ((mem_rhtFinset).1 hy))
      · intro hy; exact False.elim (Finset.notMem_empty y hy)
    rcases hcop with hE | ⟨hne, _⟩ | ⟨hne, _⟩
    · exact C.ent_trans (C.con_sing C.bot) C.con_empty
        (fun _ hz => False.elim (Finset.notMem_empty _ hz))
        (hE Y (Finset.mem_singleton_self _))
    · exact False.elim (hne hl)
    · exact False.elim (hne hr)
  · intro Y hY
    refine ⟨∅, fun _ hp => False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 hp)), ?_⟩
    refine ⟨SumCon_empty A B, C.con_sing Y, Or.inl ?_⟩
    intro Z hZ
    have : Z = Y := Finset.mem_singleton.mp hZ
    subst this
    exact C.ent_trans C.con_empty (C.con_sing C.bot)
      (fun _ hz => by
        have : _ = C.bot := Finset.mem_singleton.mp hz
        subst this
        exact C.ent_bot C.con_empty)
      hY

/-- Carrier of the left copy extracted from a sum element. -/
def sumLftCarrier (z : (sumSystem A B).Element) : Set α :=
  {x | SumToken.left x ∈ z.carrier}

/-- Carrier of the right copy extracted from a sum element. -/
def sumRhtCarrier (z : (sumSystem A B).Element) : Set β :=
  {y | SumToken.right y ∈ z.carrier}

/-- Left copy as an `A`-element, given some left token in `z`. -/
def sumElementLft (z : (sumSystem A B).Element)
    (x0 : α) (hx0 : SumToken.left x0 ∈ z.carrier) : A.Element where
  carrier := sumLftCarrier A B z
  consistent := by
    intro Y hY
    have hsub : (↑(liftSumLeft (β := β) Y) : Set _) ⊆ z.carrier := by
      intro p hp
      rcases (mem_liftSumLeft (β := β)).1 (Finset.mem_coe.1 hp) with ⟨x, hx, rfl⟩
      exact hY (Finset.mem_coe.2 hx)
    have h := lft_mem_Con_of_SumCon_rht_empty A B (z.consistent _ hsub)
      (rhtFinset_liftSumLeft (β := β) Y)
    rwa [lftFinset_liftSumLeft] at h
  closed := by
    intro Y a hY hEnt
    if hempty : Y = ∅ then
      subst hempty
      have hEnt' : A.Ent {x0} a :=
        A.ent_trans (A.con_sing x0) A.con_empty
          (fun _ h => False.elim (Finset.notMem_empty _ h)) hEnt
      have hsub : (↑({SumToken.left x0} : Finset (SumToken α β)) : Set _) ⊆ z.carrier := by
        intro p hp
        have : p = .left x0 := Finset.mem_singleton.mp (Finset.mem_coe.1 hp)
        subst this; exact hx0
      have hSum : (sumSystem A B).Ent {SumToken.left x0} (.left a) := by
        refine ⟨z.consistent _ hsub, ⟨Finset.singleton_ne_empty _, ?_⟩⟩
        rw [lftFinset_singleton_left]; exact hEnt'
      exact z.closed _ _ hsub hSum
    else
      have hsub : (↑(liftSumLeft (β := β) Y) : Set _) ⊆ z.carrier := by
        intro p hp
        rcases (mem_liftSumLeft (β := β)).1 (Finset.mem_coe.1 hp) with ⟨x, hx, rfl⟩
        exact hY (Finset.mem_coe.2 hx)
      have hSum : (sumSystem A B).Ent (liftSumLeft (β := β) Y) (.left a) := by
        refine ⟨z.consistent _ hsub, ⟨?_, ?_⟩⟩
        · rw [lftFinset_liftSumLeft]; exact hempty
        · rw [lftFinset_liftSumLeft]; exact hEnt
      exact z.closed _ _ hsub hSum

/-- Right copy as a `B`-element, given some right token in `z`. -/
def sumElementRht (z : (sumSystem A B).Element)
    (y0 : β) (hy0 : SumToken.right y0 ∈ z.carrier) : B.Element where
  carrier := sumRhtCarrier A B z
  consistent := by
    intro W hW
    have hsub : (↑(liftSumRight (α := α) W) : Set _) ⊆ z.carrier := by
      intro p hp
      rcases (mem_liftSumRight (α := α)).1 (Finset.mem_coe.1 hp) with ⟨y, hy, rfl⟩
      exact hW (Finset.mem_coe.2 hy)
    have h := rht_mem_Con_of_SumCon_lft_empty A B (z.consistent _ hsub)
      (lftFinset_liftSumRight (α := α) W)
    rwa [rhtFinset_liftSumRight] at h
  closed := by
    intro W b hW hEnt
    if hempty : W = ∅ then
      subst hempty
      have hEnt' : B.Ent {y0} b :=
        B.ent_trans (B.con_sing y0) B.con_empty
          (fun _ h => False.elim (Finset.notMem_empty _ h)) hEnt
      have hsub : (↑({SumToken.right y0} : Finset (SumToken α β)) : Set _) ⊆ z.carrier := by
        intro p hp
        have : p = .right y0 := Finset.mem_singleton.mp (Finset.mem_coe.1 hp)
        subst this; exact hy0
      have hSum : (sumSystem A B).Ent {SumToken.right y0} (.right b) := by
        refine ⟨z.consistent _ hsub, ⟨Finset.singleton_ne_empty _, ?_⟩⟩
        rw [rhtFinset_singleton_right]; exact hEnt'
      exact z.closed _ _ hsub hSum
    else
      have hsub : (↑(liftSumRight (α := α) W) : Set _) ⊆ z.carrier := by
        intro p hp
        rcases (mem_liftSumRight (α := α)).1 (Finset.mem_coe.1 hp) with ⟨y, hy, rfl⟩
        exact hW (Finset.mem_coe.2 hy)
      have hSum : (sumSystem A B).Ent (liftSumRight (α := α) W) (.right b) := by
        refine ⟨z.consistent _ hsub, ⟨?_, ?_⟩⟩
        · rw [rhtFinset_liftSumRight]; exact hempty
        · rw [rhtFinset_liftSumRight]; exact hEnt
      exact z.closed _ _ hsub hSum

theorem not_mem_right_of_mem_left (z : (sumSystem A B).Element)
    {x : α} {y : β} (hx : SumToken.left x ∈ z.carrier)
    (hy : SumToken.right y ∈ z.carrier) : False := by
  let u : Finset (SumToken α β) := insert (.left x) {SumToken.right y}
  have hsub : (↑u : Set _) ⊆ z.carrier := by
    intro p hp
    rcases Finset.mem_insert.mp (Finset.mem_coe.1 hp) with h | h
    · subst h; exact hx
    · have : p = .right y := Finset.mem_singleton.mp h
      subst this; exact hy
  have hCon := z.consistent u hsub
  have hlne : lftFinset u ≠ ∅ := by
    intro h
    have : x ∈ lftFinset u := (mem_lftFinset).2 (Finset.mem_insert_self _ _)
    rw [h] at this
    exact Finset.notMem_empty _ this
  have hrne : rhtFinset u ≠ ∅ := by
    intro h
    have : y ∈ rhtFinset u :=
      (mem_rhtFinset).2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [h] at this
    exact Finset.notMem_empty _ this
  rcases hCon with ⟨_, hr⟩ | ⟨hl, _⟩
  · exact hrne hr
  · exact hlne hl

theorem inlMap_toElement_sumElementLft (z : (sumSystem A B).Element)
    (x0 : α) (hx0 : SumToken.left x0 ∈ z.carrier) :
    (inlMap A B).toElement (sumElementLft A B z x0 hx0) = z := by
  apply le_antisymm
  · intro p ⟨v, hv, ⟨hvCon, huCon, hr, hEnt⟩⟩
    cases p with
    | bot => exact factoid_3_2 (sumSystem A B) z
    | left x =>
      have hEntx : A.Ent v x := by
        have : lftFinset ({SumToken.left x} : Finset (SumToken α β)) = {x} :=
          lftFinset_singleton_left x
        simpa [this] using hEnt x (Finset.mem_singleton_self x)
      exact (sumElementLft A B z x0 hx0).closed v x hv hEntx
    | right y =>
      have : rhtFinset ({SumToken.right y} : Finset (SumToken α β)) = {y} :=
        rhtFinset_singleton_right y
      exact False.elim (Finset.singleton_ne_empty y (this ▸ hr))
  · intro p hp
    cases p with
    | bot =>
      refine ⟨∅, fun _ h => False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 h)), ?_⟩
      exact ⟨A.con_empty, (sumSystem A B).con_sing _, by rw [rhtFinset_singleton_bot],
        A.entSet_empty _⟩
    | left x =>
      refine ⟨{x}, ?_, ?_⟩
      · intro a ha
        have : a = x := Finset.mem_singleton.mp (Finset.mem_coe.1 ha)
        subst this; exact hp
      · refine ⟨A.con_sing x, (sumSystem A B).con_sing _, ?_, ?_⟩
        · ext y; constructor
          · intro hy
            have : SumToken.right y ∈ ({SumToken.left x} : Finset _) := (mem_rhtFinset).1 hy
            exact False.elim (nomatch Finset.mem_singleton.mp this)
          · intro hy; exact False.elim (Finset.notMem_empty y hy)
        · rw [lftFinset_singleton_left]
          exact proposition_2_3_iii A (A.con_sing x)
    | right y =>
      exact False.elim (not_mem_right_of_mem_left A B z hx0 hp)

theorem inrMap_toElement_sumElementRht (z : (sumSystem A B).Element)
    (y0 : β) (hy0 : SumToken.right y0 ∈ z.carrier) :
    (inrMap A B).toElement (sumElementRht A B z y0 hy0) = z := by
  apply le_antisymm
  · intro p ⟨w, hw, ⟨hwCon, huCon, hl, hEnt⟩⟩
    cases p with
    | bot => exact factoid_3_2 (sumSystem A B) z
    | right y =>
      have hEnty : B.Ent w y := by
        have : rhtFinset ({SumToken.right y} : Finset (SumToken α β)) = {y} :=
          rhtFinset_singleton_right y
        simpa [this] using hEnt y (Finset.mem_singleton_self y)
      exact (sumElementRht A B z y0 hy0).closed w y hw hEnty
    | left x =>
      have : lftFinset ({SumToken.left x} : Finset (SumToken α β)) = {x} :=
        lftFinset_singleton_left x
      exact False.elim (Finset.singleton_ne_empty x (this ▸ hl))
  · intro p hp
    cases p with
    | bot =>
      refine ⟨∅, fun _ h => False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 h)), ?_⟩
      exact ⟨B.con_empty, (sumSystem A B).con_sing _, by rw [lftFinset_singleton_bot],
        B.entSet_empty _⟩
    | right y =>
      refine ⟨{y}, ?_, ?_⟩
      · intro b hb
        have : b = y := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
        subst this; exact hp
      · refine ⟨B.con_sing y, (sumSystem A B).con_sing _, ?_, ?_⟩
        · ext x; constructor
          · intro hx
            have : SumToken.left x ∈ ({SumToken.right y} : Finset _) := (mem_lftFinset).1 hx
            exact False.elim (nomatch Finset.mem_singleton.mp this)
          · intro hx; exact False.elim (Finset.notMem_empty x hx)
        · rw [rhtFinset_singleton_right]
          exact proposition_2_3_iii B (B.con_sing y)
    | left x =>
      exact False.elim (not_mem_right_of_mem_left A B z hp hy0)

theorem eq_botElement_of_no_injections (z : (sumSystem A B).Element)
    (hL : ∀ x : α, SumToken.left x ∉ z.carrier)
    (hR : ∀ y : β, SumToken.right y ∉ z.carrier) :
    z = (sumSystem A B).botElement := by
  apply le_antisymm
  · intro p hp
    cases p with
    | bot =>
      change SumToken.bot ∈ (sumSystem A B).botElement.carrier
      exact (sumSystem A B).ent_refl ((sumSystem A B).con_sing _) (Finset.mem_singleton_self _)
    | left x => exact False.elim (hL x hp)
    | right y => exact False.elim (hR y hp)
  · exact botElement_le (sumSystem A B) z

/-- Choice-free emptiness dichotomy for `lftFinset` (avoids `Finset.decidableEq`). -/
theorem lftFinset_eq_empty_or_mem (u : Finset (SumToken α β)) :
    lftFinset u = ∅ ∨ ∃ x, x ∈ lftFinset u := by
  induction u using Finset.induction_on with
  | empty =>
    exact Or.inl lftFinset_empty
  | insert p s _hp ih =>
    cases p with
    | left x =>
      exact Or.inr ⟨x, by rw [lftFinset_insert_left]; exact Finset.mem_insert_self _ _⟩
    | right y =>
      rw [lftFinset_insert_right]; exact ih
    | bot =>
      rw [lftFinset_insert_bot]; exact ih

/-- Choice-free emptiness dichotomy for `rhtFinset`. -/
theorem rhtFinset_eq_empty_or_mem (u : Finset (SumToken α β)) :
    rhtFinset u = ∅ ∨ ∃ y, y ∈ rhtFinset u := by
  induction u using Finset.induction_on with
  | empty =>
    exact Or.inl rhtFinset_empty
  | insert p s _hp ih =>
    cases p with
    | right y =>
      exact Or.inr ⟨y, by rw [rhtFinset_insert_right]; exact Finset.mem_insert_self _ _⟩
    | left x =>
      rw [rhtFinset_insert_left]; exact ih
    | bot =>
      rw [rhtFinset_insert_bot]; exact ih

theorem entSet_liftLft_of_left_only {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (hr : rhtFinset u = ∅) :
    (sumSystem A B).EntSet (liftSumLeft (β := β) (lftFinset u)) u := by
  intro p hp
  cases p with
  | bot =>
    exact ⟨SumCon_liftSumLeft A B (lft_mem_Con_of_SumCon_rht_empty A B hu hr), trivial⟩
  | left x =>
    have hx : x ∈ lftFinset u := (mem_lftFinset).2 hp
    refine ⟨SumCon_liftSumLeft A B (lft_mem_Con_of_SumCon_rht_empty A B hu hr), ⟨?_, ?_⟩⟩
    · rw [lftFinset_liftSumLeft]; exact Finset.ne_empty_of_mem hx
    · rw [lftFinset_liftSumLeft]
      exact A.ent_refl (lft_mem_Con_of_SumCon_rht_empty A B hu hr) hx
  | right y =>
    exact False.elim (by
      have : y ∈ rhtFinset u := (mem_rhtFinset).2 hp
      rw [hr] at this
      exact Finset.notMem_empty _ this)

theorem entSet_liftRht_of_right_only {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (hl : lftFinset u = ∅) :
    (sumSystem A B).EntSet (liftSumRight (α := α) (rhtFinset u)) u := by
  intro p hp
  cases p with
  | bot =>
    exact ⟨SumCon_liftSumRight A B (rht_mem_Con_of_SumCon_lft_empty A B hu hl), trivial⟩
  | right y =>
    have hy : y ∈ rhtFinset u := (mem_rhtFinset).2 hp
    refine ⟨SumCon_liftSumRight A B (rht_mem_Con_of_SumCon_lft_empty A B hu hl), ⟨?_, ?_⟩⟩
    · rw [rhtFinset_liftSumRight]; exact Finset.ne_empty_of_mem hy
    · rw [rhtFinset_liftSumRight]
      exact B.ent_refl (rht_mem_Con_of_SumCon_lft_empty A B hu hl) hy
  | left x =>
    exact False.elim (by
      have : x ∈ lftFinset u := (mem_lftFinset).2 hp
      rw [hl] at this
      exact Finset.notMem_empty _ this)

theorem subset_botElement_of_projections_empty {u : Finset (SumToken α β)}
    (hl : lftFinset u = ∅) (hr : rhtFinset u = ∅) :
    (↑u : Set (SumToken α β)) ⊆ (sumSystem A B).botElement.carrier := by
  intro p hp
  have hp' : p ∈ u := Finset.mem_coe.1 hp
  cases p with
  | bot =>
    exact (sumSystem A B).ent_refl ((sumSystem A B).con_sing _) (Finset.mem_singleton_self _)
  | left x =>
    exact False.elim (by
      have : x ∈ lftFinset u := (mem_lftFinset).2 hp'
      rw [hl] at this; exact Finset.notMem_empty _ this)
  | right y =>
    exact False.elim (by
      have : y ∈ rhtFinset u := (mem_rhtFinset).2 hp'
      rw [hr] at this; exact Finset.notMem_empty _ this)

theorem entSet_empty_of_rel_bot_like (h : ApproximableMap (sumSystem A B) C)
    (hbot : h.toElement (sumSystem A B).botElement = C.botElement)
    {u : Finset (SumToken α β)} {s : Finset γ}
    (hu : SumCon A B u) (hs : s ∈ C.Con) (hl : lftFinset u = ∅) (hr : rhtFinset u = ∅)
    (hh : h.rel u s) : C.EntSet ∅ s := by
  have hsub := subset_botElement_of_projections_empty A B hl hr
  have hcl : (sumSystem A B).closure u hu ≤ (sumSystem A B).botElement := by
    intro p hp
    exact (sumSystem A B).botElement.closed u p hsub hp
  have hle : C.closure s hs ≤ C.botElement := by
    have := (h.rel_iff_closure_le hu hs).1 hh
    have := le_trans this (toElement_mono h hcl)
    rwa [hbot] at this
  intro Y hY
  have hY' : Y ∈ (C.closure s hs).carrier := C.subset_closure hs hY
  have hbotY : Y ∈ C.botElement.carrier := hle hY'
  exact C.ent_trans C.con_empty (C.con_sing C.bot)
    (fun _ hz => by
      have : _ = C.bot := Finset.mem_singleton.mp hz
      subst this; exact C.ent_bot C.con_empty)
    hbotY

theorem entSet_u_of_inl_witness {u u' : Finset (SumToken α β)} {v : Finset α}
    (hlne : lftFinset u ≠ ∅) (hinl : (inlMap A B).rel v u')
    (huv : A.EntSet (lftFinset u) v) (hu : SumCon A B u)
    (hr : rhtFinset u = ∅) :
    (sumSystem A B).EntSet u u' := by
  intro p hp
  have ⟨hv, hu', hr', hEnt⟩ := hinl
  cases p with
  | bot => exact ⟨hu, trivial⟩
  | left x =>
    have hx : x ∈ lftFinset u' := (mem_lftFinset).2 hp
    have hAx : A.Ent v x := hEnt x hx
    have hAx' : A.Ent (lftFinset u) x :=
      A.ent_trans (lft_mem_Con_of_SumCon_rht_empty A B hu hr) hv huv hAx
    exact ⟨hu, ⟨hlne, hAx'⟩⟩
  | right y =>
    exact False.elim (by
      have : y ∈ rhtFinset u' := (mem_rhtFinset).2 hp
      rw [hr'] at this; exact Finset.notMem_empty _ this)

theorem entSet_u_of_inr_witness {u u' : Finset (SumToken α β)} {w : Finset β}
    (hrne : rhtFinset u ≠ ∅) (hinr : (inrMap A B).rel w u')
    (huw : B.EntSet (rhtFinset u) w) (hu : SumCon A B u)
    (hl : lftFinset u = ∅) :
    (sumSystem A B).EntSet u u' := by
  intro p hp
  have ⟨hw, hu', hl', hEnt⟩ := hinr
  cases p with
  | bot => exact ⟨hu, trivial⟩
  | right y =>
    have hy : y ∈ rhtFinset u' := (mem_rhtFinset).2 hp
    have hBy : B.Ent w y := hEnt y hy
    have hBy' : B.Ent (rhtFinset u) y :=
      B.ent_trans (rht_mem_Con_of_SumCon_lft_empty A B hu hl) hw huw hBy
    exact ⟨hu, ⟨hrne, hBy'⟩⟩
  | left x =>
    exact False.elim (by
      have : x ∈ lftFinset u' := (mem_lftFinset).2 hp
      rw [hl'] at this; exact Finset.notMem_empty _ this)

/-- Uniqueness of copairing (Scott Prop 6.4). -/
theorem copairMap_unique (f : ApproximableMap A C) (g : ApproximableMap B C)
    (h : ApproximableMap (sumSystem A B) C)
    (hinl : comp h (inlMap A B) = f) (hinr : comp h (inrMap A B) = g)
    (hbot : h.toElement (sumSystem A B).botElement = C.botElement) :
    h = copairMap A B f g := by
  refine ApproximableMap.ext fun u s => ?_
  constructor
  · intro hh
    have hu : SumCon A B u := h.rel_dom hh
    have hs : s ∈ C.Con := h.rel_cod hh
    refine ⟨hu, hs, ?_⟩
    rcases lftFinset_eq_empty_or_mem u with hl | ⟨x0, hx0⟩
    · rcases rhtFinset_eq_empty_or_mem u with hr | ⟨y0, hy0⟩
      · exact Or.inl (entSet_empty_of_rel_bot_like A B h hbot hu hs hl hr hh)
      · have hl' : lftFinset u = ∅ := hl
        have hg : g.rel (rhtFinset u) s := by
          have hinr' : (comp h (inrMap A B)).rel (rhtFinset u) s := by
            refine ⟨liftSumRight (α := α) (rhtFinset u), ?_, ?_⟩
            · exact ⟨rht_mem_Con_of_SumCon_lft_empty A B hu hl',
                SumCon_liftSumRight A B (rht_mem_Con_of_SumCon_lft_empty A B hu hl'),
                lftFinset_liftSumRight (α := α) _, by
                  rw [rhtFinset_liftSumRight]
                  exact proposition_2_3_iii B
                    (rht_mem_Con_of_SumCon_lft_empty A B hu hl')⟩
            · exact h.mono hh (entSet_liftRht_of_right_only A B hu hl')
                (proposition_2_3_iii C hs)
                (SumCon_liftSumRight A B (rht_mem_Con_of_SumCon_lft_empty A B hu hl')) hs
          simpa [hinr] using hinr'
        exact Or.inr (Or.inr ⟨Finset.ne_empty_of_mem hy0, hg⟩)
    · have hne : lftFinset u ≠ ∅ := Finset.ne_empty_of_mem hx0
      have hr : rhtFinset u = ∅ := SumCon_rht_empty_of_lft_nonempty A B hu hne
      have hf : f.rel (lftFinset u) s := by
        have hinl' : (comp h (inlMap A B)).rel (lftFinset u) s := by
          refine ⟨liftSumLeft (β := β) (lftFinset u), ?_, ?_⟩
          · exact ⟨lft_mem_Con_of_SumCon_rht_empty A B hu hr,
              SumCon_liftSumLeft A B (lft_mem_Con_of_SumCon_rht_empty A B hu hr),
              rhtFinset_liftSumLeft (β := β) _, by
                rw [lftFinset_liftSumLeft]
                exact proposition_2_3_iii A
                  (lft_mem_Con_of_SumCon_rht_empty A B hu hr)⟩
          · exact h.mono hh (entSet_liftLft_of_left_only A B hu hr)
              (proposition_2_3_iii C hs)
              (SumCon_liftSumLeft A B (lft_mem_Con_of_SumCon_rht_empty A B hu hr)) hs
        simpa [hinl] using hinl'
      exact Or.inr (Or.inl ⟨hne, hf⟩)
  · intro hc
    rcases hc with ⟨hu, hs, hcop⟩
    rcases hcop with hE | ⟨hne, hf⟩ | ⟨hne, hg⟩
    · have hb : h.rel ∅ s :=
        h.mono h.empty_rel ((sumSystem A B).entSet_empty _) hE
          (sumSystem A B).con_empty hs
      exact h.mono hb ((sumSystem A B).entSet_empty _) (proposition_2_3_iii C hs) hu hs
    · have : (comp h (inlMap A B)).rel (lftFinset u) s := by simpa [hinl] using hf
      rcases this with ⟨u', hinl', hh'⟩
      have hr : rhtFinset u = ∅ := SumCon_rht_empty_of_lft_nonempty A B hu hne
      have hEnt : (sumSystem A B).EntSet u u' :=
        entSet_u_of_inl_witness A B hne hinl'
          (proposition_2_3_iii A (lft_mem_Con_of_SumCon_rht_empty A B hu hr)) hu hr
      exact h.mono hh' hEnt (proposition_2_3_iii C hs) hu hs
    · have : (comp h (inrMap A B)).rel (rhtFinset u) s := by simpa [hinr] using hg
      rcases this with ⟨u', hinr', hh'⟩
      have hl : lftFinset u = ∅ := SumCon_lft_empty_of_rht_nonempty A B hu hne
      have hEnt : (sumSystem A B).EntSet u u' :=
        entSet_u_of_inr_witness A B hne hinr'
          (proposition_2_3_iii B (rht_mem_Con_of_SumCon_lft_empty A B hu hl)) hu hl
      exact h.mono hh' hEnt (proposition_2_3_iii C hs) hu hs

end ApproximableMap

end InfoSys

end Scott1982

-- Vendor 1972 — Scott1972.ContinuousLattice.Specialization (from vendor/scott1972/Scott1972/ContinuousLattice/Specialization.lean)

/-!
# Specialization order and Scott topology (Scott 1972, §2 opening)

Scott's §2 begins with the specialization order on a `T₀`-space and the induced (Scott)
topology on a complete lattice. Proposition 2.1 (monotone nets and least upper bounds) is
split into its two directions; the convergence-to-below direction is the mathematically
heavier half and is recorded as `proposition_2_1_of_le`.
-/

namespace Scott1972.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]

/-! ### Specialization order -/

/-- **Scott 1972, §2.** The *specialization order*: `x ⊑ y` when `x ∈ U` open implies `y ∈ U`. -/
def SpecializationLe (x y : X) : Prop :=
  ∀ U, IsOpen U → x ∈ U → y ∈ U

instance specializationPreorder : Preorder X where
  le := SpecializationLe
  le_refl x := fun _ _ hx => hx
  le_trans x y z hxy hyz U hU hxU := hyz U hU (hxy U hU hxU)

theorem specializationLe_antisymm [T0Space X] {x y : X}
    (hxy : SpecializationLe x y) (hyx : SpecializationLe y x) : x = y :=
  Inseparable.eq (inseparable_iff_specializes_and.2
    ⟨specializes_iff_forall_open.2 fun s hs hy => hyx s hs hy,
     specializes_iff_forall_open.2 fun s hs hx => hxy s hs hx⟩)

/-- Scott's specialization order is the reverse of Mathlib's `Specializes` convention. -/
theorem specializationLe_iff_specializes {x y : X} :
    SpecializationLe x y ↔ y ⤳ x :=
  specializes_iff_forall_open.symm

/-- Continuous maps preserve Scott's specialization order. -/
theorem SpecializationLe.map {Y : Type*} [TopologicalSpace Y] {x y : X}
    (hxy : SpecializationLe x y) {f : X → Y} (hf : Continuous f) :
    SpecializationLe (f x) (f y) := by
  intro U hU hxU
  exact hxy (f ⁻¹' U) (hU.preimage hf) hxU

/-! ### Scott topology from `ScottOpen` -/

/-- Scott's induced topology on a complete lattice, realized as mathlib's Scott topology. -/
@[reducible] noncomputable def scottTopologicalSpace : TopologicalSpace D :=
  Topology.scott D univ

theorem ScottOpen_iff_dirSupInacc {U : Set D} : ScottOpen U ↔ IsUpperSet U ∧ DirSupInacc U := by
  constructor
  · intro ⟨hU, hU'⟩
    refine ⟨hU, fun d hd₁ hd₂ a ha hmem => ?_⟩
    rw [← IsLUB.sSup_eq ha] at hmem
    obtain ⟨s, hs, hsU⟩ := hU' hd₁ hd₂ hmem
    exact ⟨s, hs, hsU⟩
  · intro ⟨hU, hU'⟩
    refine ⟨hU, fun d hd₁ hd₂ hmem => ?_⟩
    obtain ⟨s, hs, hsU⟩ := hU' hd₁ hd₂ (isLUB_sSup d) hmem
    exact ⟨s, hs, hsU⟩

theorem isOpen_iff_scottOpen {U : Set D} : @IsOpen D scottTopologicalSpace U ↔ ScottOpen U := by
  rw [ScottOpen_iff_dirSupInacc, scottTopologicalSpace]
  have hinst : @IsScott D univ _ (Topology.scott D univ) :=
    @IsScott.mk D univ _ (Topology.scott D univ) rfl
  simpa [dirSupInaccOn_univ] using
    @IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn D univ _ (Topology.scott D univ) U hinst

/-- Scott-open sets in our sense agree with mathlib's Scott topology (alias). -/
theorem isOpen_scott_iff_scottOpen {U : Set D} :
    @IsOpen D (Topology.scott D univ) U ↔ ScottOpen U :=
  isOpen_iff_scottOpen

/-! ### Monotone nets and Proposition 2.1 -/

variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]

def IsMonotoneNet (x : ι → D) : Prop :=
  Monotone x

def ScottConvergesTo (x : ι → D) (y : D) : Prop :=
  ∀ U, ScottOpen U → y ∈ U → ∃ i, ∀ j ≥ i, x j ∈ U

variable {x : ι → D} {L y : D}

/-- **Scott 1972, Proposition 2.1 (backward).** If `y ≤ L` and `L` is  the lub of a monotone
net, then the net converges to `y` in the Scott topology. -/
theorem proposition_2_1_of_le [Nonempty ι] (hx : IsMonotoneNet x) (hL : IsLUB (range x) L)
    (hyL : y ≤ L) : ScottConvergesTo x y := by
  intro U hU hyU
  have hdir : DirectedOn (· ≤ ·) (range x) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := IsDirected.directed (r := (· ≤ ·)) i j
    exact ⟨x k, ⟨k, rfl⟩, hx hik, hx hjk⟩
  have hLU : sSup (range x) ∈ U := by
    rw [IsLUB.sSup_eq hL]
    exact hU.1 hyL hyU
  obtain ⟨s, hsS, hsU⟩ := hU.2 (Set.range_nonempty x) hdir hLU
  obtain ⟨i₀, rfl⟩ := hsS
  refine ⟨i₀, fun j hj => hU.1 (hx hj) hsU⟩

/-- The complement of a principal lower set `Iic L` is Scott-open: it is an upper set, and it
is inaccessible by directed suprema because if every member of a directed `S` lies below `L`
then so does `⊔S`. -/
theorem scottOpen_not_le (L : D) : ScottOpen {z : D | ¬ z ≤ L} := by
  refine ⟨fun a b hab ha hb => ha (le_trans hab hb), fun S hSne hSdir hmem => ?_⟩
  by_contra hcon
  refine hmem (sSup_le fun s hs => ?_)
  by_contra hsL
  exact hcon ⟨s, hs, hsL⟩

/-- The specialization order of the Scott topology is the original lattice order. -/
theorem specializationLe_scott_iff {x y : D} :
    @SpecializationLe D scottTopologicalSpace x y ↔ x ≤ y := by
  constructor
  · intro hxy
    by_contra h
    exact hxy {z | ¬ z ≤ y} (isOpen_iff_scottOpen.mpr (scottOpen_not_le y)) h (by simp)
  · intro hxy U hU hxU
    exact (isOpen_iff_scottOpen.mp hU).1 hxy hxU

/-- The Scott topology of a partial order is `T₀`. -/
theorem scottTopology_t0Space : @T0Space D scottTopologicalSpace := by
  letI : TopologicalSpace D := scottTopologicalSpace
  constructor
  intro x y hxy
  apply le_antisymm
  · rw [← specializationLe_scott_iff]
    intro U hU hxU
    exact (hxy.mem_open_iff hU).mp hxU
  · rw [← specializationLe_scott_iff]
    intro U hU hyU
    exact (hxy.mem_open_iff hU).mpr hyU

omit [IsDirected ι (· ≤ ·)] in
/-- **Scott 1972, Proposition 2.1 (forward).** If a monotone net converges to `y` in the Scott
topology and `L` is its least upper bound, then `y ≤ L`. -/
theorem proposition_2_1_le_of_converges (hL : IsLUB (range x) L)
    (hconv : ScottConvergesTo x y) : y ≤ L := by
  by_contra hyL
  obtain ⟨i, hi⟩ := hconv {z : D | ¬ z ≤ L} (scottOpen_not_le L) hyL
  exact hi i le_rfl (hL.1 ⟨i, rfl⟩)

/-- **Scott 1972, Proposition 2.1.** A monotone net with least upper bound `L` converges to
`y` in the Scott topology iff `y ⊑ L = ⊔ {xᵢ}`. -/
theorem proposition_2_1 [Nonempty ι] (hx : IsMonotoneNet x) (hL : IsLUB (range x) L) :
    ScottConvergesTo x y ↔ y ≤ L :=
  ⟨fun hconv => proposition_2_1_le_of_converges hL hconv, proposition_2_1_of_le hx hL⟩

end Scott1972.ContinuousLattice

-- Vendor 1972 — Scott1972.ContinuousLattice.ScottMaps (from vendor/scott1972/Scott1972/ContinuousLattice/ScottMaps.lean)

/-!
# Scott-continuous maps (Scott 1972, §2.5–2.7)
-/

namespace Scott1972.ContinuousLattice

open Set Topology

variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

def PreservesDirectedSup (f : D → D') : Prop :=
  ∀ ⦃S : Set D⦄, S.Nonempty → DirectedOn (· ≤ ·) S → f (sSup S) = sSup (f '' S)

theorem preservesDirectedSup_monotone {f : D → D'} (hf : PreservesDirectedSup f) :
    Monotone f := by
  intro x y hxy
  have hdir : DirectedOn (· ≤ ·) ({x, y} : Set D) := directedOn_pair hxy
  have hS : ({x, y} : Set D).Nonempty := ⟨x, Set.mem_insert _ _⟩
  have hsup : sSup ({x, y} : Set D) = y := by
    calc sSup ({x, y} : Set D) = x ⊔ y := sSup_pair
      _ = y := by apply le_antisymm; exact sup_le hxy le_rfl; exact le_sup_right
  have heq := hf hS hdir
  rw [hsup, Set.image_pair] at heq
  exact le_trans (le_sSup (Set.mem_insert _ _)) heq.symm.le

theorem scottOpen_preimage {f : D → D'} (hf : PreservesDirectedSup f) {U : Set D'}
    (hU : ScottOpen U) : ScottOpen (f ⁻¹' U) := by
  have hmono := preservesDirectedSup_monotone hf
  refine ⟨fun a b hab ha => hU.1 (hmono hab) ha, fun S hS hSdir hmem => ?_⟩
  rw [Set.mem_preimage] at hmem
  have hmem' : sSup (f '' S) ∈ U := by rw [← hf hS hSdir]; exact hmem
  obtain ⟨s, hsS, hsU⟩ := hU.2 (Set.image_nonempty.2 hS)
    (fun s hs t ht => by
      obtain ⟨a, haS, rfl⟩ := hs
      obtain ⟨b, hbS, rfl⟩ := ht
      obtain ⟨c, hcS, hac, hbc⟩ := hSdir a haS b hbS
      exact ⟨f c, Set.mem_image_of_mem f hcS, hmono hac, hmono hbc⟩) hmem'
  obtain ⟨a, haS, rfl⟩ := hsS
  exact ⟨a, haS, Set.mem_preimage.2 hsU⟩

theorem continuous_of_preservesDirectedSup {f : D → D'} (hf : PreservesDirectedSup f) :
    @Continuous D D' scottTopologicalSpace scottTopologicalSpace f := by
  rw [continuous_def]
  intro U hU
  rw [isOpen_iff_scottOpen] at hU ⊢
  exact scottOpen_preimage hf hU

theorem continuous_preservesDirectedSup {f : D → D'}
    (hf : @Continuous D D' scottTopologicalSpace scottTopologicalSpace f) :
    PreservesDirectedSup f := by
  have hD : @IsScott D univ _ (Topology.scott D univ) :=
    @IsScott.mk D univ _ (Topology.scott D univ) rfl
  have hD' : @IsScott D' univ _ (Topology.scott D' univ) :=
    @IsScott.mk D' univ _ (Topology.scott D' univ) rfl
  have hsc : ScottContinuous f :=
    scottContinuousOn_univ.1 <|
      (@Topology.IsScott.scottContinuousOn_iff_continuous D D' _
        (Topology.scott D univ) _ (Topology.scott D' univ) hD' f univ hD
        (fun _ _ _ => trivial)).2 hf
  intro S hS hSdir
  exact (hsc hS hSdir (isLUB_sSup S)).sSup_eq.symm

/-- **Scott 1972, Proposition 2.5.** Scott continuity ↔ preservation of directed suprema. -/
theorem proposition_2_5 (f : D → D') :
    (@Continuous D D' scottTopologicalSpace scottTopologicalSpace f) ↔
      PreservesDirectedSup f :=
  ⟨continuous_preservesDirectedSup, fun hf => continuous_of_preservesDirectedSup hf⟩

/-! ### Proposition 2.6 -/

/-- **Scott 1972, Proposition 2.6.** A function of several variables between complete lattices is
(Scott-)continuous jointly iff it is continuous in each variable separately. Continuity is phrased
as preservation of directed suprema (Proposition 2.5); it suffices to treat two variables, the
product `D × D'` carrying the componentwise complete-lattice structure (whose induced topology is
the product topology). -/
theorem proposition_2_6 (f : D × D' → D'') :
    PreservesDirectedSup f ↔
      (∀ y, PreservesDirectedSup fun x => f (x, y)) ∧
        (∀ x, PreservesDirectedSup fun y => f (x, y)) := by
  constructor
  · -- joint continuity ⟹ separate continuity (precompose with the continuous slice maps)
    intro hf
    refine ⟨fun y S hS hSdir => ?_, fun x S hS hSdir => ?_⟩
    · set T : Set (D × D') := (fun x => (x, y)) '' S with hT
      have hTne : T.Nonempty := hS.image _
      have hTdir : DirectedOn (· ≤ ·) T := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        obtain ⟨c, hc, hac, hbc⟩ := hSdir a ha b hb
        exact ⟨(c, y), Set.mem_image_of_mem _ hc, ⟨hac, le_rfl⟩, ⟨hbc, le_rfl⟩⟩
      have hfst : Prod.fst '' T = S := by rw [hT, Set.image_image]; simp
      have hsnd : Prod.snd '' T = {y} := by rw [hT, Set.image_image]; exact hS.image_const y
      have hsupT : sSup T = (sSup S, y) := by
        have e1 : (sSup T).1 = sSup S := by rw [Prod.fst_sSup, hfst]
        have e2 : (sSup T).2 = y := by rw [Prod.snd_sSup, hsnd, sSup_singleton]
        exact Prod.ext_iff.mpr ⟨e1, e2⟩
      have h := hf hTne hTdir
      rw [hsupT, hT, Set.image_image] at h
      simpa using h
    · set T : Set (D × D') := (fun y => (x, y)) '' S with hT
      have hTne : T.Nonempty := hS.image _
      have hTdir : DirectedOn (· ≤ ·) T := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        obtain ⟨c, hc, hac, hbc⟩ := hSdir a ha b hb
        exact ⟨(x, c), Set.mem_image_of_mem _ hc, ⟨le_rfl, hac⟩, ⟨le_rfl, hbc⟩⟩
      have hfst : Prod.fst '' T = {x} := by rw [hT, Set.image_image]; exact hS.image_const x
      have hsnd : Prod.snd '' T = S := by rw [hT, Set.image_image]; simp
      have hsupT : sSup T = (x, sSup S) := by
        have e1 : (sSup T).1 = x := by rw [Prod.fst_sSup, hfst, sSup_singleton]
        have e2 : (sSup T).2 = sSup S := by rw [Prod.snd_sSup, hsnd]
        exact Prod.ext_iff.mpr ⟨e1, e2⟩
      have h := hf hTne hTdir
      rw [hsupT, hT, Set.image_image] at h
      simpa using h
  · -- separate continuity ⟹ joint continuity (Scott 1972's directedness argument)
    rintro ⟨h1, h2⟩ Sstar hne hdir
    have hmono1 : ∀ y, Monotone fun x => f (x, y) := fun y => preservesDirectedSup_monotone (h1 y)
    have hmono2 : ∀ x, Monotone fun y => f (x, y) := fun x => preservesDirectedSup_monotone (h2 x)
    have hmono : Monotone f := by
      rintro ⟨a, b⟩ ⟨c, d⟩ hpq
      exact le_trans (hmono1 b hpq.1) (hmono2 c hpq.2)
    have hSne : (Prod.fst '' Sstar).Nonempty := hne.image _
    have hS'ne : (Prod.snd '' Sstar).Nonempty := hne.image _
    have hSdir : DirectedOn (· ≤ ·) (Prod.fst '' Sstar) := hdir.fst
    have hS'dir : DirectedOn (· ≤ ·) (Prod.snd '' Sstar) := hdir.snd
    have hsupStar : sSup Sstar = (sSup (Prod.fst '' Sstar), sSup (Prod.snd '' Sstar)) :=
      Prod.ext_iff.mpr ⟨Prod.fst_sSup _, Prod.snd_sSup _⟩
    apply le_antisymm
    · rw [hsupStar]
      have e1 : f (sSup (Prod.fst '' Sstar), sSup (Prod.snd '' Sstar))
          = sSup ((fun x => f (x, sSup (Prod.snd '' Sstar))) '' (Prod.fst '' Sstar)) :=
        h1 (sSup (Prod.snd '' Sstar)) hSne hSdir
      rw [e1]
      apply sSup_le
      rintro _ ⟨x, hx, rfl⟩
      show f (x, sSup (Prod.snd '' Sstar)) ≤ sSup (f '' Sstar)
      have e2 : f (x, sSup (Prod.snd '' Sstar))
          = sSup ((fun y => f (x, y)) '' (Prod.snd '' Sstar)) :=
        h2 x hS'ne hS'dir
      rw [e2]
      apply sSup_le
      rintro _ ⟨y, hy, rfl⟩
      show f (x, y) ≤ sSup (f '' Sstar)
      obtain ⟨p, hpS, hpfst⟩ := hx
      obtain ⟨q, hqS, hqsnd⟩ := hy
      obtain ⟨r, hrS, hpr, hqr⟩ := hdir p hpS q hqS
      have hxr : x ≤ r.1 := hpfst ▸ hpr.1
      have hyr : y ≤ r.2 := hqsnd ▸ hqr.2
      calc f (x, y) ≤ f (r.1, r.2) := hmono ⟨hxr, hyr⟩
        _ = f r := by rw [Prod.mk.eta]
        _ ≤ sSup (f '' Sstar) := le_sSup (Set.mem_image_of_mem f hrS)
    · apply sSup_le
      rintro _ ⟨p, hp, rfl⟩
      exact hmono (le_sSup hp)

/-! ### Proposition 2.7 -/

/-- **Scott 1972, Proposition 2.7 (join).** Binary join is Scott-continuous on every complete
lattice; this is the `⊔`-part of Scott's 2.7. -/
theorem proposition_2_7_sup :
    @Continuous (D × D) D scottTopologicalSpace scottTopologicalSpace (fun p : D × D => p.1 ⊔ p.2) :=
  continuous_of_preservesDirectedSup <| by
    intro S hS hSdir
    simpa using (ScottContinuous.sup₂ (β := D) (d := S) hS hSdir (isLUB_sSup S)).sSup_eq.symm

theorem meet_preservesDirectedSup (x : D) (hD : IsContinuousLattice D) :
    PreservesDirectedSup (fun z => x ⊓ z) := by
  intro S hS hSdir
  apply le_antisymm
  · have hle : sSup {t | t ≪ x ⊓ sSup S} ≤ sSup (Set.image (fun z => x ⊓ z) S) := by
      apply sSup_le
      intro t ht
      obtain ⟨w, hwS, ht_w⟩ := (wayBelow_sSup_iff hS hSdir).1 (ht.trans_le inf_le_right)
      have hmem : x ⊓ w ∈ Set.image (fun z : D => x ⊓ z) S :=
        Set.mem_image_of_mem (fun z => x ⊓ z) hwS
      have hbound : x ⊓ w ≤ sSup (Set.image (fun z => x ⊓ z) S) := le_sSup hmem
      exact (le_inf (ht.le.trans inf_le_left) ht_w.le).trans hbound
    dsimp only
    rw [← hD.sSup_wayBelow (x ⊓ sSup S)]
    exact hle
  · apply sSup_le
    intro z hz
    obtain ⟨w, hwS, rfl⟩ := hz
    exact inf_le_inf le_rfl (le_sSup hwS)

/-- **Scott 1972, Proposition 2.7 (meet, separate).** On a continuous lattice, `x ↦ x ⊓ y`
and `y ↦ x ⊓ y` are Scott-continuous; Scott's full 2.7 also covers joint continuity on the
product via Proposition 2.6. -/
theorem proposition_2_7_inf_left (hD : IsContinuousLattice D) (y : D) :
    @Continuous D D scottTopologicalSpace scottTopologicalSpace (fun x => x ⊓ y) :=
  continuous_of_preservesDirectedSup <| by
    intro S' hS' hSdir'
    rw [show (fun x => x ⊓ y) = fun z => y ⊓ z from funext fun x => inf_comm x y]
    have h := meet_preservesDirectedSup y hD
    exact h (S := S') hS' hSdir'

theorem proposition_2_7_inf_right (hD : IsContinuousLattice D) (x : D) :
    @Continuous D D scottTopologicalSpace scottTopologicalSpace (fun y => x ⊓ y) :=
  continuous_of_preservesDirectedSup (meet_preservesDirectedSup x hD)

end Scott1972.ContinuousLattice

-- Vendor 1972 — Scott1972.ContinuousLattice.FunctionSpaces (from vendor/scott1972/Scott1972/ContinuousLattice/FunctionSpaces.lean)

/-!
# Function spaces on continuous lattices (Scott 1972, §3)

Scott's §3 studies spaces of continuous maps `[X → Y]` with the topology of pointwise
convergence (subbasic sets `{f | f x ∈ U}`), the pointwise specialization order (3.2),
and the fact that `[D → D']` is a continuous lattice when `D → D']` is (3.3).

## March 1972 correction (Milner)

Scott's remark before Proposition 2.5 was mistaken: a `T₀`-topology on a complete lattice
need not have every open set Scott-open. The two extreme `T₀`-topologies inducing the same
order are generated by `{x | x ⋢ y}` (lower) and `{x | y ⊑ x}` (principal up-sets).
The corrected proofs of 2.9, 2.10, and 3.3 assume the given topology is *coarser* than
the Scott (lattice) topology (`scottTopologicalSpace ≤ τ` in mathlib). We revisit that
hypothesis when formalizing those results.

In the March 1972 correction (p. 135), Scott writes `⊔S′` (prime on the index, not on the
join): for `S ⊆ D` a subspace of ambient `D′`, `⊔S′` is the supremum of `S` computed in `D′`,
while `⊔S` is the supremum in the subspace `D`; the retraction identity is `j(⊔S′) = ⊔S`.
-/

namespace Scott1972.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

/-! ### Definition 3.1 -/

/-- Subbasic sets for Scott's function-space topology (pointwise convergence). -/
def scottFunctionEvalSubbasis (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :
    Set (Set (C(X, Y))) :=
  { W | ∃ (x : X) (U : Set Y), IsOpen U ∧ W = {f : C(X, Y) | f x ∈ U} }

/-- **Scott 1972, Definition 3.1.** The function space `[X → Y]` carries the topology
generated by `{f : f x ∈ U | x ∈ X, U open in Y}`. -/
@[reducible] noncomputable def scottFunctionTopology (X Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] : TopologicalSpace (C(X, Y)) :=
  generateFrom (scottFunctionEvalSubbasis X Y)

/-- The literal product topology on the underlying functions `X → Y`, restricted to continuous
maps.  This is the standard Mathlib realization of Scott's pointwise topology from Definition 3.1.
The topology arguments are explicit to avoid installing a second global topology on `C(X, Y)`. -/
@[reducible] noncomputable def continuousMapInducedPiTopology (X Y : Type*)
    [TopologicalSpace X] [TopologicalSpace Y] : TopologicalSpace C(X, Y) :=
  TopologicalSpace.induced (fun f : C(X, Y) => (f : X → Y))
    (@Pi.topologicalSpace X (fun _ => Y) (fun _ => inferInstance))

/-- Scott's notation `[X → Y]`: continuous maps with the pointwise (product) topology. -/
abbrev ScottFunctionSpace (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :=
  C(X, Y)

/-! ### Proposition 3.2 -/

theorem scottFunctionSubbasis_isOpen {x : X} {U : Set Y} (hU : IsOpen U) :
    @IsOpen (C(X, Y)) (scottFunctionTopology X Y) {f : C(X, Y) | f x ∈ U} :=
  isOpen_generateFrom_of_mem (s := {f : C(X, Y) | f x ∈ U}) ⟨x, U, hU, rfl⟩

/-- **Scott 1972, Definition 3.1.** Scott's topology generated by evaluation cylinders is exactly
the topology induced on continuous maps from Mathlib's Pi topology on all underlying functions. -/
theorem scottFunctionTopology_eq_induced_pi (X Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] :
    scottFunctionTopology X Y = continuousMapInducedPiTopology X Y := by
  apply le_antisymm
  · letI : TopologicalSpace C(X, Y) := scottFunctionTopology X Y
    change scottFunctionTopology X Y ≤ continuousMapInducedPiTopology X Y
    rw [← continuous_iff_le_induced]
    exact continuous_pi fun x =>
      continuous_def.2 fun U hU =>
        scottFunctionSubbasis_isOpen (X := X) (Y := Y) (x := x) hU
  · apply le_generateFrom_iff_subset_isOpen.2
    rintro W ⟨x, U, hU, rfl⟩
    change @IsOpen C(X, Y)
      (TopologicalSpace.induced (fun f : C(X, Y) => (f : X → Y))
        (@Pi.topologicalSpace X (fun _ => Y) (fun _ => inferInstance)))
      {f : C(X, Y) | f x ∈ U}
    rw [isOpen_induced_iff]
    exact ⟨{g : X → Y | g x ∈ U}, (@continuous_apply X (fun _ => Y)
      (fun _ => inferInstance) x).isOpen_preimage U hU, rfl⟩

def specializationLe_generateOpen (f g : C(X, Y)) (hfg : ∀ x, SpecializationLe (f x) (g x))
    {V : Set (C(X, Y))} (hV : GenerateOpen (scottFunctionEvalSubbasis X Y) V) (hf : f ∈ V) :
    g ∈ V :=
  match hV with
  | .basic W hW => by
    obtain ⟨x, U, hU, rfl⟩ := hW
    exact hfg x U hU hf
  | .univ => hf
  | .inter s t hs ht => by
    rcases hf with ⟨hfs, hft⟩
    exact Set.mem_inter (specializationLe_generateOpen f g hfg hs hfs)
      (specializationLe_generateOpen f g hfg ht hft)
  | .sUnion S hS => by
    obtain ⟨W, hWS, hfW⟩ := Set.mem_sUnion.mp hf
    exact Set.mem_sUnion.mpr ⟨W, hWS, specializationLe_generateOpen f g hfg (hS W hWS) hfW⟩

theorem scottFunctionSpecializationLe {f g : C(X, Y)} :
    letI := scottFunctionTopology X Y
    SpecializationLe f g ↔ ∀ x, SpecializationLe (f x) (g x) := by
  letI : TopologicalSpace (C(X, Y)) := scottFunctionTopology X Y
  constructor
  · intro hfg x U hU hfU
    exact hfg {h | h x ∈ U} (scottFunctionSubbasis_isOpen (X := X) (Y := Y) hU) hfU
  · intro hfg U hU hfU
    exact specializationLe_generateOpen f g hfg hU hfU

/-- **Scott 1972, Proposition 3.2.** The specialization order on `[X → Y]` is pointwise. -/
theorem proposition_3_2 {f g : C(X, Y)} :
    letI := scottFunctionTopology X Y
    (SpecializationLe f g ↔ ∀ x, SpecializationLe (f x) (g x)) :=
  scottFunctionSpecializationLe

/-! ### §3 on continuous lattices: pointwise lattice structure -/

/-- Continuous maps `D → D'` with Scott topologies on domain and codomain. -/
abbrev ScottC (D D' : Type*) [CompleteLattice D] [CompleteLattice D'] :=
  @ContinuousMap D D' scottTopologicalSpace scottTopologicalSpace

/-- Continuous maps between complete lattices with Scott's induced topologies. -/
def ScottMap (D : Type u) (D' : Type v) [CompleteLattice D] [CompleteLattice D'] : Type _ :=
  { f : D → D' // @Continuous D D' scottTopologicalSpace scottTopologicalSpace f }

namespace ScottMap

instance : CoeFun (ScottMap D D') (fun _ => D → D') where
  coe f := f.1

@[ext]
theorem ext {f g : ScottMap D D'} (h : ∀ x, f x = g x) : f = g :=
  Subtype.ext (funext h)

theorem continuous (f : ScottMap D D') :
    @Continuous D D' scottTopologicalSpace scottTopologicalSpace f :=
  f.2

theorem preservesDirectedSup_coe (f : ScottMap D D') (S : Set D) (hS : S.Nonempty)
    (hSdir : DirectedOn (· ≤ ·) S) :
    (f : D → D') (sSup S) = sSup (Set.image (f : D → D') S) := by
  have h := (proposition_2_5 (Subtype.val f)).mp f.property
  exact h hS hSdir

theorem monotone (f : ScottMap D D') : Monotone (f : D → D') :=
  preservesDirectedSup_monotone ((proposition_2_5 (Subtype.val f)).mp f.property)

theorem preservesDirectedSup_comp {f : D' → D''} {g : D → D'} (hf : PreservesDirectedSup f)
    (hg : PreservesDirectedSup g) : PreservesDirectedSup (f ∘ g) := by
  intro S hS hSdir
  have hmono : Monotone g := preservesDirectedSup_monotone hg
  have hdir' : DirectedOn (· ≤ ·) (g '' S) := by
    intro p hp q hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    obtain ⟨c, hc, hac, hbc⟩ := hSdir a ha b hb
    exact ⟨g c, Set.mem_image_of_mem g hc, hmono hac, hmono hbc⟩
  have hne : (g '' S).Nonempty := Set.image_nonempty.2 hS
  rw [Function.comp_apply, hg hS hSdir, hf hne hdir']
  congr 1
  exact (Set.image_comp f g S).symm

def comp (f : ScottMap D' D'') (g : ScottMap D D') : ScottMap D D'' :=
  ⟨f ∘ g, continuous_of_preservesDirectedSup (preservesDirectedSup_comp
    ((proposition_2_5 (Subtype.val f)).mp f.property)
    ((proposition_2_5 (Subtype.val g)).mp g.property))⟩

def const (c : D') : ScottMap D D' :=
  ⟨fun _ => c, continuous_of_preservesDirectedSup fun S hS _ => by
    obtain ⟨x, hx⟩ := hS
    apply le_antisymm
    · exact le_sSup ⟨x, hx, rfl⟩
    · apply sSup_le
      intro b hb
      obtain ⟨y, hy, rfl⟩ := hb
      exact le_rfl⟩

theorem pointwise_sup_preservesDirectedSup (f g : ScottMap D D') :
    PreservesDirectedSup (fun x => f x ⊔ g x) := by
  intro S hS hSdir
  show f (sSup S) ⊔ g (sSup S) = sSup (Set.image (fun x => f x ⊔ g x) S)
  rw [f.preservesDirectedSup_coe S hS hSdir, g.preservesDirectedSup_coe S hS hSdir]
  apply le_antisymm
  · apply sup_le
    · apply sSup_le
      intro b hb
      obtain ⟨s, hsS, rfl⟩ := hb
      exact le_trans le_sup_left (le_sSup (Set.mem_image_of_mem (fun z => f z ⊔ g z) hsS))
    · apply sSup_le
      intro b hb
      obtain ⟨s, hsS, rfl⟩ := hb
      exact le_trans le_sup_right (le_sSup (Set.mem_image_of_mem (fun z => f z ⊔ g z) hsS))
  · apply sSup_le
    intro b hb
    obtain ⟨s, hsS, rfl⟩ := hb
    exact sup_le (le_trans (le_sSup (Set.mem_image_of_mem f hsS)) le_sup_left)
      (le_trans (le_sSup (Set.mem_image_of_mem g hsS)) le_sup_right)

noncomputable def bot : ScottMap D D' :=
  const ⊥

def le {D : Type u} {D' : Type v} [CompleteLattice D] [CompleteLattice D']
    (f g : ScottMap D D') : Prop :=
  letI : LE D' :=
    (ChainCompletePartialOrder.instOfCompleteLattice
      (α := D')).toPartialOrder.toPreorder.toLE
  ∀ x, f x ≤ g x

noncomputable def sup (f g : ScottMap D D') : ScottMap D D' :=
  ⟨fun x => f x ⊔ g x, continuous_of_preservesDirectedSup (pointwise_sup_preservesDirectedSup f g)⟩

theorem pointwise_sSup_preservesDirectedSup (F : Set (ScottMap D D')) :
    PreservesDirectedSup (fun x => sSup (Set.image (fun f : ScottMap D D' => (f : D → D') x) F)) := by
  intro S hS hSdir
  set H := fun x => sSup (Set.image (fun f : ScottMap D D' => (f : D → D') x) F)
  show H (sSup S) = sSup (Set.image H S)
  apply le_antisymm
  · apply sSup_le
    intro b hb
    obtain ⟨f, hfF, rfl⟩ := hb
    change f (sSup S) ≤ sSup (Set.image H S)
    rw [f.preservesDirectedSup_coe S hS hSdir]
    apply sSup_le
    intro c hc
    obtain ⟨s, hsS, rfl⟩ := hc
    exact le_trans (le_sSup (Set.mem_image_of_mem (fun g : ScottMap D D' => (g : D → D') s) hfF))
      (le_sSup (Set.mem_image_of_mem H hsS))
  · apply sSup_le
    intro b hb
    obtain ⟨s, hsS, rfl⟩ := hb
    apply sSup_le
    intro c hc
    obtain ⟨f, hfF, rfl⟩ := hc
    exact le_trans (ScottMap.monotone f (le_sSup hsS))
      (le_sSup (Set.mem_image_of_mem (fun g : ScottMap D D' => (g : D → D') (sSup S)) hfF))

/-- The pointwise supremum function is Scott-continuous. Kept as a named
proof boundary so the Challenge fixes the function while leaving this proof open. -/
theorem sSupMaps_continuous {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (F : Set (ScottMap D D')) :
    @Continuous D D' scottTopologicalSpace scottTopologicalSpace
      (fun x => sSup (Set.image (fun f : ScottMap D D' => (f : D → D') x) F)) :=
  continuous_of_preservesDirectedSup (pointwise_sSup_preservesDirectedSup F)

noncomputable def sSupMaps {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (F : Set (ScottMap D D')) : ScottMap D D' :=
  ⟨fun x => sSup (Set.image (fun f : ScottMap D D' => (f : D → D') x) F),
    sSupMaps_continuous F⟩

theorem sSupMaps_apply (F : Set (ScottMap D D')) (x : D) :
    (sSupMaps F : D → D') x =
      sSup (Set.image (fun f : ScottMap D D' => (f : D → D') x) F) :=
  rfl

/-! ### The complete lattice `[D → D']` (Theorem 3.3, order content)

The pointwise order makes `ScottMap D D'` a partial order; `sSupMaps` gives suprema (pointwise,
since directed *and* arbitrary suprema of Scott maps are computed pointwise — Theorem 3.3). By
`completeLatticeOfSup` this is a complete lattice. Note infima are *not* pointwise (Scott's
warning); `completeLatticeOfSup` derives them as `sSup` of lower bounds. -/

/-- Reflexivity of the pointwise order. -/
theorem le_refl' {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (f : ScottMap D D') :
    ScottMap.le f f :=
  fun _ => le_refl _

/-- Transitivity of the pointwise order. -/
theorem le_trans' {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (f g h : ScottMap D D')
    (hfg : ScottMap.le f g)
    (hgh : ScottMap.le g h) : ScottMap.le f h :=
  fun x => le_trans (hfg x) (hgh x)

/-- Antisymmetry of the pointwise order. -/
theorem le_antisymm' {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (f g : ScottMap D D')
    (hfg : ScottMap.le f g)
    (hgf : ScottMap.le g f) : f = g :=
  ScottMap.ext fun x => le_antisymm (hfg x) (hgf x)

/-- Strict pointwise order induced by `ScottMap.le`. -/
def lt {D : Type u} {D' : Type v} [CompleteLattice D] [CompleteLattice D']
    (f g : ScottMap D D') : Prop :=
  ScottMap.le f g ∧ ¬ ScottMap.le g f

/-- The chosen strict pointwise order is `≤ ∧ ¬ ≥`. -/
theorem lt_iff_le_not_ge' {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (f g : ScottMap D D') :
    ScottMap.lt f g ↔
      ScottMap.le f g ∧ ¬ ScottMap.le g f :=
  Iff.rfl

instance instPartialOrder {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] : PartialOrder (ScottMap D D') where
  le := ScottMap.le
  lt := ScottMap.lt
  le_refl := le_refl'
  le_trans := le_trans'
  lt_iff_le_not_ge := lt_iff_le_not_ge'
  le_antisymm := le_antisymm'

theorem le_def {f g : ScottMap D D'} : f ≤ g ↔ ∀ x, (f : D → D') x ≤ g x := Iff.rfl

noncomputable instance instSupSet {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] : SupSet (ScottMap D D') := ⟨sSupMaps⟩

theorem sSup_apply (F : Set (ScottMap D D')) (x : D) :
    ((sSup F : ScottMap D D') : D → D') x =
      sSup (Set.image (fun f : ScottMap D D' => (f : D → D') x) F) :=
  rfl

theorem isLUB_sSup {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (F : Set (ScottMap D D')) :
    IsLUB F (sSup F) := by
  constructor
  · intro f hf
    rw [le_def]
    intro x
    rw [sSup_apply]
    exact le_sSup (Set.mem_image_of_mem _ hf)
  · intro g hg
    rw [le_def]
    intro x
    rw [sSup_apply]
    refine sSup_le ?_
    rintro _ ⟨f, hfF, rfl⟩
    exact (hg hfF) x

noncomputable instance instCompleteLattice {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] : CompleteLattice (ScottMap D D') :=
  completeLatticeOfSup (ScottMap D D') isLUB_sSup

/-- The identity Scott map. -/
def idMap : ScottMap D D :=
  ⟨fun x => x, continuous_of_preservesDirectedSup fun S _ _ => by
    show sSup S = sSup (Set.image (fun x => x) S)
    rw [Set.image_id']⟩

@[simp] theorem idMap_apply (x : D) : (idMap : ScottMap D D) x = x := rfl

@[simp] theorem comp_apply (f : ScottMap D' D'') (g : ScottMap D D') (x : D) :
    (f.comp g : D → D'') x = f (g x) := rfl

/-- The (completeLatticeOfSup-derived) binary join of Scott maps is computed pointwise. -/
theorem sup_apply (f g : ScottMap D D') (x : D) :
    ((f ⊔ g : ScottMap D D') : D → D') x = f x ⊔ g x := by
  have h : (f ⊔ g : ScottMap D D') = sSup ({f, g} : Set (ScottMap D D')) := rfl
  rw [h, sSup_apply, Set.image_pair]
  exact sSup_pair

/-- The bottom Scott map is the constant `⊥`. -/
theorem bot_apply (x : D) : ((⊥ : ScottMap D D') : D → D') x = ⊥ := by
  have h : (⊥ : ScottMap D D') = sSup (∅ : Set (ScottMap D D')) := rfl
  rw [h, sSup_apply, Set.image_empty, sSup_empty]

@[simp] theorem const_apply (c : D') (x : D) : (ScottMap.const c : D → D') x = c := rfl

end ScottMap

/-! ### Theorem 3.3 (core) -/

/-- **Scott 1972, Theorem 3.3 (directed sup).** Pointwise suprema of Scott-continuous maps are
Scott-continuous; this is the heart of Scott's proof that `[D → D']` is a complete lattice. -/
noncomputable def theorem_3_3_sSup (F : Set (ScottMap D D')) : ScottMap D D' :=
  ScottMap.sSupMaps F

/-- **Scott 1972, Theorem 3.3 (binary join).** Pointwise join of Scott-continuous maps is
Scott-continuous. -/
noncomputable def theorem_3_3_sup (f g : ScottMap D D') : ScottMap D D' :=
  ScottMap.sup f g

/-! ### Theorem 3.3 (`[D → D']` is a continuous lattice)

Scott's *step functions* `ē[e, e']` are the building blocks: `ē[e,e'](x) = e'` if `e ≪ x`, else
`⊥`. We encode the conditional value as `⨆ _ : e ≪ x, e'` (which is `e'` when `e ≪ x` and `⊥`
otherwise), avoiding any decidability assumption. Each step function is Scott-continuous (the
way-above set `{x | e ≪ x}` is Scott-open), is way below `f` whenever `e' ≪ f e`, and `f` is the
supremum of the step functions below it — whence `[D → D']` is a continuous lattice. -/

/-- The (value of the) step function `ē[e, e']` at `x`: `e'` if `e ≪ x`, else `⊥`. -/
noncomputable def stepFun (e : D) (e' : D') (x : D) : D' := ⨆ _ : e ≪ x, e'

theorem stepFun_of_wayBelow {e : D} {e' : D'} {x : D} (h : e ≪ x) : stepFun e e' x = e' :=
  iSup_pos h

theorem stepFun_of_not_wayBelow {e : D} {e' : D'} {x : D} (h : ¬ e ≪ x) :
    stepFun e e' x = ⊥ :=
  iSup_neg h

/-- Step functions are Scott-continuous: `{x | e ≪ x}` is Scott-open, so the conditional commutes
with directed suprema. -/
theorem stepFun_preservesDirectedSup (e : D) (e' : D') :
    PreservesDirectedSup (stepFun e e') := by
  intro S hS hSdir
  show stepFun e e' (sSup S) = sSup (Set.image (stepFun e e') S)
  by_cases h : e ≪ sSup S
  · rw [stepFun_of_wayBelow h]
    obtain ⟨s, hsS, hes⟩ := (scottOpen_wayBelow e).2 hS hSdir h
    apply le_antisymm
    · refine le_sSup_of_le (Set.mem_image_of_mem _ hsS) ?_
      rw [stepFun_of_wayBelow hes]
    · refine sSup_le ?_
      rintro _ ⟨x, _, rfl⟩
      exact iSup_le fun _ => le_rfl
  · rw [stepFun_of_not_wayBelow h]
    refine (sSup_eq_bot.2 ?_).symm
    rintro _ ⟨x, hxS, rfl⟩
    refine stepFun_of_not_wayBelow (fun hex => ?_)
    exact h (hex.trans_le (le_sSup hxS))

/-- The step function `ē[e, e']` as a Scott map. -/
noncomputable def stepMap (e : D) (e' : D') : ScottMap D D' :=
  ⟨stepFun e e', continuous_of_preservesDirectedSup (stepFun_preservesDirectedSup e e')⟩

theorem stepMap_apply_of_wayBelow {e : D} {e' : D'} {x : D} (h : e ≪ x) :
    (stepMap e e' : D → D') x = e' :=
  stepFun_of_wayBelow h

/-- If `e' ≪ g e` then the step function `ē[e, e']` lies below `g` (a pointwise argument). -/
theorem stepMap_le_of_wayBelow {e : D} {e' : D'} {g : ScottMap D D'}
    (h : e' ≪ (g : D → D') e) : stepMap e e' ≤ g := by
  rw [ScottMap.le_def]
  intro x
  by_cases hex : e ≪ x
  · rw [stepMap_apply_of_wayBelow hex]
    exact h.le.trans (g.monotone hex.le)
  · show stepFun e e' x ≤ (g : D → D') x
    rw [stepFun_of_not_wayBelow hex]
    exact bot_le

/-- **The step function is way below `f`.** If `e' ≪ f e`, then `ē[e, e'] ≪ f` in `[D → D']`,
witnessed by the Scott-open set `{g | e' ≪ g e}` (open because suprema in `[D → D']` are pointwise
and `{· ≪ ·}` is inaccessible by directed suprema). -/
theorem stepMap_wayBelow {e : D} {e' : D'} {f : ScottMap D D'}
    (he' : e' ≪ (f : D → D') e) : stepMap e e' ≪ f := by
  refine ⟨{g : ScottMap D D' | e' ≪ (g : D → D') e}, ⟨?_, ?_⟩, he', ?_⟩
  · intro g g' hgg' hg
    exact hg.trans_le (hgg' e)
  · intro F hFne hFdir hmem
    simp only [Set.mem_setOf_eq, ScottMap.sSup_apply] at hmem
    have hne : (Set.image (fun g : ScottMap D D' => (g : D → D') e) F).Nonempty := hFne.image _
    have hdir : DirectedOn (· ≤ ·) (Set.image (fun g : ScottMap D D' => (g : D → D') e) F) := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      obtain ⟨c, hc, hac, hbc⟩ := hFdir a ha b hb
      exact ⟨(c : D → D') e, Set.mem_image_of_mem _ hc, hac e, hbc e⟩
    obtain ⟨_, ⟨g, hgF, rfl⟩, hg⟩ := (wayBelow_sSup_iff hne hdir).1 hmem
    exact ⟨g, hgF, hg⟩
  · intro g hg
    exact Set.mem_Ici.2 (stepMap_le_of_wayBelow hg)

/-- **Pointwise reconstruction.** For a Scott map `f`, the supremum of the values of the step
functions below `f` recovers `f x`: `f x = ⊔ {e' | ∃ e ≪ x, e' ≪ f e}`. Uses continuity of `D`
(`x = ⊔{e | e ≪ x}`), Scott-continuity of `f`, and continuity of `D'`. -/
theorem stepMap_pointwise_sSup (hD : IsContinuousLattice D) (hD' : IsContinuousLattice D')
    (f : ScottMap D D') (x : D) :
    sSup {e' : D' | ∃ e, e ≪ x ∧ e' ≪ (f : D → D') e} = (f : D → D') x := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro e' ⟨e, hex, he'⟩
    exact he'.le.trans (f.monotone hex.le)
  · rw [← hD'.sSup_wayBelow ((f : D → D') x)]
    refine sSup_le ?_
    intro w hw
    have hfx : (f : D → D') x = sSup (Set.image (f : D → D') {e | e ≪ x}) := by
      rw [← f.preservesDirectedSup_coe {e | e ≪ x} ⟨⊥, bot_wayBelow x⟩ (directedOn_wayBelow x),
        hD.sSup_wayBelow x]
    rw [hfx] at hw
    have hne : (Set.image (f : D → D') {e | e ≪ x}).Nonempty := ⟨f ⊥, ⊥, bot_wayBelow x, rfl⟩
    have hdir : DirectedOn (· ≤ ·) (Set.image (f : D → D') {e | e ≪ x}) := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      obtain ⟨c, hc, hac, hbc⟩ := directedOn_wayBelow x a ha b hb
      exact ⟨f c, Set.mem_image_of_mem _ hc, f.monotone hac, f.monotone hbc⟩
    obtain ⟨_, ⟨e, hex, rfl⟩, hwe⟩ := (wayBelow_sSup_iff hne hdir).1 hw
    exact le_sSup ⟨e, hex, hwe⟩

/-- **Scott 1972, Theorem 3.3 (order content).** If `D` and `D'` are continuous lattices, then so
is `[D → D']` under the pointwise order. Every `f` is the supremum of the step functions way below
it: `f = ⊔ {ē[e,e'] | e' ≪ f e}`, and each such step function is way below `f`. -/
theorem theorem_3_3_isContinuousLattice (hD : IsContinuousLattice D)
    (hD' : IsContinuousLattice D') : IsContinuousLattice (ScottMap D D') := by
  intro f
  refine ⟨fun h hh => hh.le, fun g hg => ?_⟩
  rw [ScottMap.le_def]
  intro x
  rw [← stepMap_pointwise_sSup hD hD' f x]
  refine sSup_le ?_
  rintro e' ⟨e, hex, he'⟩
  have hle : stepMap e e' ≤ g := hg (stepMap_wayBelow he')
  have hx := (ScottMap.le_def.1 hle) x
  rwa [stepMap_apply_of_wayBelow hex] at hx

/-! ### Theorem 3.3(b): the lattice topology = the topology of pointwise convergence

The Scott topology of the continuous lattice `[D → D']` coincides with the product (pointwise
convergence) topology, whose subbasis is `{f | f x ∈ U}` (`U` Scott-open in `D'`). One inclusion
(pointwise ⊆ Scott) is immediate: each subbasic set is Scott-open in the lattice (joins are
pointwise). The other (Scott ⊆ pointwise) is Scott's argument via the `↟φ` basis of a continuous
lattice: `φ ≪ g` forces `φ ≤ ⊔ᵢ ē[eᵢ,eᵢ']` for finitely many pairs with `eᵢ' ≪ g eᵢ`, and the
finite intersection `⋂ᵢ {h | eᵢ' ≪ h eᵢ}` is a pointwise-open neighbourhood of `g` inside `↟φ`. -/

/-- A finite sup of elements way below `g` is way below `g`. -/
theorem wayBelow_finset_sup {ι L : Type*} [CompleteLattice L] {s : Finset ι} {f : ι → L} {g : L}
    (h : ∀ i ∈ s, f i ≪ g) : s.sup f ≪ g :=
  Finset.sup_induction (p := fun a => a ≪ g) (bot_wayBelow g) (fun _ ha _ hb => ha.sup hb) h

/-- Subbasic sets of the pointwise (product) topology on `[D → D']`: `{f | f x ∈ U}` for `U`
Scott-open in `D'`. -/
def scottMapPointwiseSubbasis (D D' : Type*) [CompleteLattice D] [CompleteLattice D'] :
    Set (Set (ScottMap D D')) :=
  { W | ∃ (x : D) (U : Set D'),
      @IsOpen D' scottTopologicalSpace U ∧ W = {f : ScottMap D D' | (f : D → D') x ∈ U} }

/-- **Scott 1972, Definition 3.1 (on lattices).** The topology of pointwise convergence on
`[D → D']`. -/
@[reducible] noncomputable def scottMapPointwiseTopology (D D' : Type*)
    [CompleteLattice D] [CompleteLattice D'] : TopologicalSpace (ScottMap D D') :=
  generateFrom (scottMapPointwiseSubbasis D D')

/-- The literal Pi topology on all functions `D → D'`, restricted along the underlying-function
map of `ScottMap`.  No topology instance is installed, so it can be compared safely with the Scott
lattice topology and with `scottMapPointwiseTopology`. -/
@[reducible] noncomputable def scottMapInducedPiTopology (D : Type u) (D' : Type v)
    [CompleteLattice D] [CompleteLattice D'] : TopologicalSpace (ScottMap D D') :=
  TopologicalSpace.induced (fun f : ScottMap D D' => (f : D → D'))
    (@Pi.topologicalSpace D (fun _ => D') (fun _ => scottTopologicalSpace))

theorem pointwiseSubbasic_isOpen (x : D) {U : Set D'} (hU : @IsOpen D' scottTopologicalSpace U) :
    @IsOpen (ScottMap D D') (scottMapPointwiseTopology D D')
      {f : ScottMap D D' | (f : D → D') x ∈ U} :=
  isOpen_generateFrom_of_mem ⟨x, U, hU, rfl⟩

/-- Scott's manually generated pointwise topology on `ScottMap` is the subspace topology inherited
from the literal Pi product of the codomain Scott topology. -/
theorem scottMapPointwiseTopology_eq_induced_pi :
    scottMapPointwiseTopology D D' = scottMapInducedPiTopology D D' := by
  apply le_antisymm
  · letI : TopologicalSpace D' := scottTopologicalSpace
    letI : TopologicalSpace (ScottMap D D') := scottMapPointwiseTopology D D'
    change scottMapPointwiseTopology D D' ≤ scottMapInducedPiTopology D D'
    rw [← continuous_iff_le_induced]
    exact continuous_pi fun x =>
      continuous_def.2 fun U hU => pointwiseSubbasic_isOpen (D := D) (D' := D') x hU
  · apply le_generateFrom_iff_subset_isOpen.2
    rintro W ⟨x, U, hU, rfl⟩
    letI : TopologicalSpace D' := scottTopologicalSpace
    change @IsOpen (ScottMap D D')
      (TopologicalSpace.induced (fun f : ScottMap D D' => (f : D → D'))
        (@Pi.topologicalSpace D (fun _ => D') (fun _ => scottTopologicalSpace)))
      {f : ScottMap D D' | (f : D → D') x ∈ U}
    rw [isOpen_induced_iff]
    exact ⟨{g : D → D' | g x ∈ U}, (@continuous_apply D (fun _ => D')
      (fun _ => scottTopologicalSpace) x).isOpen_preimage U hU, rfl⟩

/-- Each pointwise-subbasic set `{f | f x ∈ U}` (`U` Scott-open) is Scott-open in the lattice
`[D → D']`, because suprema there are pointwise. This is the easy inclusion pointwise ⊆ Scott. -/
theorem pointwiseSubbasic_scottOpen (x : D) {U : Set D'} (hU : ScottOpen U) :
    ScottOpen {f : ScottMap D D' | (f : D → D') x ∈ U} := by
  refine ⟨fun f f' hff' hf => hU.1 (hff' x) hf, fun F hFne hFdir hmem => ?_⟩
  simp only [Set.mem_setOf_eq, ScottMap.sSup_apply] at hmem
  have hne : (Set.image (fun g : ScottMap D D' => (g : D → D') x) F).Nonempty := hFne.image _
  have hdir : DirectedOn (· ≤ ·) (Set.image (fun g : ScottMap D D' => (g : D → D') x) F) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hFdir a ha b hb
    exact ⟨(c : D → D') x, Set.mem_image_of_mem _ hc, hac x, hbc x⟩
  obtain ⟨_, ⟨g, hgF, rfl⟩, hg⟩ := hU.2 hne hdir hmem
  exact ⟨g, hgF, hg⟩

/-- **Step-function decomposition of `≪`.** If `φ ≪ g` in `[D → D']`, then `φ` lies below a finite
join of step functions `ē[eᵢ,eᵢ']` with `eᵢ' ≪ g eᵢ`. The finite joins of such step functions form
a directed family with supremum `g`, so `wayBelow_sSup_iff` produces one above `φ`. -/
theorem wayBelow_le_finset_sup_step (hD : IsContinuousLattice D) (hD' : IsContinuousLattice D')
    {φ g : ScottMap D D'} (h : φ ≪ g) :
    ∃ F : Finset (D × D'), (∀ p ∈ F, (p.2 : D') ≪ (g : D → D') p.1) ∧
      φ ≤ F.sup (fun p => stepMap p.1 p.2) := by
  classical
  set Sg : Set (ScottMap D D') :=
    (fun F : Finset (D × D') => F.sup (fun p => stepMap p.1 p.2)) ''
      {F | ∀ p ∈ F, (p.2 : D') ≪ (g : D → D') p.1} with hSg
  have hSgne : Sg.Nonempty := by
    refine ⟨_, ∅, ?_, rfl⟩
    intro p hp
    exact absurd hp (Finset.notMem_empty p)
  have hSgdir : DirectedOn (· ≤ ·) Sg := by
    rintro _ ⟨F₁, hF₁, rfl⟩ _ ⟨F₂, hF₂, rfl⟩
    refine ⟨(F₁ ∪ F₂).sup (fun p => stepMap p.1 p.2), ⟨F₁ ∪ F₂, fun p hp => ?_, rfl⟩,
      Finset.sup_mono Finset.subset_union_left, Finset.sup_mono Finset.subset_union_right⟩
    rcases Finset.mem_union.1 hp with hp | hp
    · exact hF₁ p hp
    · exact hF₂ p hp
  have hSgsup : sSup Sg = g := by
    apply le_antisymm
    · refine sSup_le ?_
      rintro _ ⟨F, hF, rfl⟩
      exact Finset.sup_le fun p hp => stepMap_le_of_wayBelow (hF p hp)
    · rw [ScottMap.le_def]
      intro x
      rw [← stepMap_pointwise_sSup hD hD' g x]
      refine sSup_le ?_
      rintro e' ⟨e, hex, he'⟩
      have hmemSg : stepMap e e' ∈ Sg := by
        refine ⟨{(e, e')}, fun p hp => ?_, ?_⟩
        · rw [Finset.mem_singleton] at hp; subst hp; exact he'
        · show ({(e, e')} : Finset (D × D')).sup (fun p => stepMap p.1 p.2) = stepMap e e'
          rw [Finset.sup_singleton]
      have hx : (stepMap e e' : D → D') x ≤ ((sSup Sg : ScottMap D D') : D → D') x := by
        rw [ScottMap.sSup_apply]
        exact le_sSup ⟨stepMap e e', hmemSg, rfl⟩
      rwa [stepMap_apply_of_wayBelow hex] at hx
  rw [← hSgsup] at h
  obtain ⟨_, ⟨F, hF, rfl⟩, hφs⟩ := (wayBelow_sSup_iff hSgne hSgdir).1 h
  exact ⟨F, hF, hφs.le⟩

/-- **Scott 1972, Theorem 3.3(b).** The Scott (lattice) topology on `[D → D']` agrees with the
topology of pointwise convergence. -/
theorem theorem_3_3_topology (hD : IsContinuousLattice D) (hD' : IsContinuousLattice D') :
    (scottTopologicalSpace : TopologicalSpace (ScottMap D D')) = scottMapPointwiseTopology D D' := by
  have hL : IsContinuousLattice (ScottMap D D') := theorem_3_3_isContinuousLattice hD hD'
  apply le_antisymm
  · -- pointwise ⊆ Scott: each subbasic set is Scott-open in the lattice
    apply le_generateFrom_iff_subset_isOpen.2
    rintro W ⟨x, U, hUopen, rfl⟩
    exact isOpen_iff_scottOpen.mpr (pointwiseSubbasic_scottOpen x (isOpen_iff_scottOpen.mp hUopen))
  · -- Scott ⊆ pointwise: each Scott-open lattice set is pointwise-open, via the `↟φ` basis
    intro U hU
    rw [isOpen_iff_scottOpen] at hU
    rw [@isOpen_iff_forall_mem_open (ScottMap D D') (scottMapPointwiseTopology D D')]
    intro g hgU
    obtain ⟨φ, hφg, hφsub⟩ := exists_wayBelow_subset hL hU hgU
    obtain ⟨F, hF, hφF⟩ := wayBelow_le_finset_sup_step hD hD' hφg
    refine ⟨⋂ p ∈ F, {h : ScottMap D D' | (p.2 : D') ≪ (h : D → D') p.1}, ?_, ?_, ?_⟩
    · intro h hh
      refine hφsub (WayBelow.le_trans hφF (wayBelow_finset_sup fun p hp => ?_))
      exact stepMap_wayBelow (Set.mem_iInter₂.1 hh p hp)
    · exact @isOpen_biInter_finset (ScottMap D D') (D × D') (scottMapPointwiseTopology D D') F _
        (fun p _ => pointwiseSubbasic_isOpen p.1 (isOpen_iff_scottOpen.mpr (scottOpen_wayBelow p.2)))
    · exact Set.mem_iInter₂.2 fun p hp => hF p hp

/-- The literal product/subspace form of Theorem 3.3: the Scott lattice topology on `[D → D']`
is induced from Mathlib's Pi topology on the underlying functions. -/
theorem theorem_3_3_topology_induced_pi (hD : IsContinuousLattice D)
    (hD' : IsContinuousLattice D') :
    (scottTopologicalSpace : TopologicalSpace (ScottMap D D')) =
      scottMapInducedPiTopology D D' := by
  rw [theorem_3_3_topology hD hD', scottMapPointwiseTopology_eq_induced_pi]

/-- **Scott 1972, Theorem 3.3 (full statement).** For continuous lattices `D`, `D'`, the function
space `[D → D']` is a continuous lattice (`theorem_3_3_isContinuousLattice`) whose Scott topology
agrees with the topology of pointwise convergence (`theorem_3_3_topology`). -/
theorem theorem_3_3 (hD : IsContinuousLattice D) (hD' : IsContinuousLattice D') :
    IsContinuousLattice (ScottMap D D') ∧
      (scottTopologicalSpace : TopologicalSpace (ScottMap D D')) = scottMapPointwiseTopology D D' :=
  ⟨theorem_3_3_isContinuousLattice hD hD', theorem_3_3_topology hD hD'⟩

/-! ### Corollary 3.4 -/

theorem scottFunctionSubbasis_isOpen_scott {x : D} {U : Set D'} (hU : @IsOpen D' scottTopologicalSpace U) :
    @IsOpen (ScottC D D') (@scottFunctionTopology D D' scottTopologicalSpace scottTopologicalSpace)
      {f : ScottC D D' | f x ∈ U} :=
  isOpen_generateFrom_of_mem (s := {f : ScottC D D' | f x ∈ U}) ⟨x, U, hU, rfl⟩

theorem corollary_3_4_eval_on_C (x : D) :
    @Continuous (ScottC D D') D'
      (@scottFunctionTopology D D' scottTopologicalSpace scottTopologicalSpace)
      scottTopologicalSpace (fun f : ScottC D D' => f x) :=
  continuous_def.2 fun _U hU => scottFunctionSubbasis_isOpen_scott (D := D) (D' := D') (x := x) hU

/-- **Scott 1972, Corollary 3.4 (fixed `x`).** Evaluation at fixed `x` is continuous on `[D → D']`
(with Scott topologies on `D` and `D'`); this is one half of the separate-continuity input to
joint continuity. -/
theorem corollary_3_4 (x : D) :
    @Continuous (ScottC D D') D'
      (@scottFunctionTopology D D' scottTopologicalSpace scottTopologicalSpace)
      scottTopologicalSpace (fun f : ScottC D D' => f x) :=
  corollary_3_4_eval_on_C (D := D) (D' := D') x

/-- **Scott 1972, Corollary 3.4 (joint continuity, core).** Evaluation `[D → D'] × D → D'`,
`(f, x) ↦ f x`, preserves directed suprema. By Proposition 2.6 it suffices to check separate
Scott-continuity: in `x` (with `f` fixed) it is `f`'s own continuity, and in `f` (with `x` fixed)
it is the pointwise formula for suprema in `[D → D']` (`ScottMap.sSup_apply`). -/
theorem corollary_3_4_preservesDirectedSup :
    PreservesDirectedSup (fun p : ScottMap D D' × D => (p.1 : D → D') p.2) := by
  rw [proposition_2_6]
  constructor
  · intro y S hS hSdir
    show ((sSup S : ScottMap D D') : D → D') y
        = sSup ((fun x : ScottMap D D' => (x : D → D') y) '' S)
    rw [ScottMap.sSup_apply]
  · intro x
    exact (proposition_2_5 _).mp x.continuous

/-- **Scott 1972, Corollary 3.4.** The evaluation map `eval : [D → D'] × D → D'`, `(f, x) ↦ f x`,
is (jointly) Scott-continuous. Via Theorem 3.3(b) and Proposition 2.9(b) the Scott topology of the
product lattice is the product of the pointwise topology on `[D → D']` and the Scott topology on
`D`, so this is exactly joint continuity for Scott's product topology. -/
theorem corollary_3_4_jointly_continuous :
    @Continuous (ScottMap D D' × D) D' scottTopologicalSpace scottTopologicalSpace
      (fun p : ScottMap D D' × D => (p.1 : D → D') p.2) :=
  continuous_of_preservesDirectedSup corollary_3_4_preservesDirectedSup

/-! ### Proposition 3.5 (currying) -/

theorem sSup_image_prod_mk_left (x : D) (S : Set D') (hS : S.Nonempty) :
    sSup (Set.image (fun y => (x, y)) S) = (x, sSup S) := by
  have himage : Set.image (fun y => (x, y)) S = ({x} : Set D) ×ˢ S := by
    ext ⟨a, b⟩
    simp only [Set.mem_image, Set.mem_prod, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, h⟩
      obtain ⟨ha, hb⟩ := Prod.ext_iff.mp h
      subst hb
      exact ⟨ha.symm, hy⟩
    · rintro ⟨ha, hb⟩
      refine ⟨b, hb, Prod.ext_iff.mpr ⟨ha.symm, rfl⟩⟩
  have hx : sSup ({x} : Set D) = x := by
    apply le_antisymm
    · exact sSup_le fun z hz => by rw [Set.mem_singleton_iff] at hz; rw [hz]
    · exact le_sSup (Set.mem_singleton x)
  rw [himage, sSup_prod (hs := ⟨x, Set.mem_singleton x⟩) (ht := hS), hx]

theorem curry_right_preservesDirectedSup (f : ScottMap (D × D') D'') (x : D) :
    PreservesDirectedSup (fun y => f (x, y)) := by
  intro S hS hSdir
  have hS' : DirectedOn (· ≤ ·) (Set.image (fun y => (x, y)) S) := by
    intro p hp q hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    obtain ⟨c, hc, hac, hbc⟩ := hSdir a ha b hb
    exact ⟨(x, c), Set.mem_image_of_mem _ hc, And.intro (And.intro le_rfl hac) (And.intro le_rfl hbc)⟩
  have hS'ne : (Set.image (fun y => (x, y)) S).Nonempty := by
    obtain ⟨s, hs⟩ := hS
    exact ⟨(x, s), s, hs, rfl⟩
  rw [show (fun y => f (x, y)) (sSup S) = f (x, sSup S) from rfl,
    ← sSup_image_prod_mk_left x S hS,
    f.preservesDirectedSup_coe (Set.image (fun y => (x, y)) S) hS'ne hS']
  congr 1
  simp [Set.image_image]

/-- **Scott 1972, Proposition 3.5 (right).** Currying in the `y`-variable is Scott-continuous. -/
noncomputable def scottLambdaAt (f : ScottMap (D × D') D'') (x : D) : ScottMap D' D'' :=
  ⟨fun y => f (x, y), continuous_of_preservesDirectedSup (curry_right_preservesDirectedSup f x)⟩

theorem sSup_image_prod_mk_right (y : D') (S : Set D) (hS : S.Nonempty) :
    sSup (Set.image (fun x => (x, y)) S) = (sSup S, y) := by
  have himage : Set.image (fun x => (x, y)) S = S ×ˢ ({y} : Set D') := by
    ext ⟨a, b⟩
    simp only [Set.mem_image, Set.mem_prod, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, h⟩
      obtain ⟨ha, hb⟩ := Prod.ext_iff.mp h
      subst ha
      exact ⟨hx, hb.symm⟩
    · rintro ⟨ha, hb⟩
      exact ⟨a, ha, Prod.ext_iff.mpr ⟨rfl, hb.symm⟩⟩
  have hy : sSup ({y} : Set D') = y := by
    apply le_antisymm
    · exact sSup_le fun z hz => by rw [Set.mem_singleton_iff] at hz; rw [hz]
    · exact le_sSup (Set.mem_singleton y)
  rw [himage, sSup_prod (hs := hS) (ht := ⟨y, Set.mem_singleton y⟩), hy]

/-- Currying in the `x`-variable: `x ↦ f (x, y)` is Scott-continuous (used for continuity of
`lambda f` as a map `D → [D' → D'']`). -/
theorem curry_left_preservesDirectedSup (f : ScottMap (D × D') D'') (y : D') :
    PreservesDirectedSup (fun x => f (x, y)) := by
  intro S hS hSdir
  have hS' : DirectedOn (· ≤ ·) (Set.image (fun x => (x, y)) S) := by
    intro p hp q hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    obtain ⟨c, hc, hac, hbc⟩ := hSdir a ha b hb
    exact ⟨(c, y), Set.mem_image_of_mem _ hc, And.intro (And.intro hac le_rfl) (And.intro hbc le_rfl)⟩
  have hS'ne : (Set.image (fun x => (x, y)) S).Nonempty := by
    obtain ⟨s, hs⟩ := hS
    exact ⟨(s, y), s, hs, rfl⟩
  rw [show (fun x => f (x, y)) (sSup S) = f (sSup S, y) from rfl,
    ← sSup_image_prod_mk_right y S hS,
    f.preservesDirectedSup_coe (Set.image (fun x => (x, y)) S) hS'ne hS']
  congr 1
  simp [Set.image_image]

/-- The outer half of currying: `x ↦ (y ↦ f (x, y))` preserves directed suprema (so `lambda f` is a
Scott map `D → [D' → D'']`). Equality in `[D' → D'']` is pointwise, reducing to `curry_left`. -/
theorem lambda_outer_preservesDirectedSup (f : ScottMap (D × D') D'') :
    PreservesDirectedSup (fun x => scottLambdaAt f x) := by
  intro S hS hSdir
  apply ScottMap.ext
  intro y
  show f (sSup S, y)
      = ((sSup (Set.image (fun x => scottLambdaAt f x) S) : ScottMap D' D'') : D' → D'') y
  rw [ScottMap.sSup_apply, Set.image_image]
  exact curry_left_preservesDirectedSup f y hS hSdir

/-- **Scott 1972, Proposition 3.5.** Functional abstraction
`lambda : [[D × D'] → D''] → [D → [D' → D'']]`, `lambda f x y = f (x, y)`. By Theorem 3.3,
`[D → [D' → D'']]` is itself a continuous lattice, and `lambda f` is a Scott map. -/
noncomputable def scottLambda (f : ScottMap (D × D') D'') : ScottMap D (ScottMap D' D'') :=
  ⟨fun x => scottLambdaAt f x,
    continuous_of_preservesDirectedSup (lambda_outer_preservesDirectedSup f)⟩

@[simp] theorem scottLambda_apply (f : ScottMap (D × D') D'') (x : D) (y : D') :
    ((scottLambda f x : ScottMap D' D'') : D' → D'') y = (f : (D × D') → D'') (x, y) :=
  rfl

/-- `lambda` preserves directed suprema: both sides evaluate, pointwise at `(x, y)`, to
`⊔ {f (x, y) | f ∈ 𝓕}`, since suprema in every function lattice involved are pointwise. -/
theorem proposition_3_5_preservesDirectedSup :
    PreservesDirectedSup
      (scottLambda : ScottMap (D × D') D'' → ScottMap D (ScottMap D' D'')) := by
  intro 𝓕 h𝓕 h𝓕dir
  apply ScottMap.ext
  intro x
  apply ScottMap.ext
  intro y
  rw [scottLambda_apply, ScottMap.sSup_apply, ScottMap.sSup_apply, ScottMap.sSup_apply,
    Set.image_image, Set.image_image]
  congr 1

/-- **Scott 1972, Proposition 3.5.** Functional abstraction `lambda` is Scott-continuous. -/
theorem proposition_3_5 :
    @Continuous (ScottMap (D × D') D'') (ScottMap D (ScottMap D' D''))
      scottTopologicalSpace scottTopologicalSpace scottLambda :=
  continuous_of_preservesDirectedSup proposition_3_5_preservesDirectedSup

/-! ### Definition 3.6 -/

/-- **Scott 1972, Definition 3.6.** A *retraction* of continuous lattices. -/
structure IsContinuousLatticeRetraction (D : Type u) (D' : Type v)
    [CompleteLattice D] [CompleteLattice D'] where
  incl : ScottMap D D'
  retr : ScottMap D' D
  retr_incl : ∀ d, retr (incl d) = d

/-- **Scott 1972, Definition 3.6.** A *projection* of continuous lattices: a retract with
`i ∘ j ⊑ id`. -/
structure IsContinuousLatticeProjection (D : Type u) (D' : Type v)
    [CompleteLattice D] [CompleteLattice D']
    extends IsContinuousLatticeRetraction D D' where
  incl_retr_le : ∀ d,
    @LE.le D'
      (ChainCompletePartialOrder.instOfCompleteLattice (α := D')).toPartialOrder.toPreorder.toLE
      (incl (retr d)) d

namespace IsContinuousLatticeRetraction

/-- **Scott 1972, Prop 2.10 / March 1972 correction (p. 135).** For `S ⊆ D` a subspace of
ambient `D'`, write `⊔S′` for the supremum of `S` computed in `D'` (Scott's prime is on the
index, not the join). This is `sSup (i '' S)` in Lean. -/
noncomputable def ambientSSup (R : IsContinuousLatticeRetraction D D') (S : Set D) : D' :=
  sSup (Set.image (R.incl : D → D') S)

/-- **Scott 1972, Prop 2.10 / March 1972 correction (p. 135).** For directed `S ⊆ D`,
`j(⊔S′) = ⊔S`: the retraction sends the ambient join back to the subspace join. -/
theorem retr_ambientSSup_eq_sSup (R : IsContinuousLatticeRetraction D D') (S : Set D)
    (hS : S.Nonempty) (hdir : DirectedOn (· ≤ ·) S) :
    R.retr (ambientSSup R S) = sSup S := by
  unfold ambientSSup
  have hdir' : DirectedOn (· ≤ ·) (Set.image (R.incl : D → D') S) := by
    intro p hp q hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    obtain ⟨c, hc, hac, hbc⟩ := hdir a ha b hb
    exact ⟨R.incl c, Set.mem_image_of_mem _ hc, R.incl.monotone hac, R.incl.monotone hbc⟩
  have hne' : (Set.image (R.incl : D → D') S).Nonempty := Set.image_nonempty.2 hS
  rw [R.retr.preservesDirectedSup_coe (Set.image (R.incl : D → D') S) hne' hdir']
  rw [Set.image_image, Set.image_congr fun a _ => R.retr_incl a]
  simp [Set.image_id]

/-- The inclusion of a retraction preserves directed suprema (it is a Scott map). -/
theorem incl_preservesDirectedSup (R : IsContinuousLatticeRetraction D D') :
    PreservesDirectedSup (R.incl : D → D') :=
  fun _ hS hSdir => R.incl.preservesDirectedSup_coe _ hS hSdir

/-- **Heart of Scott's proof of 2.10.** If `x' ≪ i(d)` in the ambient continuous lattice `D'`,
then its image `j(x')` is way below `d` in the retract `D`. The Scott-open witness in `D` is the
preimage `i⁻¹V'` of an ambient Scott-open witness `V'` (Scott-open because `i` preserves directed
suprema); for `z ∈ i⁻¹V'` we have `x' ⊑ i(z)`, hence `j(x') ⊑ j(i(z)) = z`. No projection
hypothesis is needed — `j ∘ i = id` and monotonicity suffice. -/
theorem retr_wayBelow_of_wayBelow_incl (R : IsContinuousLatticeRetraction D D')
    {d : D} {x' : D'} (hx' : x' ≪ R.incl d) : R.retr x' ≪ d := by
  obtain ⟨U', hU'open, hd_in, hU'sub⟩ := hx'
  refine ⟨(R.incl : D → D') ⁻¹' U', scottOpen_preimage R.incl_preservesDirectedSup hU'open,
    hd_in, fun z hz => ?_⟩
  have hle : x' ≤ R.incl z := Set.mem_Ici.1 (hU'sub hz)
  have hjle := R.retr.monotone hle
  rw [R.retr_incl z] at hjle
  exact Set.mem_Ici.2 hjle

/-- For `d` in the retract, the ambient way-below set of `i(d)` pushed back by `j` is a directed
family whose supremum (computed in `D`) is `d`. This is the identity `j(⊔S′) = ⊔S` applied to
`S = {j(x') : x' ≪ i(d)}`, combined with continuity of `D'`. -/
theorem sSup_image_retr_wayBelow (R : IsContinuousLatticeRetraction D D')
    (hD' : IsContinuousLattice D') (d : D) :
    sSup (Set.image (R.retr : D' → D) {x' | x' ≪ R.incl d}) = d := by
  have hne : ({x' : D' | x' ≪ R.incl d}).Nonempty := ⟨⊥, bot_wayBelow _⟩
  have hdir : DirectedOn (· ≤ ·) {x' : D' | x' ≪ R.incl d} := directedOn_wayBelow _
  rw [← R.retr.preservesDirectedSup_coe _ hne hdir, hD'.sSup_wayBelow (R.incl d), R.retr_incl d]

theorem image_retr_wayBelow_nonempty (R : IsContinuousLatticeRetraction D D') (d : D) :
    (Set.image (R.retr : D' → D) {x' | x' ≪ R.incl d}).Nonempty :=
  ⟨R.retr ⊥, ⊥, bot_wayBelow _, rfl⟩

theorem image_retr_wayBelow_directed (R : IsContinuousLatticeRetraction D D') (d : D) :
    DirectedOn (· ≤ ·) (Set.image (R.retr : D' → D) {x' | x' ≪ R.incl d}) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact ⟨R.retr (a ⊔ b), ⟨a ⊔ b, WayBelow.sup ha hb, rfl⟩,
    R.retr.monotone le_sup_left, R.retr.monotone le_sup_right⟩

end IsContinuousLatticeRetraction

/-! ### Proposition 2.10: a retract of a continuous lattice is a continuous lattice -/

/-- **Scott 1972, Proposition 2.10(a).** A (Scott-continuous) retract of a continuous lattice is a
continuous lattice. For `d ∈ D` we have, in the ambient `D'`, `i(d) = ⊔{x' | x' ≪ i(d)}`; applying
the retraction `j` (which preserves this directed supremum) gives `d = ⊔{j(x') | x' ≪ i(d)}` in
`D`, and each `j(x') ≪ d` by `retr_wayBelow_of_wayBelow_incl`. Hence any upper bound of
`{x | x ≪ d}` dominates `d`, so `d = ⊔{x | x ≪ d}`. -/
theorem proposition_2_10_a (R : IsContinuousLatticeRetraction D D')
    (hD' : IsContinuousLattice D') : IsContinuousLattice D := by
  intro d
  refine ⟨fun x hx => hx.le, fun b hb => ?_⟩
  rw [← R.sSup_image_retr_wayBelow hD' d]
  exact sSup_le fun _ ⟨x', hx', hxeq⟩ => hxeq ▸ hb (R.retr_wayBelow_of_wayBelow_incl hx')

/-- **Scott 1972, Proposition 2.10(b) (March 1972 / Milner correction).** The Scott topology of the
retract `D` coincides with the subspace topology induced from the ambient `D'` along `i`.

* `scott ≤ induced`: each induced-open `i⁻¹V'` is Scott-open in `D` because `i` is a Scott map.
* `induced ≤ scott`: the sets `i⁻¹(↟x') = {z | x' ≪ i(z)}` (`x' ∈ D'`) are a basis of `D`'s Scott
  topology — given a Scott-open `U ∋ d`, the directed family `{j(x') | x' ≪ i(d)}` (sup `d`) meets
  `U` at some `j(x')`, and `i⁻¹(↟x') ⊆ U` since `x' ≪ i(z) ⟹ j(x') ⊑ z` with `U` upper. Each such
  basic set is induced-open by construction, so every Scott-open of `D` is induced-open. -/
theorem proposition_2_10_b (R : IsContinuousLatticeRetraction D D')
    (hD' : IsContinuousLattice D') :
    (scottTopologicalSpace : TopologicalSpace D) =
      TopologicalSpace.induced (R.incl : D → D') scottTopologicalSpace := by
  apply le_antisymm
  · intro U hU
    rw [isOpen_induced_iff (t := scottTopologicalSpace)] at hU
    obtain ⟨V', hV'open, rfl⟩ := hU
    rw [isOpen_iff_scottOpen] at hV'open ⊢
    exact scottOpen_preimage R.incl_preservesDirectedSup hV'open
  · intro U hU
    rw [isOpen_iff_scottOpen] at hU
    rw [@isOpen_iff_forall_mem_open _
      (TopologicalSpace.induced (R.incl : D → D') scottTopologicalSpace)]
    intro d hd
    have hmem : sSup (Set.image (R.retr : D' → D) {x' | x' ≪ R.incl d}) ∈ U := by
      rw [R.sSup_image_retr_wayBelow hD' d]; exact hd
    obtain ⟨p, hp, hpU⟩ :=
      hU.2 (R.image_retr_wayBelow_nonempty d) (R.image_retr_wayBelow_directed d) hmem
    obtain ⟨x', hx', rfl⟩ := hp
    refine ⟨(R.incl : D → D') ⁻¹' {z' | x' ≪ z'}, fun z hz => ?_, ?_, hx'⟩
    · have hjle := R.retr.monotone (show x' ≤ R.incl z from (hz : x' ≪ R.incl z).le)
      rw [R.retr_incl z] at hjle
      exact hU.1 hjle hpU
    · rw [isOpen_induced_iff (t := scottTopologicalSpace)]
      exact ⟨{z' | x' ≪ z'}, isOpen_iff_scottOpen.mpr (scottOpen_wayBelow x'), rfl⟩

/-- **Scott 1972, Proposition 2.10 (full statement).** A retract of a continuous lattice is a
continuous lattice (`proposition_2_10_a`) whose Scott topology agrees with the subspace topology
(`proposition_2_10_b`). -/
theorem proposition_2_10 (R : IsContinuousLatticeRetraction D D')
    (hD' : IsContinuousLattice D') :
    IsContinuousLattice D ∧
      (scottTopologicalSpace : TopologicalSpace D) =
        TopologicalSpace.induced (R.incl : D → D') scottTopologicalSpace :=
  ⟨proposition_2_10_a R hD', proposition_2_10_b R hD'⟩

/-! ### Proposition 3.7 -/

/-- **Scott 1972, Proposition 3.7 (retraction half).** If `D_n` is a retract of `D'_n`
(`n = 0,1`), then `[D₀ → D₁]` is a retract of `[D'₀ → D'₁]` via
`f ↦ i₁ ∘ f ∘ j₀` and `f' ↦ j₁ ∘ f' ∘ i₀`. -/
structure ScottMapRetraction (D₀ D₀' D₁ D₁' : Type*)
    [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁'] where
  incl : ScottMap D₀ D₁ → ScottMap D₀' D₁'
  retr : ScottMap D₀' D₁' → ScottMap D₀ D₁
  retr_incl : ∀ f, retr (incl f) = f

/-- **Scott 1972, Proposition 3.7 (projection half).** Under the same hypotheses with
projections, the induced pair on function spaces is also a projection. -/
structure ScottMapProjection (D₀ D₀' D₁ D₁' : Type*)
    [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁'] extends
    ScottMapRetraction D₀ D₀' D₁ D₁' where
  incl_retr_le : ∀ f' x, (incl (retr f')) x ≤ f' x

namespace ScottMapRetraction

def functionSpace (R₀ : IsContinuousLatticeRetraction D₀ D₀') (R₁ : IsContinuousLatticeRetraction D₁ D₁') :
    ScottMapRetraction D₀ D₀' D₁ D₁' where
  incl f := ScottMap.comp R₁.incl (ScottMap.comp f R₀.retr)
  retr f' := ScottMap.comp R₁.retr (ScottMap.comp f' R₀.incl)
  retr_incl f := ScottMap.ext fun x => by simp [ScottMap.comp, R₀.retr_incl, R₁.retr_incl]

end ScottMapRetraction

namespace ScottMapProjection

def functionSpace (P₀ : IsContinuousLatticeProjection D₀ D₀') (P₁ : IsContinuousLatticeProjection D₁ D₁') :
    ScottMapProjection D₀ D₀' D₁ D₁' where
  toScottMapRetraction :=
    ScottMapRetraction.functionSpace P₀.toIsContinuousLatticeRetraction P₁.toIsContinuousLatticeRetraction
  incl_retr_le f' y := by
    dsimp only [ScottMapRetraction.functionSpace, ScottMap.comp, Function.comp_def]
    exact le_trans (P₁.incl_retr_le (f' (P₀.incl (P₀.retr y))))
      (ScottMap.monotone f' (P₀.incl_retr_le y))

end ScottMapProjection

/-- **Scott 1972, Proposition 3.7 (retraction).** Function spaces inherit retractions. -/
def proposition_3_7_retraction (R₀ : IsContinuousLatticeRetraction D₀ D₀')
    (R₁ : IsContinuousLatticeRetraction D₁ D₁') :
    ScottMapRetraction D₀ D₀' D₁ D₁' :=
  ScottMapRetraction.functionSpace R₀ R₁

/-- **Scott 1972, Proposition 3.7 (projection).** Function spaces inherit projections. -/
def proposition_3_7_projection (P₀ : IsContinuousLatticeProjection D₀ D₀')
    (P₁ : IsContinuousLatticeProjection D₁ D₁') :
    ScottMapProjection D₀ D₀' D₁ D₁' :=
  ScottMapProjection.functionSpace P₀ P₁

/-! ### Proposition 3.10 -/

section Proposition310

open Finset

namespace IsContinuousLatticeProjection

/-- **Scott 1972, Proposition 3.10(ii).** The inclusion map of a projection is injective. -/
theorem incl_injective (P : IsContinuousLatticeProjection D D') {x y : D} (h : P.incl x = P.incl y) : x = y := by
  rw [← P.retr_incl x, ← P.retr_incl y, h]

theorem retr_bot (P : IsContinuousLatticeProjection D D') : (P.retr : D' → D) ⊥ = ⊥ := by
  have hle : (⊥ : D') ≤ P.incl (⊥ : D) := bot_le
  have heq : (P.retr : D' → D) (P.incl (⊥ : D)) = (⊥ : D) := P.retr_incl (d := (⊥ : D))
  exact le_antisymm (le_trans (P.retr.monotone hle) (le_of_eq heq)) bot_le

/-- **Scott 1972, Proposition 3.10(i), empty case.** `i(⊥) = ⊥`. -/
theorem incl_bot (P : IsContinuousLatticeProjection D D') : P.incl (⊥ : D) = ⊥ :=
  le_antisymm (by simpa [retr_bot P] using P.incl_retr_le (⊥ : D')) bot_le

/-- **Scott 1972, Proposition 3.10(i), binary case.** `i(x ⊔ y) = i(x) ⊔ i(y)`. -/
theorem incl_sup (P : IsContinuousLatticeProjection D D') (x y : D) :
    P.incl (x ⊔ y) = P.incl x ⊔ P.incl y := by
  apply le_antisymm
  · have hx : x ≤ P.retr (P.incl x ⊔ P.incl y) :=
      le_trans (le_of_eq (P.retr_incl x).symm) (P.retr.monotone le_sup_left)
    have hy : y ≤ P.retr (P.incl x ⊔ P.incl y) :=
      le_trans (le_of_eq (P.retr_incl y).symm) (P.retr.monotone le_sup_right)
    exact le_trans (P.incl.monotone (sup_le hx hy)) (P.incl_retr_le (P.incl x ⊔ P.incl y))
  · exact sup_le (P.incl.monotone le_sup_left) (P.incl.monotone le_sup_right)

theorem incl_finset_sup (P : IsContinuousLatticeProjection D D') (T : Finset D) :
    P.incl (T.sup (fun x => x)) = T.sup (fun x => P.incl x) := by
  classical
  refine Finset.induction_on T ?base ?step
  · simp only [sup_empty]
    exact incl_bot P
  · intro a s _ ih
    simp only [sup_insert]
    rw [incl_sup P, ih]

/-- Finite sub-lubs used in Scott's proof of Proposition 3.10(i). -/
def finsetSupOf (S : Set D) : Set D :=
  { z | ∃ T : Finset D, (∀ x ∈ T, x ∈ S) ∧ z = T.sup id }

theorem mem_finsetSupOf_of_mem {S : Set D} {x : D} (hx : x ∈ S) :
    x ∈ finsetSupOf S :=
  ⟨{x}, by simp [hx], by simp⟩

theorem le_sSup_finsetSupOf (S : Set D) : sSup S ≤ sSup (finsetSupOf S) :=
  sSup_le fun _ hx => le_sSup (mem_finsetSupOf_of_mem hx)

theorem sSup_le_finsetSupOf (S : Set D) : sSup (finsetSupOf S) ≤ sSup S :=
  sSup_le fun z hz => by
    obtain ⟨T, hTS, rfl⟩ := hz
    exact Finset.sup_le fun t ht => le_sSup (hTS t ht)

theorem sSup_finsetSupOf (S : Set D) : sSup S = sSup (finsetSupOf S) :=
  le_antisymm (le_sSup_finsetSupOf S) (sSup_le_finsetSupOf S)

theorem directedOn_finsetSupOf (S : Set D) :
    DirectedOn (· ≤ ·) (finsetSupOf S) := by
  classical
  intro a ha b hb
  obtain ⟨T₁, hT₁, rfl⟩ := ha
  obtain ⟨T₂, hT₂, rfl⟩ := hb
  have hunion : (T₁ ∪ T₂).sup id = T₁.sup id ⊔ T₂.sup id := by
    simpa using Finset.sup_union (s₁ := T₁) (s₂ := T₂) (f := id)
  refine ⟨T₁.sup id ⊔ T₂.sup id, ⟨T₁ ∪ T₂, ?_, hunion.symm⟩, le_sup_left, le_sup_right⟩
  intro x hx
  simp only [Finset.mem_union] at hx
  exact hx.elim (hT₁ x) (hT₂ x)

theorem directedOn_wayBelow (a : D) : DirectedOn (· ≤ ·) { z | z ≪ a } := by
  intro p hp q hq
  exact ⟨p ⊔ q, WayBelow.sup hp hq, le_sup_left, le_sup_right⟩

/-- **Scott 1972, Proposition 3.10(i).** Projections preserve arbitrary suprema. -/
theorem incl_sSup (P : IsContinuousLatticeProjection D D') (S : Set D) :
    P.incl (sSup S) = sSup (Set.image (P.incl : D → D') S) := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS
    simp only [sSup_empty, Set.image_empty, incl_bot P]
  · rw [sSup_finsetSupOf S]
    have hdir := directedOn_finsetSupOf S
    have hne : (finsetSupOf S).Nonempty := by
      obtain ⟨x, hx⟩ := hS
      exact ⟨x, mem_finsetSupOf_of_mem hx⟩
    rw [P.incl.preservesDirectedSup_coe (finsetSupOf S) hne hdir]
    apply le_antisymm
    · apply sSup_le
      intro b hb
      obtain ⟨z, hz, rfl⟩ := hb
      obtain ⟨T, hT, rfl⟩ := hz
      have h := incl_finset_sup P T
      conv_lhs => rw [show T.sup id = T.sup (fun x => x) from rfl]
      rw [h]
      apply Finset.sup_le
      intro t ht
      exact le_sSup (Set.mem_image_of_mem (P.incl : D → D') (hT t ht))
    · apply sSup_le
      intro b hb
      obtain ⟨x, hxS, rfl⟩ := (Set.mem_image (P.incl : D → D') S b).1 hb
      exact le_sSup (Set.mem_image_of_mem (P.incl : D → D') (mem_finsetSupOf_of_mem hxS))

/-- **Scott 1972, Proposition 3.10(iii).** Projections preserve the way-below relation. -/
theorem incl_wayBelow (P : IsContinuousLatticeProjection D D') (hD' : IsContinuousLattice D')
    {x y : D} (h : x ≪ y) : @WayBelow D' _ (P.incl x) (P.incl y) := by
  set W : Set D' := { z' | @WayBelow D' _ z' (P.incl y) }
  have hWne : W.Nonempty := ⟨(⊥ : D'), @bot_wayBelow D' _ (P.incl y)⟩
  have hWdir : DirectedOn (· ≤ ·) W := by
    intro p hp q hq
    exact ⟨p ⊔ q, @WayBelow.sup D' _ p q (P.incl y) hp hq, le_sup_left, le_sup_right⟩
  have hy : y = sSup (Set.image (P.retr : D' → D) W) := by
    rw [← P.retr.preservesDirectedSup_coe W hWne hWdir, @IsContinuousLattice.sSup_wayBelow D' _ hD' (P.incl y),
      P.retr_incl y]
  have hImgne : (Set.image (P.retr : D' → D) W).Nonempty := by
    obtain ⟨z', hz'⟩ := hWne
    exact ⟨P.retr z', z', hz', rfl⟩
  have hImgdir : DirectedOn (· ≤ ·) (Set.image (P.retr : D' → D) W) := by
    intro p hp q hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    refine ⟨P.retr (a ⊔ b), ⟨a ⊔ b, @WayBelow.sup D' _ a b (P.incl y) ha hb, rfl⟩, ?_, ?_⟩
    · exact P.retr.monotone le_sup_left
    · exact P.retr.monotone le_sup_right
  have hx : x ≪ sSup (Set.image (P.retr : D' → D) W) := by rwa [← hy]
  obtain ⟨prz, hprz, hxpr⟩ := (wayBelow_sSup_iff hImgne hImgdir).1 hx
  obtain ⟨z', hz', rfl⟩ := hprz
  exact @WayBelow.le_trans D' _ (P.incl x) z' (P.incl y)
    (le_trans (P.incl.monotone hxpr.le) (P.incl_retr_le z')) hz'

/-- **Scott 1972, Proposition 3.10(i)–(iii), bundled.** The inclusion `i` of a projection preserves
arbitrary suprema, is injective, and preserves the way-below relation. -/
theorem proposition_3_10_forward (P : IsContinuousLatticeProjection D D')
    (hD' : IsContinuousLattice D') :
    (∀ S : Set D, (P.incl : D → D') (sSup S) = sSup (Set.image (P.incl : D → D') S))
      ∧ Function.Injective (P.incl : D → D')
      ∧ (∀ x y : D, x ≪ y → (P.incl : D → D') x ≪ (P.incl : D → D') y) :=
  ⟨fun S => P.incl_sSup S, fun _ _ h => P.incl_injective h,
    fun _ _ h => P.incl_wayBelow hD' h⟩

/-- **Scott 1972, Proposition 3.10(iv), uniqueness.** The retraction of any projection is forced to
be Scott's formula `j(x') = ⊔ { x | i(x) ⊑ x' }`. `≤`: `j(x')` itself satisfies `i(j x') ⊑ x'`
(by `i ∘ j ⊑ id`), so it is a member of the set; `≥`: each member `x` (with `i x ⊑ x'`) satisfies
`x = j(i x) ⊑ j(x')` by `j ∘ i = id` and monotonicity. -/
theorem retr_eq_sSup (P : IsContinuousLatticeProjection D D') (x' : D') :
    (P.retr : D' → D) x' = sSup {x | (P.incl : D → D') x ≤ x'} := by
  apply le_antisymm
  · exact le_sSup (show (P.incl : D → D') (P.retr x') ≤ x' from P.incl_retr_le x')
  · refine sSup_le fun x hx => ?_
    calc x = (P.retr : D' → D) (P.incl x) := (P.retr_incl x).symm
      _ ≤ (P.retr : D' → D) x' := P.retr.monotone hx

end IsContinuousLatticeProjection

/-! #### Proposition 3.10, converse direction

Given a map `i : D → D'` satisfying (i)–(iii), Scott's formula (iv)
`j(x') = ⊔ { x | i(x) ⊑ x' }` is the unique continuous retraction making `D` a projection of `D'`. -/

variable {i : D → D'}

/-- **Scott 1972, Proposition 3.10(iv).** Scott's candidate retraction `j(x') = ⊔ { x | i(x) ⊑ x' }`. -/
noncomputable def converseRetr (i : D → D') (x' : D') : D :=
  sSup {x | i x ≤ x'}

theorem converseRetr_mono (i : D → D') : Monotone (converseRetr i) := by
  intro a b hab
  exact sSup_le_sSup fun _ hx => le_trans hx hab

/-- From (i): `i` preserves binary joins (Scott checks (i) on two-element sets). -/
theorem incl_sup_of_preservesSSup (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S)) (x y : D) :
    i (x ⊔ y) = i x ⊔ i y := by
  calc i (x ⊔ y) = i (sSup {x, y}) := by rw [sSup_pair]
    _ = sSup (i '' {x, y}) := hi _
    _ = sSup {i x, i y} := by rw [Set.image_pair]
    _ = i x ⊔ i y := sSup_pair

/-- From (i): `i` is monotone. -/
theorem incl_mono_of_preservesSSup (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S)) :
    Monotone i := by
  intro x y hxy
  have h := incl_sup_of_preservesSSup hi x y
  rw [sup_eq_right.mpr hxy] at h
  rw [h]; exact le_sup_left

/-- From (i)+(ii): `i` is order-reflecting (`x ⊑ y ↔ i x ⊑ i y`), since `x ⊑ y ↔ x ⊔ y = y`. -/
theorem le_of_incl_le (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S))
    (hinj : Function.Injective i) {x y : D} (h : i x ≤ i y) : x ≤ y := by
  have h1 : i (x ⊔ y) = i y := by rw [incl_sup_of_preservesSSup hi, sup_eq_right.mpr h]
  exact sup_eq_right.mp (hinj h1)

/-- `i ∘ j ⊑ id` (uses only (i)). -/
theorem incl_converseRetr_le (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S)) (x' : D') :
    i (converseRetr i x') ≤ x' := by
  show i (sSup {x | i x ≤ x'}) ≤ x'
  rw [hi]
  exact sSup_le (by rintro _ ⟨x, hx, rfl⟩; exact hx)

/-- `j ∘ i = id` (uses (i)+(ii)): `{x | i x ⊑ i y} = Iic y`, whose join is `y`. -/
theorem converseRetr_incl (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S))
    (hinj : Function.Injective i) (y : D) : converseRetr i (i y) = y := by
  have hset : {x | i x ≤ i y} = Set.Iic y := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Iic]
    exact ⟨le_of_incl_le hi hinj, fun hx => incl_mono_of_preservesSSup hi hx⟩
  show sSup {x | i x ≤ i y} = y
  rw [hset]
  exact le_antisymm (sSup_le fun _ hx => hx) (le_sSup le_rfl)

/-- `j` is Scott-continuous (uses (i)+(iii) and continuity of `D`). For directed `S'`: monotonicity
gives `⊔ j''S' ⊑ j(⊔S')`; conversely if `i x ⊑ ⊔S'` then for every `z ≪ x` we have `i z ≪ i x ⊑ ⊔S'`,
so `i z ⊑ x'` for some `x' ∈ S'` (directedness), whence `z ⊑ j(x') ⊑ ⊔ j''S'`; continuity of `D`
then gives `x ⊑ ⊔ j''S'`. -/
theorem converseRetr_preservesDirectedSup
    (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S))
    (hwb : ∀ {x y : D}, x ≪ y → i x ≪ i y) (hD : IsContinuousLattice D) :
    PreservesDirectedSup (converseRetr i) := by
  intro S' hS'ne hS'dir
  apply le_antisymm
  · show sSup {x | i x ≤ sSup S'} ≤ sSup (converseRetr i '' S')
    apply sSup_le
    intro x hx
    have hx' : i x ≤ sSup S' := hx
    rw [← hD.sSup_wayBelow x]
    apply sSup_le
    intro z hz
    have hiz : i z ≪ sSup S' := (hwb hz).trans_le hx'
    obtain ⟨x', hx'S', hzx'⟩ := (wayBelow_sSup_iff hS'ne hS'dir).1 hiz
    have hz_mem : z ∈ {x | i x ≤ x'} := hzx'.le
    exact le_trans (le_sSup hz_mem) (le_sSup ⟨x', hx'S', rfl⟩)
  · apply sSup_le
    rintro _ ⟨x', hx'S', rfl⟩
    exact converseRetr_mono i (le_sSup hx'S')

/-- The projection assembled from a map `i` satisfying 3.10(i)–(iii). -/
noncomputable def converseProjection
    (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S)) (hinj : Function.Injective i)
    (hwb : ∀ {x y : D}, x ≪ y → i x ≪ i y) (hD : IsContinuousLattice D) :
    IsContinuousLatticeProjection D D' where
  incl := ⟨i, continuous_of_preservesDirectedSup (fun _ _ _ => hi _)⟩
  retr := ⟨converseRetr i, continuous_of_preservesDirectedSup
    (converseRetr_preservesDirectedSup hi hwb hD)⟩
  retr_incl := fun d => converseRetr_incl hi hinj d
  incl_retr_le := fun x' => incl_converseRetr_le hi x'

/-- **Scott 1972, Proposition 3.10 (converse).** If `i : D → D'` (between continuous lattices)
satisfies (i) preservation of arbitrary suprema, (ii) injectivity, and (iii) preservation of `≪`,
then there is a continuous `j` making `D` a projection of `D'` via `i`, with `j` given by Scott's
formula (iv) `j(x') = ⊔ { x | i(x) ⊑ x' }`. -/
theorem proposition_3_10_converse
    (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S)) (hinj : Function.Injective i)
    (hwb : ∀ {x y : D}, x ≪ y → i x ≪ i y) (hD : IsContinuousLattice D) :
    ∃ P : IsContinuousLatticeProjection D D',
      (∀ d, (P.incl : D → D') d = i d)
        ∧ (∀ x', (P.retr : D' → D) x' = sSup {x | i x ≤ x'}) :=
  ⟨converseProjection hi hinj hwb hD, fun _ => rfl, fun _ => rfl⟩

end Proposition310

/-! ### Proposition 3.8 -/

section SubspaceExtension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompleteLattice Y]

/-- **Scott 1972, Proposition 3.8.** The infimum term `⊓ { f(x) : e(x) ∈ U }` for open `U ⊆ Y`. -/
noncomputable def scottSubspaceExtendInf (e : X → Y) (f : X → D) (U : Set Y) : D :=
  sInf (f '' (e ⁻¹' U))

/-- **Scott 1972, Proposition 3.8.** Scott's maximal subspace extension `f̄ : Y → D`. -/
noncomputable def scottSubspaceExtend (e : X → Y) (f : X → D) (y : Y) : D :=
  sSup { d | ∃ U, @IsOpen Y scottTopologicalSpace U ∧ y ∈ U ∧ d = scottSubspaceExtendInf e f U }

omit [TopologicalSpace Y] in
theorem scottSubspaceExtendInf_le_of_mem {f' : ScottMap Y D} {U : Set Y} {y : Y}
    (hyU : y ∈ U) : sInf (Set.image (f' : Y → D) U) ≤ f' y :=
  sInf_le (Set.mem_image_of_mem _ hyU)

theorem sInf_image_le_sInf_image_of_subset {α : Type*} {f : α → D} {S T : Set α}
    (hST : S ⊆ T) : sInf (Set.image f T) ≤ sInf (Set.image f S) :=
  sInf_le_sInf fun _ hd => by
    obtain ⟨s, hs, rfl⟩ := hd
    exact ⟨s, hST hs, rfl⟩

theorem scottMap_eq_sSup_openInfs (hD : IsContinuousLattice D) (f' : ScottMap Y D) (y : Y) :
    (f' : Y → D) y =
      sSup { d | ∃ U, @IsOpen Y scottTopologicalSpace U ∧ y ∈ U ∧
        d = sInf (Set.image (f' : Y → D) U) } := by
  apply le_antisymm
  · rw [← IsContinuousLattice.sSup_wayBelow hD (f' y)]
    apply sSup_le
    intro a ha
    obtain ⟨V, hV, hf'V, hVsub⟩ := ha
    have hVopen : @IsOpen D scottTopologicalSpace V := isOpen_iff_scottOpen.mpr hV
    have hyU : y ∈ (f' : Y → D) ⁻¹' V := hf'V
    have hUScott : ScottOpen ((f' : Y → D) ⁻¹' V) :=
      scottOpen_preimage ((proposition_2_5 (Subtype.val f')).mp f'.property) hV
    have hUopen : @IsOpen Y scottTopologicalSpace ((f' : Y → D) ⁻¹' V) :=
      isOpen_iff_scottOpen.mpr hUScott
    have ha' : a ≤ sInf (Set.image (f' : Y → D) ((f' : Y → D) ⁻¹' V)) := by
      apply le_sInf
      intro d hd
      obtain ⟨z, hzV, rfl⟩ := hd
      exact Set.mem_Ici.1 (hVsub hzV)
    have hmem : sInf (Set.image (f' : Y → D) ((f' : Y → D) ⁻¹' V)) ∈
        { d | ∃ U, @IsOpen Y scottTopologicalSpace U ∧ y ∈ U ∧
          d = sInf (Set.image (f' : Y → D) U) } :=
      ⟨(f' : Y → D) ⁻¹' V, hUopen, hyU, rfl⟩
    exact le_trans ha' (le_sSup hmem)
  · apply sSup_le
    intro d hd
    obtain ⟨U, _hUopen, hyU, rfl⟩ := hd
    exact scottSubspaceExtendInf_le_of_mem (f' := f') hyU

theorem scottSubspaceExtendInf_eq_of_comp {e : X → Y} {f : X → D} {U : Set Y}
    (f' : ScottMap Y D) (h : ∀ x, f' (e x) = f x) :
    scottSubspaceExtendInf e f U = sInf (Set.image (f' : Y → D) (Set.image e Set.univ ∩ U)) := by
  have hset : f '' (e ⁻¹' U) = Set.image (f' : Y → D) (Set.image e Set.univ ∩ U) := by
    ext d
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, Set.mem_univ, true_and]
    constructor
    · rintro ⟨x, hxU, heq⟩
      refine ⟨e x, ⟨?_, hxU⟩, ?_⟩
      · exact ⟨x, rfl⟩
      · rw [h x, heq]
    · rintro ⟨y, ⟨hex, hyU⟩, heq⟩
      obtain ⟨x, _, rfl⟩ := hex
      exact ⟨x, hyU, (h x).symm.trans heq⟩
  rw [scottSubspaceExtendInf, hset]

/-- **Scott 1972, Proposition 3.8 (subspace variant).** `f̄` (with the Scott topology on `Y`) is
the maximal extension along a subspace embedding. The faithful statement (arbitrary topology on
`Y`) is `proposition_3_8` in `Constructions.lean`. -/
theorem scottSubspaceExtend_maximal (hD : IsContinuousLattice D) (e : X → Y) (_he : IsEmbedding e)
    (f : X → D) (f' : ScottMap Y D) (h_ext : ∀ x, f' (e x) = f x) (y : Y) :
    (f' : Y → D) y ≤ scottSubspaceExtend e f y := by
  have hEq := scottMap_eq_sSup_openInfs hD f' y
  have hmain :
      sSup { d | ∃ U, @IsOpen Y scottTopologicalSpace U ∧ y ∈ U ∧
        d = sInf (Set.image (f' : Y → D) U) } ≤ scottSubspaceExtend e f y := by
    unfold scottSubspaceExtend
    apply sSup_le
    intro d hd
    obtain ⟨U, hUopen, hyU, rfl⟩ := hd
    have hmem : scottSubspaceExtendInf e f U ∈
        { d | ∃ U, @IsOpen Y scottTopologicalSpace U ∧ y ∈ U ∧ d = scottSubspaceExtendInf e f U } :=
      ⟨U, hUopen, hyU, rfl⟩
    refine le_trans ?_ (le_sSup hmem)
    have hrestrict :
        sInf (Set.image (f' : Y → D) U) ≤
          sInf (Set.image (f' : Y → D) (Set.image e Set.univ ∩ U)) :=
      sInf_image_le_sInf_image_of_subset
        (show Set.image e Set.univ ∩ U ⊆ U from inter_subset_right)
    refine le_trans hrestrict (le_of_eq (scottSubspaceExtendInf_eq_of_comp (f' := f') h_ext).symm)
  exact le_trans (le_of_eq hEq) hmain

omit [TopologicalSpace X] [TopologicalSpace Y] [CompleteLattice Y] in
theorem scottSubspaceExtendInf_mono {e : X → Y} {f g₀ : X → D} (hfg : ∀ x, f x ≤ g₀ x) (U : Set Y) :
    scottSubspaceExtendInf e f U ≤ scottSubspaceExtendInf e g₀ U := by
  apply le_sInf
  intro d hd
  obtain ⟨x, hxU, rfl⟩ := hd
  exact le_trans (sInf_le ⟨x, hxU, rfl⟩) (hfg x)

theorem scottSubspaceExtend_mono {e : X → Y} {f g₀ : X → D} (hfg : ∀ x, f x ≤ g₀ x) (y : Y) :
    scottSubspaceExtend e f y ≤ scottSubspaceExtend e g₀ y := by
  apply sSup_le
  intro d hd
  obtain ⟨U, hUopen, hyU, rfl⟩ := hd
  have hmem : scottSubspaceExtendInf e g₀ U ∈
      { d | ∃ U, @IsOpen Y scottTopologicalSpace U ∧ y ∈ U ∧ d = scottSubspaceExtendInf e g₀ U } :=
    ⟨U, hUopen, hyU, rfl⟩
  exact le_trans (scottSubspaceExtendInf_mono hfg U) (le_sSup hmem)

theorem scottSubspaceExtendInf_eq_of_ext {e : X → Y} {f g' : X → D} (h : ∀ x, f x = g' x) (U : Set Y) :
    scottSubspaceExtendInf e f U = scottSubspaceExtendInf e g' U := by
  unfold scottSubspaceExtendInf
  congr 1
  ext d
  simp [Set.mem_image, Set.mem_preimage, h]

theorem scottSubspaceExtend_eq_of_ext {e : X → Y} {f g' : X → D} (h : ∀ x, f x = g' x) (y : Y) :
    scottSubspaceExtend e f y = scottSubspaceExtend e g' y := by
  unfold scottSubspaceExtend
  congr 1
  ext d
  simp [Set.mem_setOf_eq, scottSubspaceExtendInf_eq_of_ext h]

theorem scottSubspaceExtendInf_mono_retr {e : X → Y} {g : X → D'}
    (P : IsContinuousLatticeProjection D D') (U : Set Y) :
    P.retr (scottSubspaceExtendInf e g U) ≤ scottSubspaceExtendInf e (fun x => P.retr (g x)) U := by
  apply le_sInf
  intro d hd
  obtain ⟨x, hxU, rfl⟩ := hd
  have hx : x ∈ e ⁻¹' U := Set.mem_preimage.mpr hxU
  exact (P.retr.monotone (sInf_le (Set.mem_image_of_mem g hx))).trans le_rfl

theorem scottSubspaceExtendInf_mono_incl {e : X → Y} {f : X → D} {g : X → D'}
    (P : IsContinuousLatticeProjection D D') (hfg : ∀ x, f x = P.retr (g x)) (U : Set Y) :
    scottSubspaceExtendInf e (fun x => P.incl (f x)) U ≤ scottSubspaceExtendInf e g U := by
  apply le_sInf
  intro d hd
  obtain ⟨x, hxU, rfl⟩ := hd
  have hx : x ∈ e ⁻¹' U := Set.mem_preimage.mpr hxU
  have hmem : P.incl (f x) ∈ (fun x => P.incl (f x)) '' (e ⁻¹' U) :=
    Set.mem_image_of_mem _ hx
  have hincl : P.incl (f x) ≤ g x := by rw [hfg x]; exact P.incl_retr_le (g x)
  exact le_trans (sInf_le hmem) hincl

theorem scottSubspaceExtendInf_mono_incl_apply {e : X → Y} {f : X → D} (U : Set Y)
    (P : IsContinuousLatticeProjection D D') :
    P.incl (scottSubspaceExtendInf e f U) ≤ scottSubspaceExtendInf e (fun x => P.incl (f x)) U := by
  apply le_sInf
  intro d hd
  obtain ⟨x, hxU, rfl⟩ := hd
  exact P.incl.monotone (sInf_le (Set.mem_image_of_mem f (Set.mem_preimage.mpr hxU)))

/-- **Scott 1972, Lemma 3.9 (inclusion at infimum level).** Used in the inverse-limit
argument (Theorem 4.4). -/
theorem lemma_3_9_incl_inf {e : X → Y} (P : IsContinuousLatticeProjection D D')
    {f : X → D} {g : X → D'} (hfg : ∀ x, f x = P.retr (g x)) (U : Set Y) :
    P.incl (scottSubspaceExtendInf e f U) ≤ scottSubspaceExtendInf e g U :=
  le_trans (scottSubspaceExtendInf_mono_incl_apply (e := e) (f := f) U P)
    (scottSubspaceExtendInf_mono_incl (e := e) (f := f) (g := g) P hfg U)

/-- **Scott 1972, Lemma 3.9 (retraction at infimum level).** The global equality
`f̄ = j ∘ ḡ` assembles these infimum bounds via Proposition 3.10(i). -/
theorem lemma_3_9_retr_inf {e : X → Y} (P : IsContinuousLatticeProjection D D') {g : X → D'}
    (U : Set Y) :
    P.retr (scottSubspaceExtendInf e g U) ≤ scottSubspaceExtendInf e (fun x => P.retr (g x)) U :=
  scottSubspaceExtendInf_mono_retr (e := e) (g := g) P U

end SubspaceExtension

/-! ### Definition 3.11 / Proposition 3.12: the lattice of projections `J_D` -/

section Projections

/-- **Scott 1972, Definition 3.11.** `J_D = { j ∈ [D → D] : j = j ∘ j ⊑ id }`: the Scott-continuous
projections of `D` (idempotent self-maps below the identity), as a predicate on `[D → D]`. -/
def IsProjection (j : ScottMap D D) : Prop :=
  j.comp j = j ∧ j ≤ ScottMap.idMap

/-- Pointwise characterization of projections: idempotent and deflationary. -/
theorem isProjection_iff {j : ScottMap D D} :
    IsProjection j ↔ (∀ x, (j : D → D) (j x) = j x) ∧ (∀ x, (j : D → D) x ≤ x) := by
  constructor
  · rintro ⟨hidem, hle⟩
    refine ⟨fun x => ?_, fun x => ?_⟩
    · have h : ((j.comp j : ScottMap D D) : D → D) x = (j : D → D) x := by rw [hidem]
      rwa [ScottMap.comp_apply] at h
    · have h := (ScottMap.le_def.mp hle) x
      rwa [ScottMap.idMap_apply] at h
  · rintro ⟨hidem, hle⟩
    exact ⟨ScottMap.ext fun x => by rw [ScottMap.comp_apply]; exact hidem x,
      ScottMap.le_def.mpr fun x => by rw [ScottMap.idMap_apply]; exact hle x⟩

/-- `⊥` (the constant `⊥` map) is a projection — Scott's `⊔∅ ∈ J_D`. -/
theorem isProjection_bot : IsProjection (⊥ : ScottMap D D) := by
  rw [isProjection_iff]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · simp only [ScottMap.bot_apply]
  · rw [ScottMap.bot_apply]; exact bot_le

/-- `J_D` is closed under binary joins (Scott 1972, 3.12). The key step: since `j x ⊔ k x ⊑ x`,
monotonicity and idempotency force `j (j x ⊔ k x) = j x` and `k (j x ⊔ k x) = k x`. -/
theorem isProjection_sup {j k : ScottMap D D} (hj : IsProjection j) (hk : IsProjection k) :
    IsProjection (j ⊔ k) := by
  rw [isProjection_iff] at hj hk ⊢
  obtain ⟨hjidem, hjle⟩ := hj
  obtain ⟨hkidem, hkle⟩ := hk
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have hjkle : (j : D → D) x ⊔ k x ≤ x := sup_le (hjle x) (hkle x)
    have hj_eq : (j : D → D) (j x ⊔ k x) = j x :=
      le_antisymm (j.monotone hjkle) (le_of_eq_of_le (hjidem x).symm (j.monotone le_sup_left))
    have hk_eq : (k : D → D) (j x ⊔ k x) = k x :=
      le_antisymm (k.monotone hjkle) (le_of_eq_of_le (hkidem x).symm (k.monotone le_sup_right))
    rw [ScottMap.sup_apply, ScottMap.sup_apply, hj_eq, hk_eq]
  · rw [ScottMap.sup_apply]; exact sup_le (hjle x) (hkle x)

/-- `J_D` is closed under finite joins. -/
theorem isProjection_finsetSup {T : Finset (ScottMap D D)} (hT : ∀ j ∈ T, IsProjection j) :
    IsProjection (T.sup id) :=
  Finset.sup_induction isProjection_bot (fun _ ha _ hb => isProjection_sup ha hb) hT

/-- `J_D` is closed under *directed* joins (Scott 1972, 3.12). Continuity of each member lets the
inner `(⊔S)`-application distribute over the directed family `{ j x : j ∈ S }`, and directedness
plus idempotency collapse the double family `{ k (j x) }` to `(⊔S) x`. -/
theorem isProjection_directedSup {S : Set (ScottMap D D)} (hSne : S.Nonempty)
    (hSdir : DirectedOn (· ≤ ·) S) (hS : ∀ j ∈ S, IsProjection j) :
    IsProjection (sSup S) := by
  have hidem : ∀ j ∈ S, ∀ x, (j : D → D) (j x) = j x :=
    fun j hj => (isProjection_iff.mp (hS j hj)).1
  have hle : ∀ j ∈ S, ∀ x, (j : D → D) x ≤ x := fun j hj => (isProjection_iff.mp (hS j hj)).2
  rw [isProjection_iff]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · set A := Set.image (fun j : ScottMap D D => (j : D → D) x) S with hA
    have hAne : A.Nonempty := hSne.image _
    have hAdir : DirectedOn (· ≤ ·) A := by
      rintro _ ⟨j, hj, rfl⟩ _ ⟨k, hk, rfl⟩
      obtain ⟨m, hm, hjm, hkm⟩ := hSdir j hj k hk
      exact ⟨(m : D → D) x, Set.mem_image_of_mem _ hm, hjm x, hkm x⟩
    have hsSx : ((sSup S : ScottMap D D) : D → D) x = sSup A := ScottMap.sSup_apply S x
    apply le_antisymm
    · rw [hsSx, ScottMap.sSup_apply]
      refine sSup_le ?_
      rintro _ ⟨k, hk, rfl⟩
      show (k : D → D) (sSup A) ≤ sSup A
      rw [k.preservesDirectedSup_coe A hAne hAdir]
      refine sSup_le ?_
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      obtain ⟨m, hm, hjm, hkm⟩ := hSdir j hj k hk
      calc (k : D → D) (j x) ≤ (m : D → D) (j x) := hkm (j x)
        _ ≤ (m : D → D) (m x) := m.monotone (hjm x)
        _ = (m : D → D) x := hidem m hm x
        _ ≤ sSup A := le_sSup (Set.mem_image_of_mem _ hm)
    · rw [hsSx, ScottMap.sSup_apply]
      refine sSup_le ?_
      rintro _ ⟨j, hj, rfl⟩
      have hjxA : (j : D → D) x ≤ sSup A := le_sSup (Set.mem_image_of_mem _ hj)
      calc (j : D → D) x = (j : D → D) (j x) := (hidem j hj x).symm
        _ ≤ (j : D → D) (sSup A) := j.monotone hjxA
        _ ≤ sSup (Set.image (fun f : ScottMap D D => (f : D → D) (sSup A)) S) :=
              le_sSup (Set.mem_image_of_mem _ hj)
  · rw [ScottMap.sSup_apply]
    refine sSup_le ?_
    rintro _ ⟨j, hj, rfl⟩
    exact hle j hj x

/-- **Scott 1972, Proposition 3.12 (`⊔`-closure).** `J_D` is closed under arbitrary suprema in
`[D → D]`: every supremum is the directed supremum of finite sub-joins (`finsetSupOf`), each a
projection by `isProjection_finsetSup`. -/
theorem isProjection_sSup {T : Set (ScottMap D D)} (hT : ∀ j ∈ T, IsProjection j) :
    IsProjection (sSup T) := by
  rw [IsContinuousLatticeProjection.sSup_finsetSupOf T]
  refine isProjection_directedSup ⟨⊥, ∅, by simp, by simp⟩
    (IsContinuousLatticeProjection.directedOn_finsetSupOf T) ?_
  rintro z ⟨F, hF, rfl⟩
  exact isProjection_finsetSup fun j hj => hT j (hF j hj)

/-- **Scott 1972, Definition 3.11.** The space `J_D` of projections of `D`, as a subtype of
`[D → D]`. -/
abbrev Projections (D : Type*) [CompleteLattice D] : Type _ := {j : ScottMap D D // IsProjection j}

namespace Projections

noncomputable instance instSupSet : SupSet (Projections D) :=
  ⟨fun T => ⟨sSup (Set.image Subtype.val T), isProjection_sSup (by rintro j ⟨p, _, rfl⟩; exact p.2)⟩⟩

theorem isLUB_sSup (T : Set (Projections D)) : IsLUB T (sSup T) := by
  constructor
  · intro p hp
    apply Subtype.coe_le_coe.mp
    show (p : ScottMap D D) ≤ ((sSup T : Projections D) : ScottMap D D)
    exact le_sSup (Set.mem_image_of_mem _ hp)
  · intro q hq
    apply Subtype.coe_le_coe.mp
    show ((sSup T : Projections D) : ScottMap D D) ≤ (q : ScottMap D D)
    refine sSup_le ?_
    rintro _ ⟨p, hp, rfl⟩
    exact Subtype.coe_le_coe.mpr (hq hp)

/-- **Scott 1972, Proposition 3.12.** `J_D` is a complete lattice (a `⊔`-closed subspace of
`[D → D]`). Suprema are inherited from `[D → D]`; infima are derived by `completeLatticeOfSup`. -/
noncomputable instance instCompleteLattice : CompleteLattice (Projections D) :=
  completeLatticeOfSup (Projections D) isLUB_sSup

end Projections

/-- **Scott 1972, Proposition 3.12.** For a (complete, in particular continuous) lattice `D`, the
projections `J_D` form a complete lattice as a `⊔`-closed subspace of `[D → D]`: the `⊔`-closure is
`isProjection_sSup`, and the complete-lattice structure is `Projections.instCompleteLattice`. -/
theorem proposition_3_12 :
    (∀ T : Set (ScottMap D D), (∀ j ∈ T, IsProjection j) → IsProjection (sSup T))
      ∧ Nonempty (CompleteLattice (Projections D)) :=
  ⟨fun _ h => isProjection_sSup h, ⟨Projections.instCompleteLattice⟩⟩

end Projections

/-! ### Proposition 3.13: `D` is a projection of `[D → D]` -/

namespace Proposition313

/-- **Scott 1972, Proposition 3.13.** `con : D → [D → D]` sends `x` to the constant function `x`. -/
noncomputable def con : ScottMap D (ScottMap D D) :=
  ⟨fun x => ScottMap.const x, continuous_of_preservesDirectedSup (by
    intro S _ _
    apply ScottMap.ext
    intro y
    rw [ScottMap.sSup_apply, Set.image_image]
    simp only [ScottMap.const_apply, Set.image_id'])⟩

/-- **Scott 1972, Proposition 3.13.** `min : [D → D] → D` sends `f` to its least value `f(⊥)`. -/
noncomputable def min : ScottMap (ScottMap D D) D :=
  ⟨fun f => (f : D → D) ⊥, continuous_of_preservesDirectedSup (by
    intro F _ _
    show ((sSup F : ScottMap D D) : D → D) ⊥
      = sSup (Set.image (fun f : ScottMap D D => (f : D → D) ⊥) F)
    rw [ScottMap.sSup_apply])⟩

@[simp] theorem con_apply (x y : D) : ((con x : ScottMap D D) : D → D) y = x := rfl

@[simp] theorem min_apply (f : ScottMap D D) : (min f : D) = (f : D → D) ⊥ := rfl

/-- **Scott 1972, Proposition 3.13.** `(con, min)` makes `D` a projection of `[D → D]`:
`min ∘ con = id` (a constant's least value is its value) and `con ∘ min ⊑ id` (the constant `f(⊥)`
is `≤ f` pointwise, since `f(⊥) ⊑ f(y)` by monotonicity). -/
noncomputable def projection : IsContinuousLatticeProjection D (ScottMap D D) where
  incl := con
  retr := min
  retr_incl := fun _ => rfl
  incl_retr_le := fun f => by
    rw [ScottMap.le_def]
    intro y
    show ((ScottMap.const ((f : D → D) ⊥) : ScottMap D D) : D → D) y ≤ (f : D → D) y
    rw [ScottMap.const_apply]
    exact f.monotone bot_le

end Proposition313

/-- **Scott 1972, Proposition 3.13.** Every continuous lattice `D` is a projection of its function
space `[D → D]`, via `con`/`min` (`Proposition313.projection`). -/
theorem proposition_3_13 (_hD : IsContinuousLattice D) :
    Nonempty (IsContinuousLatticeProjection D (ScottMap D D)) :=
  ⟨Proposition313.projection⟩

/-! ### Proposition 3.14: the fixed-point operator `fix : [D → D] → D` -/

namespace Proposition314

/-- The monotone map underlying a Scott map, suitable for `OrderHom.lfp`. -/
def toOrderHom (f : ScottMap D D) : D →o D := ⟨(f : D → D), f.monotone⟩

/-- **Scott 1972, Proposition 3.14.** `fix f` is the least (pre-)fixed point of `f`, supplied by
mathlib's `OrderHom.lfp`. -/
noncomputable def fix (f : ScottMap D D) : D := (toOrderHom f).lfp

/-- `fix f` is a fixed point of `f`. -/
theorem fix_eq (f : ScottMap D D) : (f : D → D) (fix f) = fix f :=
  (toOrderHom f).map_lfp

/-- `fix f` is below every pre-fixed point: `f x ⊑ x ⟹ fix f ⊑ x`. -/
theorem fix_le {f : ScottMap D D} {x : D} (h : (f : D → D) x ≤ x) : fix f ≤ x :=
  (toOrderHom f).lfp_le h

/-- `fix` is monotone in `f`: if `f ⊑ f'` then `fix f ⊑ fix f'`, since `f (fix f') ⊑ f' (fix f') =
fix f'` makes `fix f'` a pre-fixed point of `f`. -/
theorem fix_mono {f f' : ScottMap D D} (hff' : f ≤ f') : fix f ≤ fix f' :=
  fix_le (le_trans (ScottMap.le_def.mp hff' (fix f')) (le_of_eq (fix_eq f')))

/-- **Scott 1972, Proposition 3.14 (continuity).** `fix` preserves directed suprema. Direct
lattice argument (no Kleene iteration): write `g = ⊔S` and `a = ⊔{fix f : f ∈ S}`. The reverse
bound `a ⊑ fix g` is `fix`-monotonicity. For `fix g ⊑ a` it suffices (by `fix_le`) that `a` is a
pre-fixed point of `g`. Now `g a = ⊔_{f∈S} f a` (pointwise sup), and each `f a = ⊔_{f'∈S} f (fix f')`
(continuity of `f` on the directed family `{fix f'}`); for any `f, f' ∈ S` pick `h ∈ S` above both,
so `f (fix f') ⊑ h (fix f') ⊑ h (fix h) = fix h ⊑ a`. Hence `g a ⊑ a`. -/
theorem fix_preservesDirectedSup : PreservesDirectedSup (fix : ScottMap D D → D) := by
  intro S hSne hSdir
  set T : Set D := Set.image fix S with hTdef
  have hTne : T.Nonempty := hSne.image fix
  have hTdir : DirectedOn (· ≤ ·) T := by
    rintro _ ⟨f, hf, rfl⟩ _ ⟨f', hf', rfl⟩
    obtain ⟨h, hh, hfh, hf'h⟩ := hSdir f hf f' hf'
    exact ⟨fix h, Set.mem_image_of_mem fix hh, fix_mono hfh, fix_mono hf'h⟩
  show fix (sSup S) = sSup T
  apply le_antisymm
  · apply fix_le
    show ((sSup S : ScottMap D D) : D → D) (sSup T) ≤ sSup T
    rw [ScottMap.sSup_apply]
    apply sSup_le
    rintro _ ⟨f, hf, rfl⟩
    show (f : D → D) (sSup T) ≤ sSup T
    rw [f.preservesDirectedSup_coe T hTne hTdir]
    apply sSup_le
    rintro _ ⟨_, ⟨f', hf', rfl⟩, rfl⟩
    obtain ⟨h, hh, hfh, hf'h⟩ := hSdir f hf f' hf'
    calc (f : D → D) (fix f')
        ≤ (h : D → D) (fix f') := ScottMap.le_def.mp hfh (fix f')
      _ ≤ (h : D → D) (fix h) := h.monotone (fix_mono hf'h)
      _ = fix h := fix_eq h
      _ ≤ sSup T := le_sSup (Set.mem_image_of_mem fix hh)
  · apply sSup_le
    rintro _ ⟨f, hf, rfl⟩
    exact fix_mono (le_sSup hf)

/-- **Scott 1972, Proposition 3.14.** The fixed-point operator as a Scott-continuous map. -/
noncomputable def fixMap : ScottMap (ScottMap D D) D :=
  ⟨fix, continuous_of_preservesDirectedSup fix_preservesDirectedSup⟩

@[simp] theorem fixMap_apply (f : ScottMap D D) : (fixMap f : D) = fix f := rfl

/-- Uniqueness: any value that is a fixed point of `f` and below every pre-fixed point equals
`fix f` (the least fixed point is unique). -/
theorem fix_unique {f : ScottMap D D} {a : D} (hfix : (f : D → D) a = a)
    (hleast : ∀ x, (f : D → D) x ≤ x → a ≤ x) : a = fix f :=
  le_antisymm (hleast (fix f) (le_of_eq (fix_eq f))) (fix_le hfix.le)

end Proposition314

/-- **Scott 1972, Proposition 3.14.** For a continuous lattice `D` there is a uniquely determined
continuous mapping `fix : [D → D] → D` such that `f (fix f) = fix f` for all `f`, and `fix f ⊑ x`
whenever `f x ⊑ x`. Existence and continuity are `Proposition314.fixMap`; the defining equations are
`fix_eq`/`fix_le`; uniqueness (any operator with these two properties agrees with `fix`) is
`fix_unique`. -/
theorem proposition_3_14 (_hD : IsContinuousLattice D) :
    ∃ Fix : ScottMap (ScottMap D D) D,
      (∀ f : ScottMap D D, (f : D → D) (Fix f) = Fix f)
        ∧ (∀ (f : ScottMap D D) (x : D), (f : D → D) x ≤ x → (Fix f : D) ≤ x)
        ∧ (∀ g : ScottMap D D → D,
            (∀ f : ScottMap D D, (f : D → D) (g f) = g f) →
            (∀ (f : ScottMap D D) (x : D), (f : D → D) x ≤ x → g f ≤ x) →
            ∀ f : ScottMap D D, g f = Fix f) :=
  ⟨Proposition314.fixMap, fun f => Proposition314.fix_eq f,
    fun _ _ h => Proposition314.fix_le h,
    fun _ hfix hleast f => Proposition314.fix_unique (hfix f) (fun x hx => hleast f x hx)⟩

end Scott1972.ContinuousLattice

-- Vendor 1982 — Scott1982.Factoid81 (from vendor/scott1982/Scott1982/Factoid81.lean)

/-!
# Factoid 8.1 — tree / S-expression domain `T ≅ A + (T × T)`

**Scott 1982, §8.** Given `A`, the domain `T` of unlabelled binary trees with atoms
from `A` is defined so tokens, consistency, and entailment match the separated sum
of `A` with the product `T × T` (Scott clauses (1)–(12)). The domain equation then
holds by this matching: we package it as an `InfoSys` on an inductive token type
together with the unfolding map into `A + (T × T)`.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u

/-! ## Tokens (Scott §8 (1)–(3)) -/

/-- Tokens of the tree system: sum tagging of atoms and product left/right copies. -/
inductive TreeToken (α : Type u) where
  | bot : TreeToken α
  | atom : α → TreeToken α
  | pairL : TreeToken α → TreeToken α
  | pairR : TreeToken α → TreeToken α

instance instDecidableEqTreeToken {α : Type u} [DecidableEq α] :
    DecidableEq (TreeToken α)
  | .bot, .bot => isTrue rfl
  | .atom a, .atom b =>
      if h : a = b then isTrue (h ▸ rfl)
      else isFalse fun h' => h (TreeToken.atom.inj h')
  | .pairL a, .pairL b =>
      match instDecidableEqTreeToken a b with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse fun h' => h (TreeToken.pairL.inj h')
  | .pairR a, .pairR b =>
      match instDecidableEqTreeToken a b with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse fun h' => h (TreeToken.pairR.inj h')
  | .bot, .atom _ => isFalse fun h => nomatch h
  | .bot, .pairL _ => isFalse fun h => nomatch h
  | .bot, .pairR _ => isFalse fun h => nomatch h
  | .atom _, .bot => isFalse fun h => nomatch h
  | .atom _, .pairL _ => isFalse fun h => nomatch h
  | .atom _, .pairR _ => isFalse fun h => nomatch h
  | .pairL _, .bot => isFalse fun h => nomatch h
  | .pairL _, .atom _ => isFalse fun h => nomatch h
  | .pairL _, .pairR _ => isFalse fun h => nomatch h
  | .pairR _, .bot => isFalse fun h => nomatch h
  | .pairR _, .atom _ => isFalse fun h => nomatch h
  | .pairR _, .pairL _ => isFalse fun h => nomatch h

variable {α : Type*} [DecidableEq α]

/-- Tree bottom `Δ_T`. -/
def treeBot : TreeToken α := .bot

/-! ## Projections -/

private def Factoid81_atomInsert : TreeToken α → Finset α → Finset α
  | .atom x => insert x
  | .bot | .pairL _ | .pairR _ => id

private def Factoid81_pairLInsert : TreeToken α → Finset (TreeToken α) → Finset (TreeToken α)
  | .pairL t => insert t
  | .bot | .atom _ | .pairR _ => id

private def Factoid81_pairRInsert : TreeToken α → Finset (TreeToken α) → Finset (TreeToken α)
  | .pairR t => insert t
  | .bot | .atom _ | .pairL _ => id

private instance Factoid81_Factoid81_privInst1 : LeftCommutative (Factoid81_atomInsert : TreeToken α → Finset α → Finset α) :=
  ⟨fun p q s => by cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

private instance Factoid81_Factoid81_privInst2 :
    LeftCommutative (Factoid81_pairLInsert : TreeToken α → Finset (TreeToken α) → Finset (TreeToken α)) :=
  ⟨fun p q s => by cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

private instance Factoid81_Factoid81_privInst3 :
    LeftCommutative (Factoid81_pairRInsert : TreeToken α → Finset (TreeToken α) → Finset (TreeToken α)) :=
  ⟨fun p q s => by cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

def atomFinset (u : Finset (TreeToken α)) : Finset α :=
  Multiset.foldr Factoid81_atomInsert (∅ : Finset α) u.1

def pairLFinset (u : Finset (TreeToken α)) : Finset (TreeToken α) :=
  Multiset.foldr Factoid81_pairLInsert (∅ : Finset (TreeToken α)) u.1

def pairRFinset (u : Finset (TreeToken α)) : Finset (TreeToken α) :=
  Multiset.foldr Factoid81_pairRInsert (∅ : Finset (TreeToken α)) u.1

private theorem Factoid81_mem_foldr_atom (s : Multiset (TreeToken α)) (x : α) :
    x ∈ Multiset.foldr Factoid81_atomInsert (∅ : Finset α) s ↔ ∃ p ∈ s, p = .atom x := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hx; exact False.elim (Finset.notMem_empty x hx)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro p t ih
    cases p with
    | atom a =>
      simp only [Multiset.foldr_cons, Factoid81_atomInsert, Finset.mem_insert, ih, Multiset.mem_cons]
      constructor
      · rintro (hx | ⟨q, hq, hq'⟩)
        · exact ⟨.atom a, Or.inl rfl, congrArg TreeToken.atom hx.symm⟩
        · exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · injection hq' with hx; exact Or.inl hx.symm
        · exact Or.inr ⟨q, hq, hq'⟩
    | bot | pairL _ | pairR _ =>
      simp only [Multiset.foldr_cons, Factoid81_atomInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩; exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩

private theorem Factoid81_mem_foldr_pairL (s : Multiset (TreeToken α)) (t : TreeToken α) :
    t ∈ Multiset.foldr Factoid81_pairLInsert (∅ : Finset (TreeToken α)) s ↔
      ∃ p ∈ s, p = .pairL t := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro ht; exact False.elim (Finset.notMem_empty t ht)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro p rest ih
    cases p with
    | pairL a =>
      simp only [Multiset.foldr_cons, Factoid81_pairLInsert, Finset.mem_insert, ih, Multiset.mem_cons]
      constructor
      · rintro (ht | ⟨q, hq, hq'⟩)
        · exact ⟨.pairL a, Or.inl rfl, congrArg TreeToken.pairL ht.symm⟩
        · exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · injection hq' with ht; exact Or.inl ht.symm
        · exact Or.inr ⟨q, hq, hq'⟩
    | bot | atom _ | pairR _ =>
      simp only [Multiset.foldr_cons, Factoid81_pairLInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩; exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩

private theorem Factoid81_mem_foldr_pairR (s : Multiset (TreeToken α)) (t : TreeToken α) :
    t ∈ Multiset.foldr Factoid81_pairRInsert (∅ : Finset (TreeToken α)) s ↔
      ∃ p ∈ s, p = .pairR t := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro ht; exact False.elim (Finset.notMem_empty t ht)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro p rest ih
    cases p with
    | pairR a =>
      simp only [Multiset.foldr_cons, Factoid81_pairRInsert, Finset.mem_insert, ih, Multiset.mem_cons]
      constructor
      · rintro (ht | ⟨q, hq, hq'⟩)
        · exact ⟨.pairR a, Or.inl rfl, congrArg TreeToken.pairR ht.symm⟩
        · exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · injection hq' with ht; exact Or.inl ht.symm
        · exact Or.inr ⟨q, hq, hq'⟩
    | bot | atom _ | pairL _ =>
      simp only [Multiset.foldr_cons, Factoid81_pairRInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩; exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩

theorem mem_atomFinset {u : Finset (TreeToken α)} {x : α} :
    x ∈ atomFinset u ↔ .atom x ∈ u := by
  constructor
  · intro hx
    rcases (Factoid81_mem_foldr_atom u.1 x).1 hx with ⟨p, hp, hp'⟩
    subst hp'; exact Finset.mem_def.2 hp
  · intro hx
    exact (Factoid81_mem_foldr_atom u.1 x).2 ⟨.atom x, Finset.mem_def.1 hx, rfl⟩

theorem mem_pairLFinset {u : Finset (TreeToken α)} {t : TreeToken α} :
    t ∈ pairLFinset u ↔ .pairL t ∈ u := by
  constructor
  · intro ht
    rcases (Factoid81_mem_foldr_pairL u.1 t).1 ht with ⟨p, hp, hp'⟩
    subst hp'; exact Finset.mem_def.2 hp
  · intro ht
    exact (Factoid81_mem_foldr_pairL u.1 t).2 ⟨.pairL t, Finset.mem_def.1 ht, rfl⟩

theorem mem_pairRFinset {u : Finset (TreeToken α)} {t : TreeToken α} :
    t ∈ pairRFinset u ↔ .pairR t ∈ u := by
  constructor
  · intro ht
    rcases (Factoid81_mem_foldr_pairR u.1 t).1 ht with ⟨p, hp, hp'⟩
    subst hp'; exact Finset.mem_def.2 hp
  · intro ht
    exact (Factoid81_mem_foldr_pairR u.1 t).2 ⟨.pairR t, Finset.mem_def.1 ht, rfl⟩

theorem atomFinset_empty : atomFinset (∅ : Finset (TreeToken α)) = ∅ := rfl
theorem pairLFinset_empty : pairLFinset (∅ : Finset (TreeToken α)) = ∅ := rfl
theorem pairRFinset_empty : pairRFinset (∅ : Finset (TreeToken α)) = ∅ := rfl

theorem atomFinset_mono {u v : Finset (TreeToken α)} (h : v ⊆ u) :
    atomFinset v ⊆ atomFinset u := fun _ hx => mem_atomFinset.2 (h (mem_atomFinset.1 hx))

theorem pairLFinset_mono {u v : Finset (TreeToken α)} (h : v ⊆ u) :
    pairLFinset v ⊆ pairLFinset u := fun _ ht => mem_pairLFinset.2 (h (mem_pairLFinset.1 ht))

theorem pairRFinset_mono {u v : Finset (TreeToken α)} (h : v ⊆ u) :
    pairRFinset v ⊆ pairRFinset u := fun _ ht => mem_pairRFinset.2 (h (mem_pairRFinset.1 ht))

theorem atomFinset_insert_atom (u : Finset (TreeToken α)) (x : α) :
    atomFinset (insert (.atom x) u) = insert x (atomFinset u) := by
  ext y; simp only [Finset.mem_insert, mem_atomFinset]
  constructor
  · rintro (h | h)
    · exact Or.inl (TreeToken.atom.inj h)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

theorem atomFinset_insert_bot (u : Finset (TreeToken α)) :
    atomFinset (insert (.bot : TreeToken α) u) = atomFinset u := by
  ext x; simp only [mem_atomFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem atomFinset_insert_pairL (u : Finset (TreeToken α)) (t : TreeToken α) :
    atomFinset (insert (.pairL t) u) = atomFinset u := by
  ext x; simp only [mem_atomFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem atomFinset_insert_pairR (u : Finset (TreeToken α)) (t : TreeToken α) :
    atomFinset (insert (.pairR t) u) = atomFinset u := by
  ext x; simp only [mem_atomFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem pairLFinset_insert_pairL (u : Finset (TreeToken α)) (t : TreeToken α) :
    pairLFinset (insert (.pairL t) u) = insert t (pairLFinset u) := by
  ext s; simp only [Finset.mem_insert, mem_pairLFinset]
  constructor
  · rintro (h | h)
    · exact Or.inl (TreeToken.pairL.inj h)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

theorem pairLFinset_insert_bot (u : Finset (TreeToken α)) :
    pairLFinset (insert (.bot : TreeToken α) u) = pairLFinset u := by
  ext t; simp only [mem_pairLFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem pairLFinset_insert_atom (u : Finset (TreeToken α)) (x : α) :
    pairLFinset (insert (.atom x) u) = pairLFinset u := by
  ext t; simp only [mem_pairLFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem pairLFinset_insert_pairR (u : Finset (TreeToken α)) (t : TreeToken α) :
    pairLFinset (insert (.pairR t) u) = pairLFinset u := by
  ext s; simp only [mem_pairLFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem pairRFinset_insert_pairR (u : Finset (TreeToken α)) (t : TreeToken α) :
    pairRFinset (insert (.pairR t) u) = insert t (pairRFinset u) := by
  ext s; simp only [Finset.mem_insert, mem_pairRFinset]
  constructor
  · rintro (h | h)
    · exact Or.inl (TreeToken.pairR.inj h)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

theorem pairRFinset_insert_bot (u : Finset (TreeToken α)) :
    pairRFinset (insert (.bot : TreeToken α) u) = pairRFinset u := by
  ext t; simp only [mem_pairRFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem pairRFinset_insert_atom (u : Finset (TreeToken α)) (x : α) :
    pairRFinset (insert (.atom x) u) = pairRFinset u := by
  ext t; simp only [mem_pairRFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem pairRFinset_insert_pairL (u : Finset (TreeToken α)) (t : TreeToken α) :
    pairRFinset (insert (.pairL t) u) = pairRFinset u := by
  ext s; simp only [mem_pairRFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem atomFinset_singleton_atom (x : α) :
    atomFinset ({.atom x} : Finset (TreeToken α)) = {x} := by
  ext y; simp only [mem_atomFinset, Finset.mem_singleton]
  exact ⟨fun h => TreeToken.atom.inj h, fun h => congrArg TreeToken.atom h⟩

theorem pairLFinset_singleton_pairL (t : TreeToken α) :
    pairLFinset ({.pairL t} : Finset (TreeToken α)) = {t} := by
  ext s; simp only [mem_pairLFinset, Finset.mem_singleton]
  exact ⟨fun h => TreeToken.pairL.inj h, fun h => congrArg TreeToken.pairL h⟩

theorem pairRFinset_singleton_pairR (t : TreeToken α) :
    pairRFinset ({.pairR t} : Finset (TreeToken α)) = {t} := by
  ext s; simp only [mem_pairRFinset, Finset.mem_singleton]
  exact ⟨fun h => TreeToken.pairR.inj h, fun h => congrArg TreeToken.pairR h⟩

theorem atomFinset_singleton_bot :
    atomFinset ({.bot} : Finset (TreeToken α)) = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim (nomatch mem_atomFinset.1 hx)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem pairLFinset_singleton_bot :
    pairLFinset ({.bot} : Finset (TreeToken α)) = ∅ := by
  ext t
  constructor
  · intro ht
    exact False.elim (nomatch mem_pairLFinset.1 ht)
  · intro ht
    exact False.elim (Finset.notMem_empty t ht)

theorem pairRFinset_singleton_bot :
    pairRFinset ({.bot} : Finset (TreeToken α)) = ∅ := by
  ext t
  constructor
  · intro ht
    exact False.elim (nomatch mem_pairRFinset.1 ht)
  · intro ht
    exact False.elim (Finset.notMem_empty t ht)

theorem pairLFinset_singleton_atom (x : α) :
    pairLFinset ({.atom x} : Finset (TreeToken α)) = ∅ := by
  ext t
  constructor
  · intro ht
    exact False.elim (nomatch mem_pairLFinset.1 ht)
  · intro ht
    exact False.elim (Finset.notMem_empty t ht)

theorem pairRFinset_singleton_atom (x : α) :
    pairRFinset ({.atom x} : Finset (TreeToken α)) = ∅ := by
  ext t
  constructor
  · intro ht
    exact False.elim (nomatch mem_pairRFinset.1 ht)
  · intro ht
    exact False.elim (Finset.notMem_empty t ht)

theorem atomFinset_singleton_pairL (t : TreeToken α) :
    atomFinset ({.pairL t} : Finset (TreeToken α)) = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim (nomatch mem_atomFinset.1 hx)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem atomFinset_singleton_pairR (t : TreeToken α) :
    atomFinset ({.pairR t} : Finset (TreeToken α)) = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim (nomatch mem_atomFinset.1 hx)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem pairRFinset_singleton_pairL (t : TreeToken α) :
    pairRFinset ({.pairL t} : Finset (TreeToken α)) = ∅ := by
  ext s
  constructor
  · intro hs
    exact False.elim (nomatch mem_pairRFinset.1 hs)
  · intro hs
    exact False.elim (Finset.notMem_empty s hs)

theorem pairLFinset_singleton_pairR (t : TreeToken α) :
    pairLFinset ({.pairR t} : Finset (TreeToken α)) = ∅ := by
  ext s
  constructor
  · intro hs
    exact False.elim (nomatch mem_pairLFinset.1 hs)
  · intro hs
    exact False.elim (Finset.notMem_empty s hs)

/-! ## Consistency and entailment -/

variable (A : InfoSys α)

/-- Consistency for trees (Scott §8 (4)–(7)). -/
inductive TreeCon : Finset (TreeToken α) → Prop where
  | left (u : Finset (TreeToken α))
      (hA : atomFinset u ∈ A.Con)
      (hL : pairLFinset u = ∅) (hR : pairRFinset u = ∅) : TreeCon u
  | right (u : Finset (TreeToken α))
      (hA : atomFinset u = ∅)
      (hL : TreeCon (pairLFinset u)) (hR : TreeCon (pairRFinset u)) : TreeCon u

theorem TreeCon_empty : TreeCon A (∅ : Finset (TreeToken α)) :=
  TreeCon.left _ (by rw [atomFinset_empty]; exact A.con_empty)
    pairLFinset_empty pairRFinset_empty

/-- Payload of tree entailment (Scott §8 (8)–(12)), recursive on the token.

The extra disjuncts for `pairL bot` / `pairR bot` match official product
`ent_bot`: any nonempty pair-set entails the unique product bottom, which
`treeUnfold` identifies as both constructors. Without them, closed tree
elements could contain one encoding of `(Δ,Δ)` but not the other, and
`|T|` would fail to be order-isomorphic to `|A + (T × T)|`. -/
def TreeEntPayload (u : Finset (TreeToken α)) : TreeToken α → Prop
  | .bot => True
  | .atom x => atomFinset u ≠ ∅ ∧ A.Ent (atomFinset u) x
  | .pairL t =>
      atomFinset u = ∅ ∧ TreeCon A (pairLFinset u) ∧ TreeCon A (pairRFinset u) ∧
        ((pairLFinset u ≠ ∅ ∧ TreeEntPayload (pairLFinset u) t) ∨
          (t = .bot ∧ pairRFinset u ≠ ∅))
  | .pairR t =>
      atomFinset u = ∅ ∧ TreeCon A (pairRFinset u) ∧ TreeCon A (pairLFinset u) ∧
        ((pairRFinset u ≠ ∅ ∧ TreeEntPayload (pairRFinset u) t) ∨
          (t = .bot ∧ pairLFinset u ≠ ∅))

/-- Entailment for trees. -/
def TreeEnt (u : Finset (TreeToken α)) (p : TreeToken α) : Prop :=
  TreeCon A u ∧ TreeEntPayload A u p

theorem TreeCon_pairs_empty_of_left {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (hA : atomFinset u ≠ ∅) :
    pairLFinset u = ∅ ∧ pairRFinset u = ∅ := by
  cases hu with
  | left _ _ hL hR => exact ⟨hL, hR⟩
  | right _ hAt _ _ => exact False.elim (hA hAt)

theorem TreeCon_atoms_empty_of_right {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (hP : pairLFinset u ≠ ∅ ∨ pairRFinset u ≠ ∅) :
    atomFinset u = ∅ := by
  cases hu with
  | left _ _ hL hR =>
    rcases hP with h | h
    · exact False.elim (h hL)
    · exact False.elim (h hR)
  | right _ hA _ _ => exact hA

theorem TreeCon_atom_con_of_atoms {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (hne : atomFinset u ≠ ∅) : atomFinset u ∈ A.Con := by
  cases hu with
  | left _ hA _ _ => exact hA
  | right _ hA _ _ => exact False.elim (hne hA)

theorem TreeCon_pairL_of_right {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (_hA : atomFinset u = ∅) : TreeCon A (pairLFinset u) := by
  cases hu with
  | left _ _ hL _ => rw [hL]; exact TreeCon_empty A
  | right _ _ hL _ => exact hL

theorem TreeCon_pairR_of_right {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (_hA : atomFinset u = ∅) : TreeCon A (pairRFinset u) := by
  cases hu with
  | left _ _ _ hR => rw [hR]; exact TreeCon_empty A
  | right _ _ _ hR => exact hR

theorem TreeCon_singleton (p : TreeToken α) : TreeCon A {p} := by
  induction p with
  | bot =>
    exact TreeCon.left _
      (by rw [atomFinset_singleton_bot]; exact A.con_empty)
      pairLFinset_singleton_bot pairRFinset_singleton_bot
  | atom x =>
    exact TreeCon.left _
      (by rw [atomFinset_singleton_atom]; exact A.con_sing x)
      (pairLFinset_singleton_atom x) (pairRFinset_singleton_atom x)
  | pairL t ih =>
    exact TreeCon.right _
      (atomFinset_singleton_pairL t)
      (by rw [pairLFinset_singleton_pairL]; exact ih)
      (by rw [pairRFinset_singleton_pairL]; exact TreeCon_empty A)
  | pairR t ih =>
    exact TreeCon.right _
      (atomFinset_singleton_pairR t)
      (by rw [pairLFinset_singleton_pairR]; exact TreeCon_empty A)
      (by rw [pairRFinset_singleton_pairR]; exact ih)

theorem TreeEntPayload_of_mem {u : Finset (TreeToken α)} {p : TreeToken α}
    (hu : TreeCon A u) (hp : p ∈ u) : TreeEntPayload A u p := by
  induction p generalizing u with
  | bot => exact trivial
  | atom x =>
    have hx : x ∈ atomFinset u := mem_atomFinset.2 hp
    exact ⟨Finset.ne_empty_of_mem hx,
      A.ent_refl (TreeCon_atom_con_of_atoms A hu (Finset.ne_empty_of_mem hx)) hx⟩
  | pairL t ih =>
    have ht : t ∈ pairLFinset u := mem_pairLFinset.2 hp
    have hne := Finset.ne_empty_of_mem ht
    have hAt := TreeCon_atoms_empty_of_right A hu (Or.inl hne)
    exact ⟨hAt, TreeCon_pairL_of_right A hu hAt, TreeCon_pairR_of_right A hu hAt,
      Or.inl ⟨hne, ih (TreeCon_pairL_of_right A hu hAt) ht⟩⟩
  | pairR t ih =>
    have ht : t ∈ pairRFinset u := mem_pairRFinset.2 hp
    have hne := Finset.ne_empty_of_mem ht
    have hAt := TreeCon_atoms_empty_of_right A hu (Or.inr hne)
    exact ⟨hAt, TreeCon_pairR_of_right A hu hAt, TreeCon_pairL_of_right A hu hAt,
      Or.inl ⟨hne, ih (TreeCon_pairR_of_right A hu hAt) ht⟩⟩

theorem TreeEnt_of_mem {u : Finset (TreeToken α)} {p : TreeToken α}
    (hu : TreeCon A u) (hp : p ∈ u) : TreeEnt A u p :=
  ⟨hu, TreeEntPayload_of_mem A hu hp⟩

theorem TreeCon_insert_bot {u : Finset (TreeToken α)} (hu : TreeCon A u) :
    TreeCon A (insert .bot u) := by
  cases hu with
  | left _ hA hL hR =>
    exact TreeCon.left _
      (by rw [atomFinset_insert_bot]; exact hA)
      (by rw [pairLFinset_insert_bot]; exact hL)
      (by rw [pairRFinset_insert_bot]; exact hR)
  | right _ hA hL hR =>
    exact TreeCon.right _
      (by rw [atomFinset_insert_bot]; exact hA)
      (by rw [pairLFinset_insert_bot]; exact hL)
      (by rw [pairRFinset_insert_bot]; exact hR)

theorem TreeCon_insert_of_ent {u : Finset (TreeToken α)} {p : TreeToken α}
    (h : TreeEnt A u p) : TreeCon A (insert p u) := by
  induction p generalizing u with
  | bot =>
    exact TreeCon_insert_bot A h.1
  | atom x =>
    rcases h with ⟨hu, hne, hA⟩
    have hLR := TreeCon_pairs_empty_of_left A hu hne
    exact TreeCon.left _
      (by rw [atomFinset_insert_atom]; exact A.ent_con hA)
      (by rw [pairLFinset_insert_atom]; exact hLR.1)
      (by rw [pairRFinset_insert_atom]; exact hLR.2)
  | pairL t ih =>
    rcases h with ⟨_, hAt, hConL, hConR, hOr⟩
    refine TreeCon.right _
      (by rw [atomFinset_insert_pairL]; exact hAt) ?_
      (by rw [pairRFinset_insert_pairL]; exact hConR)
    rw [pairLFinset_insert_pairL]
    rcases hOr with ⟨_, hPay⟩ | ⟨rfl, _⟩
    · exact ih ⟨hConL, hPay⟩
    · exact TreeCon_insert_bot A hConL
  | pairR t ih =>
    rcases h with ⟨_, hAt, hConR, hConL, hOr⟩
    refine TreeCon.right _
      (by rw [atomFinset_insert_pairR]; exact hAt)
      (by rw [pairLFinset_insert_pairR]; exact hConL) ?_
    rw [pairRFinset_insert_pairR]
    rcases hOr with ⟨_, hPay⟩ | ⟨rfl, _⟩
    · exact ih ⟨hConR, hPay⟩
    · exact TreeCon_insert_bot A hConR

theorem TreeEntPayload_of_no_atoms_no_pairs {u : Finset (TreeToken α)} {t : TreeToken α}
    (hAt : atomFinset u = ∅) (hL : pairLFinset u = ∅) (hR : pairRFinset u = ∅)
    (h : TreeEntPayload A u t) : t = .bot := by
  cases t with
  | bot => rfl
  | atom x => exact False.elim (h.1 hAt)
  | pairL t =>
    rcases h with ⟨_, _, _, hOr⟩
    rcases hOr with ⟨hne, _⟩ | ⟨_, hRne⟩
    · exact False.elim (hne hL)
    · exact False.elim (hRne hR)
  | pairR t =>
    rcases h with ⟨_, _, _, hOr⟩
    rcases hOr with ⟨hne, _⟩ | ⟨_, hLne⟩
    · exact False.elim (hne hR)
    · exact False.elim (hLne hL)

theorem pairL_ne_or_subset_bot {u v : Finset (TreeToken α)}
    (hEnts : ∀ y ∈ pairLFinset u, TreeEnt A v (.pairL y)) :
    pairLFinset v ≠ ∅ ∨ pairLFinset u ⊆ {.bot} := by
  revert hEnts
  induction pairLFinset u using Finset.induction with
  | empty =>
    intro; exact Or.inr (Finset.empty_subset _)
  | insert y s hys ih =>
    intro hEnts
    have hy := hEnts y (Finset.mem_insert_self _ _)
    rcases hy.2.2.2.2 with ⟨hneV, _⟩ | ⟨rfl, _⟩
    · exact Or.inl hneV
    · rcases ih (fun z hz => hEnts z (Finset.mem_insert_of_mem hz)) with h | hsub
      · exact Or.inl h
      · refine Or.inr ?_
        intro z hz
        rcases Finset.mem_insert.1 hz with rfl | hz
        · exact Finset.mem_singleton_self _
        · exact hsub hz

theorem pairR_ne_or_subset_bot {u v : Finset (TreeToken α)}
    (hEnts : ∀ y ∈ pairRFinset u, TreeEnt A v (.pairR y)) :
    pairRFinset v ≠ ∅ ∨ pairRFinset u ⊆ {.bot} := by
  revert hEnts
  induction pairRFinset u using Finset.induction with
  | empty =>
    intro; exact Or.inr (Finset.empty_subset _)
  | insert y s hys ih =>
    intro hEnts
    have hy := hEnts y (Finset.mem_insert_self _ _)
    rcases hy.2.2.2.2 with ⟨hneV, _⟩ | ⟨rfl, _⟩
    · exact Or.inl hneV
    · rcases ih (fun z hz => hEnts z (Finset.mem_insert_of_mem hz)) with h | hsub
      · exact Or.inl h
      · refine Or.inr ?_
        intro z hz
        rcases Finset.mem_insert.1 hz with rfl | hz
        · exact Finset.mem_singleton_self _
        · exact hsub hz

theorem eq_singleton_bot_of_subset {s : Finset (TreeToken α)}
    (hne : s ≠ ∅) (hsub : s ⊆ {.bot}) : s = {.bot} := by
  ext y
  constructor
  · exact fun hy => hsub hy
  · intro hy
    have : y = .bot := Finset.mem_singleton.1 hy
    subst this
    obtain ⟨z, hz⟩ := Finset.nonempty_of_ne_empty hne
    have hzbot : z = .bot := Finset.mem_singleton.1 (hsub hz)
    exact hzbot ▸ hz

theorem TreeEntPayload_trans {u v : Finset (TreeToken α)} {c : TreeToken α}
    (hv : TreeCon A v) (hu : TreeCon A u)
    (hEnts : ∀ y ∈ u, TreeEnt A v y) (hPay : TreeEntPayload A u c) :
    TreeEntPayload A v c := by
  induction c generalizing u v with
  | bot => exact trivial
  | atom x =>
    rcases hPay with ⟨hne, hA⟩
    have hlft : ∀ y ∈ atomFinset u, A.Ent (atomFinset v) y := by
      intro y hy
      exact (hEnts _ (mem_atomFinset.1 hy)).2.2
    have hne' : atomFinset v ≠ ∅ := by
      obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty hne
      exact (hEnts _ (mem_atomFinset.1 hy)).2.1
    exact ⟨hne', A.ent_trans (TreeCon_atom_con_of_atoms A hv hne')
      (TreeCon_atom_con_of_atoms A hu hne) hlft hA⟩
  | pairL t ih =>
    rcases hPay with ⟨hAt, hConL, hConR, hOr⟩
    rcases hOr with ⟨hne, hPayL⟩ | ⟨rfl, hRne⟩
    · obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hne
      have hEy := hEnts _ (mem_pairLFinset.1 hs)
      have hAtv : atomFinset v = ∅ := hEy.2.1
      have hConLv : TreeCon A (pairLFinset v) := TreeCon_pairL_of_right A hv hAtv
      have hConRv : TreeCon A (pairRFinset v) := hEy.2.2.2.1
      have hEntsL : ∀ y ∈ pairLFinset u, TreeEnt A (pairLFinset v) y := by
        intro y hy
        have hEy' := hEnts _ (mem_pairLFinset.1 hy)
        rcases hEy'.2.2.2.2 with ⟨_, hPay'⟩ | ⟨rfl, _⟩
        · exact ⟨hEy'.2.2.1, hPay'⟩
        · exact ⟨hConLv, trivial⟩
      refine ⟨hAtv, hConLv, hConRv, ?_⟩
      have hEntsPair : ∀ y ∈ pairLFinset u, TreeEnt A v (.pairL y) :=
        fun y hy => hEnts _ (mem_pairLFinset.1 hy)
      rcases pairL_ne_or_subset_bot A hEntsPair with hneV | hsub
      · exact Or.inl ⟨hneV, ih hConLv hConL hEntsL hPayL⟩
      · have huBot : pairLFinset u = {.bot} :=
          eq_singleton_bot_of_subset hne hsub
        have ht : t = .bot :=
          TreeEntPayload_of_no_atoms_no_pairs A
            atomFinset_singleton_bot pairLFinset_singleton_bot
            pairRFinset_singleton_bot (huBot ▸ hPayL)
        rcases hEy.2.2.2.2 with ⟨hneV, _⟩ | ⟨_, hR⟩
        · exact Or.inl ⟨hneV, ih hConLv hConL hEntsL hPayL⟩
        · exact Or.inr ⟨ht, hR⟩
    · obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hRne
      have hEy := hEnts _ (mem_pairRFinset.1 hs)
      have hAtv : atomFinset v = ∅ := hEy.2.1
      refine ⟨hAtv, TreeCon_pairL_of_right A hv hAtv, hEy.2.2.1, ?_⟩
      rcases hEy.2.2.2.2 with ⟨hneR, _⟩ | ⟨_, hneL⟩
      · exact Or.inr ⟨rfl, hneR⟩
      · exact Or.inl ⟨hneL, trivial⟩
  | pairR t ih =>
    rcases hPay with ⟨hAt, hConR, hConL, hOr⟩
    rcases hOr with ⟨hne, hPayR⟩ | ⟨rfl, hLne⟩
    · obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hne
      have hEy := hEnts _ (mem_pairRFinset.1 hs)
      have hAtv : atomFinset v = ∅ := hEy.2.1
      have hConRv : TreeCon A (pairRFinset v) := TreeCon_pairR_of_right A hv hAtv
      have hConLv : TreeCon A (pairLFinset v) := hEy.2.2.2.1
      have hEntsR : ∀ y ∈ pairRFinset u, TreeEnt A (pairRFinset v) y := by
        intro y hy
        have hEy' := hEnts _ (mem_pairRFinset.1 hy)
        rcases hEy'.2.2.2.2 with ⟨_, hPay'⟩ | ⟨rfl, _⟩
        · exact ⟨hEy'.2.2.1, hPay'⟩
        · exact ⟨hConRv, trivial⟩
      refine ⟨hAtv, hConRv, hConLv, ?_⟩
      have hEntsPair : ∀ y ∈ pairRFinset u, TreeEnt A v (.pairR y) :=
        fun y hy => hEnts _ (mem_pairRFinset.1 hy)
      rcases pairR_ne_or_subset_bot A hEntsPair with hneV | hsub
      · exact Or.inl ⟨hneV, ih hConRv hConR hEntsR hPayR⟩
      · have huBot : pairRFinset u = {.bot} :=
          eq_singleton_bot_of_subset hne hsub
        have ht : t = .bot :=
          TreeEntPayload_of_no_atoms_no_pairs A
            atomFinset_singleton_bot pairLFinset_singleton_bot
            pairRFinset_singleton_bot (huBot ▸ hPayR)
        rcases hEy.2.2.2.2 with ⟨hneV, _⟩ | ⟨_, hL⟩
        · exact Or.inl ⟨hneV, ih hConRv hConR hEntsR hPayR⟩
        · exact Or.inr ⟨ht, hL⟩
    · obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hLne
      have hEy := hEnts _ (mem_pairLFinset.1 hs)
      have hAtv : atomFinset v = ∅ := hEy.2.1
      refine ⟨hAtv, TreeCon_pairR_of_right A hv hAtv, hEy.2.2.1, ?_⟩
      rcases hEy.2.2.2.2 with ⟨hneL, _⟩ | ⟨_, hneR⟩
      · exact Or.inr ⟨rfl, hneL⟩
      · exact Or.inl ⟨hneR, trivial⟩

theorem TreeEnt_trans {u v : Finset (TreeToken α)} {c : TreeToken α}
    (hv : TreeCon A v) (hu : TreeCon A u)
    (hEnts : ∀ y ∈ u, TreeEnt A v y) (hEntc : TreeEnt A u c) :
    TreeEnt A v c :=
  ⟨hv, TreeEntPayload_trans A hv hu hEnts hEntc.2⟩

theorem TreeCon_subset {u : Finset (TreeToken α)} (hu : TreeCon A u) :
    ∀ {v}, v ⊆ u → TreeCon A v := by
  induction hu with
  | left u hA hL hR =>
    intro v hv
    refine TreeCon.left v (A.con_subset hA (atomFinset_mono hv)) ?_ ?_
    · exact Finset.Subset.antisymm
        (fun t ht => by
          have : t ∈ pairLFinset u := pairLFinset_mono hv ht
          rw [hL] at this; exact False.elim (Finset.notMem_empty t this))
        (Finset.empty_subset _)
    · exact Finset.Subset.antisymm
        (fun t ht => by
          have : t ∈ pairRFinset u := pairRFinset_mono hv ht
          rw [hR] at this; exact False.elim (Finset.notMem_empty t this))
        (Finset.empty_subset _)
  | right u hA hL hR ihL ihR =>
    intro v hv
    refine TreeCon.right v
      (Finset.Subset.antisymm
        (fun x hx => by
          have : x ∈ atomFinset u := atomFinset_mono hv hx
          rw [hA] at this; exact False.elim (Finset.notMem_empty x this))
        (Finset.empty_subset _))
      (ihL (pairLFinset_mono hv)) (ihR (pairRFinset_mono hv))

/-- **Factoid 8.1.** Tree information system solving `T ≅ A + (T × T)` by construction. -/
def treeSystem : InfoSys (TreeToken α) where
  bot := treeBot
  Con := {u | TreeCon A u}
  Ent := TreeEnt A
  con_subset := fun hu hv => TreeCon_subset A hu hv
  con_sing := TreeCon_singleton A
  ent_con := fun h => TreeCon_insert_of_ent A h
  ent_bot := fun hu => ⟨hu, trivial⟩
  ent_refl := fun hu hp => TreeEnt_of_mem A hu hp
  ent_trans := fun hv hu hEnts hEntc => TreeEnt_trans A hv hu hEnts hEntc

/-! ## Domain equation

Scott secures `T ≅ A + (T × T)` by choosing tokens so that `T` is literally the
sum-of-product system. Here `TreeToken` is the inductive presentation of that
tagging (clauses (1)–(3)), and `TreeCon`/`TreeEnt` are the sum×product clauses
((4)–(12)). Unfolding compares with the official `sumSystem` / `productSystem`
carriers; `pairL bot` and `pairR bot` both land on the unique product bottom,
matching Scott’s single `(Δ,(Δ,Δ))`.
-/

/-- Unfold a tree token into the sum-of-product carrier. -/
def treeUnfold (t : TreeToken α) :
    SumToken α (ProdToken (treeSystem A) (treeSystem A)) :=
  match t with
  | .bot => .bot
  | .atom x => .left x
  | .pairL t => .right ⟨(t, treeBot), Or.inr rfl⟩
  | .pairR t => .right ⟨(treeBot, t), Or.inl rfl⟩

theorem treeUnfold_bot : treeUnfold A treeBot = SumToken.bot := rfl

theorem treeUnfold_atom (x : α) : treeUnfold A (.atom x) = SumToken.left x := rfl

theorem treeUnfold_pairL (t : TreeToken α) :
    treeUnfold A (.pairL t) = .right ⟨(t, treeBot), Or.inr rfl⟩ := rfl

theorem treeUnfold_pairR (t : TreeToken α) :
    treeUnfold A (.pairR t) = .right ⟨(treeBot, t), Or.inl rfl⟩ := rfl

theorem treeUnfold_pairL_bot_eq_pairR_bot :
    treeUnfold A (.pairL treeBot) = treeUnfold A (.pairR treeBot) := rfl

/-- The right-hand side of the domain equation is the official sum of products. -/
def treeRhs : InfoSys (SumToken α (ProdToken (treeSystem A) (treeSystem A))) :=
  sumSystem A (productSystem (treeSystem A) (treeSystem A))

theorem treeRhs_eq_sum_product :
    treeRhs A = sumSystem A (productSystem (treeSystem A) (treeSystem A)) :=
  rfl

end InfoSys

end Scott1982

-- Vendor 1982 — Scott1982.Factoid24 (from vendor/scott1982/Scott1982/Factoid24.lean)

/-!
# Factoid 2.4 — first example: lower bounds on ℕ

**Scott 1982, §2 (“A first example”).** Data objects are non-negative integers,
read as propositions `n ≤ x`. Take `Δ = 0`, every finite set consistent, and

```
{n₀, …, nₖ₋₁} ⊢ m  iff  m = 0  ∨  ∃ i, m ≤ nᵢ.
```

Scott: “That ⊢ is an entailment relation in the sense of our axioms is clear.”
We package this as an `example` that builds an `InfoSys ℕ` and discharges Def 2.1.
-/

namespace Scott1982

namespace Factoid24

/-- Entailment for the lower-bound system: `u ⊢ m` iff `m = 0` or some `n ∈ u` has `m ≤ n`. -/
def lowerBoundEnt (u : Finset ℕ) (m : ℕ) : Prop :=
  m = 0 ∨ ∃ n ∈ u, m ≤ n

/-- **Factoid 2.4.** The ℕ lower-bound information system of Scott 1982, §2. -/
example : InfoSys ℕ where
  bot := 0
  Con := Set.univ
  Ent := lowerBoundEnt
  con_subset := by
    intro u v _ _
    exact Set.mem_univ v
  con_sing := by
    intro a
    exact Set.mem_univ _
  ent_con := by
    intro u a _
    exact Set.mem_univ _
  ent_bot := by
    intro u _
    exact Or.inl rfl
  ent_refl := by
    intro u a _ ha
    exact Or.inr ⟨a, ha, le_rfl⟩
  ent_trans := by
    intro u v c _ _ hvEnt huEnt
    rcases huEnt with rfl | ⟨n, hn, hcn⟩
    · exact Or.inl rfl
    · -- `u ⊢ c` via witness `n ∈ u` with `c ≤ n`; use `v ⊢ n`
      rcases hvEnt n hn with rfl | ⟨k, hk, hnk⟩
      · -- `n = 0`, so `c ≤ 0` ⇒ `c = 0`
        exact Or.inl (Nat.le_zero.mp hcn)
      · exact Or.inr ⟨k, hk, le_trans hcn hnk⟩

end Factoid24

end Scott1982

/-! ## Bridge theorems -/

-- Bridge — ScottModels.NeighborhoodToInfoSys (from ScottModels/NeighborhoodToInfoSys.lean)

/-!
# Neighbourhood systems → information systems (1980 → 1982)

Scott (1982) notes that neighbourhood systems and information systems are equivalent
in a precise sense. This module realises one direction: given a neighbourhood system
presented with a **decidable index of its neighbourhoods** (a constructive coding of
`𝒟`), build an information system on those indices whose domain is order-isomorphic
to the original filter domain.

Tokens of the information system are indices of neighbourhoods; consistency is
membership of the finite intersection in `𝒟` (Scott’s empty intersection = `Δ`);
entailment is “the intersection is a neighbourhood and is contained in the target.”
-/

namespace ScottModels

open Scott1980.Neighborhood
open Scott1982

/-- A neighbourhood system with a decidable exhaustive index of its neighbourhoods.
`DecidableEq ι` is required so the induced information system can use choice-free
`Finset` operations (`InfoSys` tokens). -/
structure NbhdBasis (ι α : Type*) [DecidableEq ι] where
  system : NeighborhoodSystem α
  nbhd : ι → Set α
  nbhd_mem : ∀ i, system.mem (nbhd i)
  exhaustive : ∀ {X : Set α}, system.mem X → ∃ i, nbhd i = X
  botIdx : ι
  botIdx_eq : nbhd botIdx = system.master

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

/-- Finite intersection of coded neighbourhoods, with Scott’s convention `⋂∅ = Δ`. -/
def interOf (u : Finset ι) : Set α :=
  u.fold (· ∩ ·) B.system.master B.nbhd

@[simp] theorem interOf_empty : B.interOf (∅ : Finset ι) = B.system.master := rfl

theorem interOf_insert {a : ι} {s : Finset ι} (ha : a ∉ s) :
    B.interOf (insert a s) = B.nbhd a ∩ B.interOf s :=
  Finset.fold_insert (op := (· ∩ ·)) ha

theorem nbhd_subset_master (i : ι) : B.nbhd i ⊆ B.system.master :=
  B.system.sub_master (B.nbhd_mem i)

theorem interOf_singleton (a : ι) : B.interOf ({a} : Finset ι) = B.nbhd a := by
  simp [interOf, Finset.fold_singleton, Set.inter_eq_left.mpr (B.nbhd_subset_master a)]

/-- Membership in the folded intersection. -/
theorem mem_interOf {u : Finset ι} {x : α} :
    x ∈ B.interOf u ↔ x ∈ B.system.master ∧ ∀ i ∈ u, x ∈ B.nbhd i := by
  induction u using Finset.induction with
  | empty =>
    simp [interOf_empty]
  | insert a s ha ih =>
    rw [B.interOf_insert ha, Set.mem_inter_iff, ih]
    constructor
    · rintro ⟨ha', hm, hs⟩
      refine ⟨hm, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ha'
      · exact hs i hi
    · rintro ⟨hm, hall⟩
      exact ⟨hall a (Finset.mem_insert_self a s), hm,
        fun i hi => hall i (Finset.mem_insert_of_mem hi)⟩

theorem interOf_subset_nbhd {u : Finset ι} {i : ι} (hi : i ∈ u) :
    B.interOf u ⊆ B.nbhd i := fun _ hx => (B.mem_interOf.mp hx).2 i hi

theorem interOf_subset_master (u : Finset ι) : B.interOf u ⊆ B.system.master :=
  fun _ hx => (B.mem_interOf.mp hx).1

/-- Larger index sets give smaller intersections. -/
theorem interOf_anti {u v : Finset ι} (h : u ⊆ v) : B.interOf v ⊆ B.interOf u := by
  intro x hx
  exact B.mem_interOf.mpr ⟨(B.mem_interOf.mp hx).1, fun i hi => (B.mem_interOf.mp hx).2 i (h hi)⟩

/-- If a neighbourhood sits below `interOf u`, then `interOf u ∈ 𝒟`. -/
theorem interOf_mem_of_lower_bound {u : Finset ι} {Z : Set α}
    (hZ : B.system.mem Z) (hsub : Z ⊆ B.interOf u) : B.system.mem (B.interOf u) := by
  induction u using Finset.induction with
  | empty =>
    simpa [interOf_empty] using B.system.master_mem
  | insert a s ha ih =>
    rw [B.interOf_insert ha] at hsub ⊢
    have hs : B.system.mem (B.interOf s) := ih (hsub.trans Set.inter_subset_right)
    exact B.system.inter_mem (B.nbhd_mem a) hs hZ hsub

/-- A filter containing every `nbhd i` for `i ∈ u` contains `interOf u`. -/
theorem filter_mem_interOf (x : B.system.Element) {u : Finset ι}
    (hu : ∀ i ∈ u, x.mem (B.nbhd i)) : x.mem (B.interOf u) := by
  induction u using Finset.induction with
  | empty =>
    simpa [interOf_empty] using x.master_mem
  | insert a s ha ih =>
    rw [B.interOf_insert ha]
    exact x.inter_mem (hu a (Finset.mem_insert_self a s))
      (ih fun i hi => hu i (Finset.mem_insert_of_mem hi))

/-- **`neighborhoodSystem_to_infoSys`.** -/
def toInfoSys : InfoSys ι where
  bot := B.botIdx
  Con := {u | B.system.mem (B.interOf u)}
  Ent := fun u a => B.system.mem (B.interOf u) ∧ B.interOf u ⊆ B.nbhd a
  con_subset := by
    intro u v hu hv
    exact B.interOf_mem_of_lower_bound hu (B.interOf_anti hv)
  con_sing := by
    intro a
    simpa [Set.mem_setOf_eq, B.interOf_singleton] using B.nbhd_mem a
  ent_con := by
    intro u a ⟨hu, hsub⟩
    have h₁ : B.interOf (insert a u) ⊆ B.interOf u :=
      B.interOf_anti (Finset.subset_insert a u)
    have h₂ : B.interOf u ⊆ B.interOf (insert a u) := by
      intro x hx
      refine B.mem_interOf.mpr ⟨(B.mem_interOf.mp hx).1, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hsub hx
      · exact (B.mem_interOf.mp hx).2 i hi
    have heq : B.interOf (insert a u) = B.interOf u := Set.Subset.antisymm h₁ h₂
    simpa [Set.mem_setOf_eq, heq] using hu
  ent_bot := by
    intro u hu
    refine ⟨hu, ?_⟩
    intro x hx
    rw [B.botIdx_eq]
    exact B.interOf_subset_master u hx
  ent_refl := by
    intro u a hu ha
    exact ⟨hu, B.interOf_subset_nbhd ha⟩
  ent_trans := by
    intro u v c hv _hu hall ⟨_, hsub⟩
    refine ⟨hv, ?_⟩
    intro x hx
    have hxu : x ∈ B.interOf u :=
      B.mem_interOf.mpr ⟨B.interOf_subset_master v hx, fun i hi => (hall i hi).2 hx⟩
    exact hsub hxu

/-! ## Domain isomorphism -/

/-- Filter → InfoSys element. -/
def toElement (x : B.system.Element) : B.toInfoSys.Element where
  carrier := {i | x.mem (B.nbhd i)}
  consistent := fun Y hY => x.sub (B.filter_mem_interOf x hY)
  closed := by
    intro Y a hY ⟨_, hsub⟩
    exact x.up_mem (B.filter_mem_interOf x hY) (B.nbhd_mem a) hsub

/-- InfoSys element → filter (upward closure of its coded neighbourhoods). -/
def ofElement (e : B.toInfoSys.Element) : B.system.Element where
  mem X := B.system.mem X ∧ ∃ i ∈ e.carrier, B.nbhd i ⊆ X
  sub h := h.1
  master_mem := by
    refine ⟨B.system.master_mem, B.botIdx, ?_, by rw [B.botIdx_eq]⟩
    have hEnt : B.toInfoSys.Ent ∅ B.botIdx := B.toInfoSys.ent_bot (InfoSys.con_empty _)
    exact e.closed ∅ B.botIdx (fun _ h => False.elim (Finset.notMem_empty _ h)) hEnt
  inter_mem := by
    intro X Y ⟨hX, i, hi, hix⟩ ⟨hY, j, hj, hjy⟩
    have hCon : ({i, j} : Finset ι) ∈ B.toInfoSys.Con :=
      e.consistent {i, j} (by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hi
        · have : x = j := Finset.mem_singleton.mp hx
          exact this ▸ hj)
    have hInterMem : B.system.mem (B.interOf ({i, j} : Finset ι)) := hCon
    have hInterSub : B.interOf ({i, j} : Finset ι) ⊆ X ∩ Y := by
      intro x hx
      refine ⟨hix (B.interOf_subset_nbhd (by simp) hx),
        hjy (B.interOf_subset_nbhd (by simp) hx)⟩
    refine ⟨B.system.inter_mem hX hY hInterMem hInterSub, ?_⟩
    obtain ⟨k, hk⟩ := B.exhaustive hInterMem
    refine ⟨k, ?_, ?_⟩
    · have hEnt : B.toInfoSys.Ent {i, j} k := ⟨hInterMem, fun x hx => hk ▸ hx⟩
      exact e.closed {i, j} k (by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hi
        · exact Finset.mem_singleton.mp hx ▸ hj) hEnt
    · intro x hx
      exact hInterSub (hk ▸ hx)
  up_mem := by
    intro X Y ⟨hX, i, hi, hix⟩ hY hXY
    exact ⟨hY, i, hi, hix.trans hXY⟩

theorem toElement_carrier (x : B.system.Element) :
    (B.toElement x).carrier = {i | x.mem (B.nbhd i)} := rfl

theorem ofElement_mem (e : B.toInfoSys.Element) (X : Set α) :
    (B.ofElement e).mem X ↔ B.system.mem X ∧ ∃ i ∈ e.carrier, B.nbhd i ⊆ X :=
  Iff.rfl

theorem toElement_ofElement (e : B.toInfoSys.Element) :
    B.toElement (B.ofElement e) = e := by
  have hc : (B.toElement (B.ofElement e)).carrier = e.carrier := by
    ext i
    constructor
    · intro hi
      rcases (B.ofElement_mem e (B.nbhd i)).mp hi with ⟨_, j, hj, hsub⟩
      have hEnt : B.toInfoSys.Ent {j} i := by
        refine ⟨by simpa [B.interOf_singleton] using B.nbhd_mem j, ?_⟩
        simpa [B.interOf_singleton] using hsub
      exact e.closed {j} i (by
        intro x hx
        have : x = j := Finset.mem_singleton.mp hx
        exact this ▸ hj) hEnt
    · intro hi
      exact ⟨B.nbhd_mem i, i, hi, subset_rfl⟩
  rcases e with ⟨c, cons, clo⟩
  rcases hte : B.toElement (B.ofElement ⟨c, cons, clo⟩) with ⟨c', cons', clo'⟩
  have hc' : c' = c := by
    simpa [hte, toElement_carrier] using hc
  subst hc'
  rfl

theorem ofElement_toElement (x : B.system.Element) :
    B.ofElement (B.toElement x) = x := by
  refine NeighborhoodSystem.Element.ext (V := B.system) fun X => ?_
  constructor
  · intro ⟨hX, i, hi, hsub⟩
    exact x.up_mem hi hX hsub
  · intro hX
    obtain ⟨i, rfl⟩ := B.exhaustive (x.sub hX)
    exact ⟨x.sub hX, i, hX, subset_rfl⟩

/-- Order isomorphism between the neighbourhood-system domain and the induced
information-system domain. -/
def domainOrderIso : B.system.Element ≃o B.toInfoSys.Element where
  toFun := B.toElement
  invFun := B.ofElement
  left_inv := B.ofElement_toElement
  right_inv := B.toElement_ofElement
  map_rel_iff' := by
    intro x y
    constructor
    · intro h X hX
      obtain ⟨i, rfl⟩ := B.exhaustive (x.sub hX)
      have hi : i ∈ (B.toElement x).carrier := hX
      have hi' : i ∈ (B.toElement y).carrier := h hi
      exact y.up_mem hi' (x.sub hX) subset_rfl
    · intro h i hi
      exact h (B.nbhd i) hi

end NbhdBasis

/-- Blueprint name: neighbourhood system (with decidable basis) → information system. -/
abbrev neighborhoodSystem_to_infoSys {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α) :
    InfoSys ι :=
  B.toInfoSys

end ScottModels

-- Bridge — ScottModels.InfoSysToNeighborhood (from ScottModels/InfoSysToNeighborhood.lean)

/-!
# Information systems → neighbourhood systems (1982 → 1980)

Scott (1982, §4): for `u ∈ Con`, the basic open
`[u] = { x ∈ |A| | u ⊆ x }` yields a neighbourhood system on the domain `|A|`
whose filters recover the original elements. This is the converse direction to
`NeighborhoodToInfoSys`.
-/

namespace ScottModels

open Scott1980.Neighborhood
open Scott1982
open Scott1982.Constructive
open Scott1982.InfoSys

namespace InfoSysToNeighborhood

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem basicOpen_empty : A.basicOpen (∅ : Finset α) = (Set.univ : Set A.Element) := by
  ext x
  constructor
  · intro; trivial
  · intro _ a ha
    exact False.elim (Finset.notMem_empty a (Finset.mem_coe.1 ha))

theorem mem_basicOpen_singleton {a : α} {x : A.Element} :
    x ∈ A.basicOpen ({a} : Finset α) ↔ a ∈ x.carrier := by
  constructor
  · intro h
    exact h (Finset.mem_coe.2 (Finset.mem_singleton_self a))
  · intro ha b hb
    have hb' : b = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
    exact hb' ▸ ha

theorem funion_singleton_eq_insert (a : α) (s : Finset α) :
    ({a} : Finset α) ∪' s = insert a s := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp h))
    · exact Finset.mem_insert_of_mem h
  · intro hx
    rcases Finset.mem_insert.mp hx with h | h
    · exact mem_funion.mpr (Or.inl (h ▸ Finset.mem_singleton_self a))
    · exact mem_funion.mpr (Or.inr h)

theorem basicOpen_singleton_inter (a : α) (s : Finset α) :
    A.basicOpen ({a} : Finset α) ∩ A.basicOpen s = A.basicOpen (insert a s) := by
  rw [basicOpen_inter A, funion_singleton_eq_insert]

theorem ent_of_basicOpen_subset {u w : Finset α} (hw : w ∈ A.Con)
    (hsub : A.basicOpen w ⊆ A.basicOpen u) {a : α} (ha : a ∈ u) : A.Ent w a := by
  have : A.closure w hw ∈ A.basicOpen w := subset_closure A hw
  have hU : A.closure w hw ∈ A.basicOpen u := hsub this
  exact hU (Finset.mem_coe.2 ha)

theorem con_of_basicOpen_subset {u w : Finset α} (hw : w ∈ A.Con)
    (hsub : A.basicOpen w ⊆ A.basicOpen u) : u ∈ A.Con := by
  have hEnt : A.EntSet w u := fun a ha => ent_of_basicOpen_subset A hw hsub ha
  exact A.con_subset (proposition_2_3_ii A hw hEnt) (subset_funion_right _ _)

/-- **`infoSys_to_neighborhoodSystem`.** -/
def toNeighborhoodSystem : NeighborhoodSystem A.Element where
  mem X := ∃ u, u ∈ A.Con ∧ X = A.basicOpen u
  master := Set.univ
  master_nonempty := ⟨A.closure ∅ A.con_empty, Set.mem_univ _⟩
  master_mem := ⟨∅, A.con_empty, (basicOpen_empty A).symm⟩
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    obtain ⟨u, hu, rfl⟩ := hX
    obtain ⟨v, hv, rfl⟩ := hY
    obtain ⟨w, hw, rfl⟩ := hZ
    have hsub : A.basicOpen w ⊆ A.basicOpen (u ∪' v) := by
      intro x hx
      have hx' : x ∈ A.basicOpen u ∩ A.basicOpen v := hZsub hx
      rwa [basicOpen_inter A] at hx'
    have huv : u ∪' v ∈ A.Con := con_of_basicOpen_subset A hw hsub
    exact ⟨u ∪' v, huv, basicOpen_inter A u v⟩
  sub_master := fun {_} _ => Set.subset_univ _

theorem mem_basicOpen_of_singletons (f : (toNeighborhoodSystem A).Element) {Y : Finset α}
    (hY : ∀ a ∈ Y, f.mem (A.basicOpen ({a} : Finset α))) :
    f.mem (A.basicOpen Y) := by
  induction Y using Finset.induction with
  | empty =>
    rw [basicOpen_empty]
    have hmaster : (toNeighborhoodSystem A).master = (Set.univ : Set A.Element) := rfl
    rw [← hmaster]
    exact f.master_mem
  | insert a s _ha ih =>
    have hA := hY a (Finset.mem_insert_self a s)
    have hSm := ih fun i hi => hY i (Finset.mem_insert_of_mem hi)
    simpa [basicOpen_singleton_inter A a s] using f.inter_mem hA hSm

def toFilter (x : A.Element) : (toNeighborhoodSystem A).Element where
  mem U := ∃ u, u ∈ A.Con ∧ U = A.basicOpen u ∧ ↑u ⊆ x.carrier
  sub := by
    intro U h
    obtain ⟨u, hu, rfl, _⟩ := h
    exact ⟨u, hu, rfl⟩
  master_mem := ⟨∅, A.con_empty, (basicOpen_empty A).symm, by
    intro a ha
    exact False.elim (Finset.notMem_empty a (Finset.mem_coe.1 ha))⟩
  inter_mem := by
    intro U V hU hV
    obtain ⟨u, hu, rfl, huX⟩ := hU
    obtain ⟨v, hv, rfl, hvX⟩ := hV
    refine ⟨u ∪' v, ?_, basicOpen_inter A u v, ?_⟩
    · have hsub : ↑(u ∪' v) ⊆ x.carrier := by
        intro a ha
        rcases mem_funion.mp (Finset.mem_coe.1 ha) with h | h
        · exact huX (Finset.mem_coe.2 h)
        · exact hvX (Finset.mem_coe.2 h)
      exact x.consistent (u ∪' v) hsub
    · intro a ha
      rcases mem_funion.mp (Finset.mem_coe.1 ha) with h | h
      · exact huX (Finset.mem_coe.2 h)
      · exact hvX (Finset.mem_coe.2 h)
  up_mem := by
    intro U V hU hV hUV
    obtain ⟨u, hu, rfl, huX⟩ := hU
    obtain ⟨v, hv, rfl⟩ := hV
    refine ⟨v, hv, rfl, ?_⟩
    intro a ha
    exact x.closed u a huX (ent_of_basicOpen_subset A hu hUV ha)

def ofFilter (f : (toNeighborhoodSystem A).Element) : A.Element where
  carrier := {a | f.mem (A.basicOpen ({a} : Finset α))}
  consistent := by
    intro Y hY
    have hmem : f.mem (A.basicOpen Y) :=
      mem_basicOpen_of_singletons A f fun a ha => hY (Finset.mem_coe.2 ha)
    obtain ⟨u, hu, heq⟩ := f.sub hmem
    have hsub : A.basicOpen u ⊆ A.basicOpen Y := by
      intro x hx; exact heq ▸ hx
    exact con_of_basicOpen_subset A hu hsub
  closed := by
    intro Y b hY hEnt
    have hmemY : f.mem (A.basicOpen Y) :=
      mem_basicOpen_of_singletons A f fun c hc => hY (Finset.mem_coe.2 hc)
    have hsub : A.basicOpen Y ⊆ A.basicOpen ({b} : Finset α) := by
      intro x hx c hc
      have eqcb : c = b := Finset.mem_singleton.mp (Finset.mem_coe.1 hc)
      rw [eqcb]
      exact x.closed Y b hx hEnt
    exact f.up_mem hmemY ⟨({b} : Finset α), A.con_sing b, rfl⟩ hsub

theorem mem_basicOpen_iff (f : (toNeighborhoodSystem A).Element) {u : Finset α}
    (_hu : u ∈ A.Con) :
    f.mem (A.basicOpen u) ↔ ↑u ⊆ (ofFilter A f).carrier := by
  constructor
  · intro h a ha
    have hsub : A.basicOpen u ⊆ A.basicOpen ({a} : Finset α) := by
      intro x hx c hc
      have hc' : c = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hc)
      subst hc'
      exact hx (Finset.mem_coe.2 ha)
    exact f.up_mem h ⟨({a} : Finset α), A.con_sing a, rfl⟩ hsub
  · intro hsub
    exact mem_basicOpen_of_singletons A f fun a ha => hsub (Finset.mem_coe.2 ha)

theorem toFilter_ofFilter (f : (toNeighborhoodSystem A).Element) :
    toFilter A (ofFilter A f) = f := by
  refine NeighborhoodSystem.Element.ext (V := toNeighborhoodSystem A) fun U => ?_
  constructor
  · intro h
    obtain ⟨u, hu, hU, hsub⟩ := h
    subst hU
    exact (mem_basicOpen_iff A f hu).mpr hsub
  · intro hU
    obtain ⟨u, hu, heq⟩ := f.sub hU
    subst heq
    exact ⟨u, hu, rfl, (mem_basicOpen_iff A f hu).mp hU⟩

theorem ofFilter_toFilter (x : A.Element) : ofFilter A (toFilter A x) = x := by
  have hc : (ofFilter A (toFilter A x)).carrier = x.carrier := by
    ext a
    constructor
    · intro ha
      obtain ⟨u, hu, heq, hsub⟩ := ha
      have huA : A.closure u hu ∈ A.basicOpen u := subset_closure A hu
      have hsing : A.closure u hu ∈ A.basicOpen ({a} : Finset α) := by
        rw [heq]; exact huA
      have ha' : a ∈ (A.closure u hu).carrier := (mem_basicOpen_singleton A).1 hsing
      exact x.closed u a hsub ha'
    · intro ha
      refine ⟨({a} : Finset α), A.con_sing a, rfl, ?_⟩
      intro c hc
      have hc' : c = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hc)
      exact hc' ▸ ha
  rcases x with ⟨c, cons, clo⟩
  rcases hte : ofFilter A (toFilter A ⟨c, cons, clo⟩) with ⟨c', cons', clo'⟩
  have hc' : c' = c := by simpa [hte] using hc
  subst hc'
  rfl

def domainOrderIso : A.Element ≃o (toNeighborhoodSystem A).Element where
  toFun := toFilter A
  invFun := ofFilter A
  left_inv := ofFilter_toFilter A
  right_inv := toFilter_ofFilter A
  map_rel_iff' := by
    intro x y
    constructor
    · intro h a ha
      have hx : (toFilter A x).mem (A.basicOpen ({a} : Finset α)) :=
        ⟨({a} : Finset α), A.con_sing a, rfl, by
          intro c hc
          have hc' : c = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hc)
          exact hc' ▸ ha⟩
      have hy : (toFilter A y).mem (A.basicOpen ({a} : Finset α)) := h _ hx
      obtain ⟨u, hu, heq, hsub⟩ := hy
      have huA : A.closure u hu ∈ A.basicOpen u := subset_closure A hu
      have hsing : A.closure u hu ∈ A.basicOpen ({a} : Finset α) := by
        rw [heq]; exact huA
      have ha' : a ∈ (A.closure u hu).carrier := (mem_basicOpen_singleton A).1 hsing
      exact y.closed u a hsub ha'
    · intro h U hU
      obtain ⟨u, hu, hUeq, huX⟩ := hU
      subst hUeq
      exact ⟨u, hu, rfl, fun a ha => h (huX ha)⟩

end InfoSysToNeighborhood

/-- Blueprint-facing name for the 1982 → 1980 basic-open neighbourhood system. -/
abbrev infoSys_to_neighborhoodSystem {α : Type*} [DecidableEq α] (A : InfoSys α) :
    NeighborhoodSystem A.Element :=
  InfoSysToNeighborhood.toNeighborhoodSystem A

end ScottModels

-- Bridge — ScottModels.ContinuousLatticeToNeighborhood (from ScottModels/ContinuousLatticeToNeighborhood.lean)

/-!
# Continuous lattices → neighbourhood systems (1972 → 1980)

For a continuous lattice `D`, Scott’s way-below neighbourhoods
`↟a = { z | a ≪ z }` form a `NeighborhoodSystem` on token set `D`.

Arbitrary filters need not be principal (`{ ↟a | a ≤ x }` is a filter with
`ofFilter = x` but properly contains `toFilter x`). The correct domain is the
**round** filters: `↟a ∈ f` implies `∃ b, a ≪ b ∧ ↟b ∈ f`. Under
`IsContinuousLattice`, `D ≃o` round filters via `toFilter` / `ofFilter`.
-/

namespace ScottModels

open Scott1972.ContinuousLattice
open Scott1980.Neighborhood
open scoped Scott1972.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

/-- `↟a = { z | a ≪ z }`. -/
def wayBelowUp (a : D) : Set D := {z | a ≪ z}

theorem wayBelowUp_bot : wayBelowUp (⊥ : D) = (Set.univ : Set D) := by
  ext z
  exact ⟨fun _ => trivial, fun _ => bot_wayBelow z⟩

theorem wayBelowUp_inter (a b : D) :
    wayBelowUp a ∩ wayBelowUp b = wayBelowUp (a ⊔ b) := by
  ext z
  constructor
  · exact fun ⟨ha, hb⟩ => WayBelow.sup ha hb
  · intro h
    exact ⟨WayBelow.le_trans le_sup_left h, WayBelow.le_trans le_sup_right h⟩

theorem wayBelowUp_anti {a b : D} (hab : a ≤ b) :
    wayBelowUp b ⊆ wayBelowUp a :=
  fun _ h => WayBelow.le_trans hab h

/-- Neighbourhood system of all `↟a`. -/
def toNeighborhoodSystem : NeighborhoodSystem D where
  mem X := ∃ a : D, X = wayBelowUp a
  master := Set.univ
  master_nonempty := ⟨⊥, Set.mem_univ _⟩
  master_mem := ⟨⊥, wayBelowUp_bot.symm⟩
  inter_mem := by
    intro X Y _Z hX hY _hZ _hZsub
    obtain ⟨a, rfl⟩ := hX
    obtain ⟨b, rfl⟩ := hY
    exact ⟨a ⊔ b, wayBelowUp_inter a b⟩
  sub_master := fun {_} _ => Set.subset_univ _

/-- Filter of the `↟`-neighbourhood system on `D`. -/
abbrev Filter : Type _ :=
  (toNeighborhoodSystem : NeighborhoodSystem D).Element

/-- Principal filter of `↟`-neighbourhoods at `x`. -/
def toFilter (x : D) : Filter (D := D) where
  mem U := ∃ a : D, U = wayBelowUp a ∧ a ≪ x
  sub := by
    intro U h
    obtain ⟨a, ⟨rfl, _⟩⟩ := h
    exact ⟨a, rfl⟩
  master_mem := ⟨⊥, wayBelowUp_bot.symm, bot_wayBelow x⟩
  inter_mem := by
    intro U V hU hV
    obtain ⟨a, ⟨rfl, ha⟩⟩ := hU
    obtain ⟨b, ⟨rfl, hb⟩⟩ := hV
    exact ⟨a ⊔ b, ⟨wayBelowUp_inter a b, WayBelow.sup ha hb⟩⟩
  up_mem := by
    intro U V hU hV hUV
    obtain ⟨a, ⟨rfl, ha⟩⟩ := hU
    obtain ⟨b, rfl⟩ := hV
    exact ⟨b, ⟨rfl, hUV ha⟩⟩

theorem toFilter_mono {x y : D} (hxy : x ≤ y) : toFilter x ≤ toFilter y := by
  intro U hU
  obtain ⟨a, ⟨rfl, ha⟩⟩ := hU
  exact ⟨a, ⟨rfl, ha.trans_le hxy⟩⟩

theorem mem_wayBelowUp_toFilter {x a : D} :
    (toFilter x).mem (wayBelowUp a) ↔ a ≪ x := by
  constructor
  · intro h
    obtain ⟨b, ⟨heq, hb⟩⟩ := h
    have : x ∈ wayBelowUp b := hb
    rwa [← heq] at this
  · intro ha
    exact ⟨a, ⟨rfl, ha⟩⟩

/-- Roundness: `↟a ∈ f` is witnessed by a finer code `b` with `a ≪ b`. -/
def IsRound (f : Filter (D := D)) : Prop :=
  ∀ {a : D}, f.mem (wayBelowUp a) → ∃ b : D, a ≪ b ∧ f.mem (wayBelowUp b)

/-- Codes whose `↟`-neighbourhoods lie in the filter. -/
def codes (f : Filter (D := D)) : Set D :=
  {a : D | f.mem (wayBelowUp a)}

theorem mem_codes_iff {f : Filter (D := D)} {a : D} :
    a ∈ codes f ↔ f.mem (wayBelowUp a) :=
  Iff.rfl

theorem bot_mem_codes (f : Filter (D := D)) : (⊥ : D) ∈ codes f := by
  have : f.mem (wayBelowUp (⊥ : D)) := by
    rw [wayBelowUp_bot]
    exact f.master_mem
  exact this

theorem codes_nonempty (f : Filter (D := D)) : (codes f).Nonempty :=
  ⟨⊥, bot_mem_codes f⟩

theorem codes_directed (f : Filter (D := D)) : DirectedOn (· ≤ ·) (codes f) := by
  intro a ha b hb
  refine ⟨a ⊔ b, ?_, le_sup_left, le_sup_right⟩
  have : f.mem (wayBelowUp a ∩ wayBelowUp b) := f.inter_mem ha hb
  rwa [wayBelowUp_inter] at this

theorem codes_lower (f : Filter (D := D)) {a b : D} (hba : b ≤ a)
    (ha : a ∈ codes f) : b ∈ codes f :=
  f.up_mem ha ⟨b, rfl⟩ (wayBelowUp_anti hba)

/-- Retraction: `⊔` of codes present in the filter. -/
noncomputable def ofFilter (f : Filter (D := D)) : D :=
  sSup (codes f)

theorem mem_wayBelowUp_ofFilter_of_round {f : Filter (D := D)} (hr : IsRound f) {a : D} :
    f.mem (wayBelowUp a) ↔ a ≪ ofFilter f := by
  constructor
  · intro ha
    obtain ⟨b, hab, hb⟩ := hr ha
    exact (wayBelow_sSup_iff (codes_nonempty f) (codes_directed f)).2 ⟨b, hb, hab⟩
  · intro ha
    obtain ⟨b, hbS, hab⟩ := (wayBelow_sSup_iff (codes_nonempty f) (codes_directed f)).1 ha
    exact f.up_mem hbS ⟨a, rfl⟩ (wayBelowUp_anti hab.le)

theorem toFilter_ofFilter {f : Filter (D := D)} (hr : IsRound f) :
    toFilter (ofFilter f) = f := by
  refine NeighborhoodSystem.Element.ext (V := toNeighborhoodSystem) fun U => ?_
  constructor
  · intro hU
    obtain ⟨a, ⟨rfl, ha⟩⟩ := hU
    exact (mem_wayBelowUp_ofFilter_of_round hr).2 ha
  · intro hU
    obtain ⟨a, rfl⟩ := f.sub hU
    refine ⟨a, ⟨rfl, ?_⟩⟩
    exact (mem_wayBelowUp_ofFilter_of_round hr).1 hU

section Continuous

variable (hD : IsContinuousLattice D)
include hD

theorem toFilter_isRound (x : D) : IsRound (toFilter x) := by
  intro a ha
  have ha' : a ≪ x := mem_wayBelowUp_toFilter.mp ha
  obtain ⟨b, hab, hbx⟩ := wayBelow_interpolate hD ha'
  exact ⟨b, hab, mem_wayBelowUp_toFilter.mpr hbx⟩

theorem ofFilter_toFilter (x : D) : ofFilter (toFilter x) = x := by
  have hset : codes (toFilter x) = {a : D | a ≪ x} := by
    ext a
    exact mem_wayBelowUp_toFilter
  change sSup (codes (toFilter x)) = x
  rw [hset, hD.sSup_wayBelow x]

/-- Round filters of the `↟`-system. -/
abbrev RoundFilter : Type _ :=
  { f : Filter (D := D) // IsRound f }

/-- Order-isomorphism: continuous lattice ↔ round `↟`-filters. -/
noncomputable def domainOrderIso : D ≃o RoundFilter (D := D) where
  toFun x := ⟨toFilter x, toFilter_isRound hD x⟩
  invFun f := ofFilter (D := D) f.1
  left_inv x := ofFilter_toFilter hD x
  right_inv f := Subtype.ext (toFilter_ofFilter f.2)
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      have : ofFilter (toFilter x) ≤ ofFilter (toFilter y) := by
        refine sSup_le fun a ha => ?_
        have ha' : a ≪ x := mem_wayBelowUp_toFilter.mp ha
        exact le_sSup (h (wayBelowUp a) ⟨a, ⟨rfl, ha'⟩⟩)
      simpa [ofFilter_toFilter hD] using this
    · intro hxy
      exact toFilter_mono hxy

/-- Order-embedding into all filters (forgets roundness). -/
noncomputable def domainEmbedding :
    D ↪o Filter (D := D) where
  toFun := toFilter
  inj' := by
    intro x y h
    rw [← ofFilter_toFilter hD x, ← ofFilter_toFilter hD y, h]
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      have : ofFilter (toFilter x) ≤ ofFilter (toFilter y) := by
        refine sSup_le fun a ha => ?_
        have ha' : a ≪ x := mem_wayBelowUp_toFilter.mp ha
        exact le_sSup (h (wayBelowUp a) ⟨a, ⟨rfl, ha'⟩⟩)
      simpa [ofFilter_toFilter hD] using this
    · exact fun hxy => toFilter_mono hxy

end Continuous

end ContinuousLatticeToNeighborhood

/-- Blueprint name. -/
abbrev continuousLattice_to_neighborhoodSystem {D : Type*} [CompleteLattice D]
    (_hD : IsContinuousLattice D) : NeighborhoodSystem D :=
  ContinuousLatticeToNeighborhood.toNeighborhoodSystem

end ScottModels

-- Bridge — ScottModels.InfoSysToIdealCompletion (from ScottModels/InfoSysToIdealCompletion.lean)

/-!
# Information systems → ideal completion (1982 → algebraic dcpo)

The domain `|A|` of an information system is the **ideal completion** of its
poset of finite elements `ū` (closures of consistent finite token sets):
`A.Element ≃o Order.Ideal (FiniteElement A)`.

Packaging of Factoids 4.4–4.5 (`directedSup`, algebraicity, `compact_closure`).
-/

namespace ScottModels

open Scott1982
open Scott1982.Constructive
open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

/-- Finite (compact) elements: closures of consistent finite token sets. -/
abbrev FiniteElement : Type _ :=
  { x : A.Element // ∃ (u : Finset α) (hu : u ∈ A.Con), x = A.closure u hu }

theorem isFinite_bot :
    ∃ (u : Finset α) (hu : u ∈ A.Con), A.botElement = A.closure u hu :=
  ⟨∅, A.con_empty, A.botElement_eq_closure_empty⟩

/-- Bottom, as a finite element. -/
def botFinite : FiniteElement A := ⟨A.botElement, isFinite_bot A⟩

/-- Finite approximants of `x`, as `FiniteElement`s. -/
def finiteApproximants (x : A.Element) : Set (FiniteElement A) :=
  { y | (y : A.Element) ∈ A.finiteApproximants x }

theorem mem_finiteApproximants_of_le {x : A.Element} {y : FiniteElement A}
    (hle : (y : A.Element) ≤ x) : y ∈ finiteApproximants A x := by
  rcases y with ⟨yval, ⟨u, hu, rfl⟩⟩
  refine ⟨u, hu, ?_, rfl⟩
  intro a ha
  exact hle (A.subset_closure hu ha)

theorem le_of_mem_finiteApproximants {x : A.Element} {y : FiniteElement A}
    (hy : y ∈ finiteApproximants A x) : (y : A.Element) ≤ x := by
  obtain ⟨u, hu, huX, hyeq⟩ := hy
  exact hyeq ▸ A.closure_le_element x hu huX

theorem mem_finiteApproximants_iff {x : A.Element} {y : FiniteElement A} :
    y ∈ finiteApproximants A x ↔ (y : A.Element) ≤ x :=
  ⟨le_of_mem_finiteApproximants A, mem_finiteApproximants_of_le A⟩

theorem nonempty_finiteApproximants (x : A.Element) :
    (finiteApproximants A x).Nonempty :=
  ⟨botFinite A, mem_finiteApproximants_of_le A (A.botElement_le x)⟩

theorem directed_finiteApproximants (x : A.Element) :
    DirectedOn (· ≤ ·) (finiteApproximants A x) := by
  intro y₁ hy₁ y₂ hy₂
  obtain ⟨u, hu, huX, hy₁eq⟩ := hy₁
  obtain ⟨v, hv, hvX, hy₂eq⟩ := hy₂
  obtain ⟨w, hw, hwX, huw, hvw⟩ := A.closures_directed x hu hv huX hvX
  refine ⟨⟨A.closure w hw, ⟨w, hw, rfl⟩⟩, ⟨w, hw, hwX, rfl⟩, ?_, ?_⟩
  · -- y₁ ≤ closure w
    change (y₁ : A.Element) ≤ A.closure w hw
    exact hy₁eq ▸ huw
  · change (y₂ : A.Element) ≤ A.closure w hw
    exact hy₂eq ▸ hvw

theorem isLowerSet_finiteApproximants (x : A.Element) :
    IsLowerSet (finiteApproximants A x) := by
  intro y₁ y₂ hle hy₂
  exact mem_finiteApproximants_of_le A (le_trans hle (le_of_mem_finiteApproximants A hy₂))

/-- Ideal of finite approximants of `x`. -/
def toIdeal (x : A.Element) : Ideal (FiniteElement A) where
  carrier := finiteApproximants A x
  lower' := isLowerSet_finiteApproximants A x
  nonempty' := nonempty_finiteApproximants A x
  directed' := directed_finiteApproximants A x

theorem mem_toIdeal_iff {x : A.Element} {y : FiniteElement A} :
    y ∈ toIdeal A x ↔ (y : A.Element) ≤ x :=
  mem_finiteApproximants_iff A

/-- Underlying set of elements of an ideal of finite elements. -/
def idealCarrier (I : Ideal (FiniteElement A)) : Set A.Element :=
  Subtype.val '' (I : Set (FiniteElement A))

theorem nonempty_idealCarrier (I : Ideal (FiniteElement A)) :
    (idealCarrier A I).Nonempty := by
  obtain ⟨y, hy⟩ := I.nonempty
  exact ⟨y, y, hy, rfl⟩

theorem directed_idealCarrier (I : Ideal (FiniteElement A)) :
    A.IsDirected (idealCarrier A I) := by
  intro x y hx hy
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  obtain ⟨z', hz', hxz, hyz⟩ := I.directed x' hx' y' hy'
  exact ⟨z', ⟨z', hz', rfl⟩, hxz, hyz⟩

/-- Retraction: directed supremum of the finite elements in the ideal. -/
noncomputable def ofIdeal (I : Ideal (FiniteElement A)) : A.Element :=
  A.directedSup (idealCarrier A I) (nonempty_idealCarrier A I) (directed_idealCarrier A I)

theorem le_ofIdeal_of_mem {I : Ideal (FiniteElement A)} {y : FiniteElement A}
    (hy : y ∈ I) : (y : A.Element) ≤ ofIdeal A I :=
  A.le_directedSup _ _ _ ⟨y, hy, rfl⟩

theorem ofIdeal_toIdeal (x : A.Element) : ofIdeal A (toIdeal A x) = x := by
  -- idealCarrier (toIdeal x) = finiteApproximants as Elements = A.finiteApproximants x
  have hset : idealCarrier A (toIdeal A x) = A.finiteApproximants x := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact hy
    · intro hz
      refine ⟨⟨z, ?_⟩, hz, rfl⟩
      obtain ⟨u, hu, _, rfl⟩ := hz
      exact ⟨u, hu, rfl⟩
  -- directedSup of that set is x
  change A.directedSup (idealCarrier A (toIdeal A x)) _ _ = x
  simp_rw [hset]
  exact (A.eq_directedSup_finiteApproximants x).symm

theorem toIdeal_ofIdeal (I : Ideal (FiniteElement A)) : toIdeal A (ofIdeal A I) = I := by
  refine Ideal.ext ?_
  ext y
  constructor
  · intro hy
    have hle : (y : A.Element) ≤ ofIdeal A I := le_of_mem_finiteApproximants A hy
    rcases y with ⟨yval, ⟨u, hu, rfl⟩⟩
    obtain ⟨z, hz, hcle⟩ :=
      A.compact_closure (idealCarrier A I) (nonempty_idealCarrier A I)
        (directed_idealCarrier A I) hu hle
    obtain ⟨z', hz', rfl⟩ := hz
    exact I.lower hcle hz'
  · intro hy
    exact mem_finiteApproximants_of_le A (le_ofIdeal_of_mem A hy)

theorem toIdeal_mono {x y : A.Element} (hxy : x ≤ y) : toIdeal A x ≤ toIdeal A y := by
  intro z hz
  exact mem_finiteApproximants_of_le A
    (le_trans (le_of_mem_finiteApproximants A hz) hxy)

/-- Order isomorphism: domain elements ↔ ideals of finite elements. -/
noncomputable def domainOrderIso : A.Element ≃o Ideal (FiniteElement A) where
  toFun := toIdeal A
  invFun := ofIdeal A
  left_inv := ofIdeal_toIdeal A
  right_inv := toIdeal_ofIdeal A
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      -- x ≤ y from toIdeal x ≤ toIdeal y via algebraicity
      rw [← ofIdeal_toIdeal A x, ← ofIdeal_toIdeal A y]
      refine A.directedSup_le _ _ _ ?_
      intro z hz
      obtain ⟨z', hz', rfl⟩ := hz
      exact le_ofIdeal_of_mem A (h hz')
    · exact toIdeal_mono A

end InfoSysToIdealCompletion

/-- Blueprint name: `|A|` as the ideal completion of its finite elements. -/
noncomputable abbrev infoSys_to_idealCompletion {α : Type*} [DecidableEq α] (A : InfoSys α) :
    A.Element ≃o Ideal (InfoSysToIdealCompletion.FiniteElement A) :=
  InfoSysToIdealCompletion.domainOrderIso A

end ScottModels

-- Bridge — ScottModels.IdealCompletionToContinuousLattice (from ScottModels/IdealCompletionToContinuousLattice.lean)

/-!
# Algebraic complete lattices → continuous lattices (ideal-completion → 1972)

An **algebraic** complete lattice — every element is the directed supremum of the
compact elements below it — is a continuous lattice in Scott's sense
(`IsContinuousLattice`). Compact elements are way-below anything they lie under,
via Scott-openness of `Set.Ici k`.

This is the classical frontier of this article’s blueprint
(`idealCompletion_to_continuousLattice`): Scott's `≪` is topological.
-/

namespace ScottModels

open Scott1972.ContinuousLattice
open scoped Scott1972.ContinuousLattice

namespace IdealCompletionToContinuousLattice

variable {D : Type*} [CompleteLattice D]

/-- Order-theoretic compactness: inaccessible by nonempty directed suprema. -/
def IsCompactElement (k : D) : Prop :=
  ∀ ⦃S : Set D⦄, S.Nonempty → DirectedOn (· ≤ ·) S → k ≤ sSup S → ∃ s ∈ S, k ≤ s

/-- Compactness implies `Set.Ici k` is Scott-open. -/
theorem scottOpen_Ici_of_compact {k : D} (hk : IsCompactElement k) :
    ScottOpen (Set.Ici k) := by
  refine ⟨isUpperSet_Ici k, fun S hS hSdir hmem => ?_⟩
  obtain ⟨s, hsS, hks⟩ := hk hS hSdir (Set.mem_Ici.1 hmem)
  exact ⟨s, hsS, Set.mem_Ici.2 hks⟩

/-- Compact elements are way below anything above them. -/
theorem compact_wayBelow {k y : D} (hk : IsCompactElement k) (hky : k ≤ y) : k ≪ y :=
  ⟨Set.Ici k, scottOpen_Ici_of_compact hk, Set.mem_Ici.2 hky, subset_rfl⟩

/-- Algebraicity: every element is the directed lub of compact elements below it. -/
def IsAlgebraicLattice (D : Type*) [CompleteLattice D] : Prop :=
  ∀ y : D,
    let S := {x : D | IsCompactElement x ∧ x ≤ y}
    S.Nonempty ∧ DirectedOn (· ≤ ·) S ∧ sSup S = y

/-- **Blueprint:** algebraic complete lattice ⇒ continuous lattice (Scott Def. 2.3). -/
theorem isContinuousLattice_of_algebraic (hA : IsAlgebraicLattice D) :
    IsContinuousLattice D := by
  intro y
  obtain ⟨hne, hdir, hsup⟩ := hA y
  refine ⟨?_, fun z hz => ?_⟩
  · -- y is an upper bound of `{x | x ≪ y}`
    intro x hx
    exact hx.le
  · -- any upper bound of the way-belows is ≥ y
    -- every compact ≤ y is ≪ y, hence ≤ z
    have hle : sSup {x : D | IsCompactElement x ∧ x ≤ y} ≤ z := by
      refine sSup_le fun x hx => ?_
      exact hz (compact_wayBelow hx.1 hx.2)
    exact hsup ▸ hle

end IdealCompletionToContinuousLattice

/-- Blueprint name. -/
abbrev idealCompletion_to_continuousLattice {D : Type*} [CompleteLattice D]
    (hA : IdealCompletionToContinuousLattice.IsAlgebraicLattice D) :
    IsContinuousLattice D :=
  IdealCompletionToContinuousLattice.isContinuousLattice_of_algebraic hA

end ScottModels

-- Bridge — ScottModels.PresentationDomains (from ScottModels/PresentationDomains.lean)

/-!
# Presentation domain equivalences

## InfoSys / neighbourhood / ideal (constructive)

For any information system `A`:
`|A| ≃o` basic-open neighbourhood filters ≃o `Ideal (FiniteElement A)`.

Under a decidable `NbhdBasis`, the same triangle starts from `|𝒟|`.

## Continuous lattices (1972 corner)

Points of a continuous lattice `D` are **round** `↟`-filters, not arbitrary filters:
`D ≃o RoundFilter`. With `DecidableEq D`, the `↟`-system admits an `NbhdBasis`,
so round filters transport to a subtype of the induced InfoSys domain (and thence
into the ideal-completion triangle). The full (non-round) `|𝒟|` / `|A|` is properly
larger.
-/

namespace ScottModels

open Scott1982
open Scott1972.ContinuousLattice
open Scott1980.Neighborhood
open Order
open scoped Scott1972.ContinuousLattice
open ContinuousLatticeToNeighborhood

section InfoSysTriangle
variable {α : Type*} [DecidableEq α]

/-- Neighbourhood filters of `|A|` ↔ ideals of finite elements (via `|A|`). -/
noncomputable def neighborhood_ideal_iso (A : InfoSys α) :
    (InfoSysToNeighborhood.toNeighborhoodSystem A).Element ≃o
      Ideal (InfoSysToIdealCompletion.FiniteElement A) :=
  (InfoSysToNeighborhood.domainOrderIso A).symm.trans
    (InfoSysToIdealCompletion.domainOrderIso A)

variable {ι β : Type*} [DecidableEq ι]

/-- Under a decidable neighbourhood basis, `|𝒟|` ↔ InfoSys domain ↔ ideal completion. -/
noncomputable def nbhdBasis_ideal_iso (B : NbhdBasis ι β) :
    B.system.Element ≃o Ideal (InfoSysToIdealCompletion.FiniteElement B.toInfoSys) :=
  B.domainOrderIso.trans (InfoSysToIdealCompletion.domainOrderIso B.toInfoSys)

/-- Constructive 1980↔1982↔ideal triangle for InfoSys domains. -/
noncomputable abbrev presentation_domains_equiv_infoSys (A : InfoSys α) :=
  neighborhood_ideal_iso A

end InfoSysTriangle

/-! ## Continuous lattice presentations via round `↟`-filters -/

universe u
variable {D : Type u} [CompleteLattice D] [DecidableEq D]

/-- Decidable coding of the `↟`-neighbourhood system: tokens are elements of `D`. -/
def wayBelowNbhdBasis : NbhdBasis D D where
  system := toNeighborhoodSystem
  nbhd := wayBelowUp
  nbhd_mem := fun a => ⟨a, rfl⟩
  exhaustive := by
    intro X hX
    obtain ⟨a, rfl⟩ := hX
    exact ⟨a, rfl⟩
  botIdx := ⊥
  botIdx_eq := wayBelowUp_bot

theorem wayBelowNbhdBasis_system :
    (wayBelowNbhdBasis (D := D)).system = toNeighborhoodSystem :=
  rfl

/-- Roundness transported to InfoSys elements of the `↟`-basis. -/
def IsRoundInfoSysElement (e : (wayBelowNbhdBasis (D := D)).toInfoSys.Element) : Prop :=
  IsRound ((wayBelowNbhdBasis (D := D)).domainOrderIso.symm e)

abbrev RoundInfoSysElement : Type _ :=
  { e : (wayBelowNbhdBasis (D := D)).toInfoSys.Element // IsRoundInfoSysElement (D := D) e }

/-- Round `↟`-filters ↔ round elements of the coded InfoSys. -/
noncomputable def roundFilter_infoSys_iso :
    RoundFilter (D := D) ≃o RoundInfoSysElement (D := D) where
  toFun := fun f =>
    ⟨(wayBelowNbhdBasis (D := D)).domainOrderIso f.1, by
      let f' : (wayBelowNbhdBasis (D := D)).system.Element := f.1
      change IsRound ((wayBelowNbhdBasis (D := D)).domainOrderIso.symm
        ((wayBelowNbhdBasis (D := D)).domainOrderIso f'))
      rw [OrderIso.symm_apply_apply]
      exact f.2⟩
  invFun := fun e =>
    ⟨(wayBelowNbhdBasis (D := D)).domainOrderIso.symm e.1, e.2⟩
  left_inv := fun f => Subtype.ext <|
    (wayBelowNbhdBasis (D := D)).domainOrderIso.left_inv f.1
  right_inv := fun e => Subtype.ext <|
    (wayBelowNbhdBasis (D := D)).domainOrderIso.right_inv e.1
  map_rel_iff' := by
    intro f g
    exact (wayBelowNbhdBasis (D := D)).domainOrderIso.map_rel_iff

section Continuous

variable (hD : IsContinuousLattice D)
include hD

/-- **1972 ↔ round 1980:** continuous lattice ↔ round `↟`-filters. -/
noncomputable def continuousLattice_roundFilter_iso :
    D ≃o RoundFilter (D := D) :=
  ContinuousLatticeToNeighborhood.domainOrderIso hD

/-- **1972 ↔ round 1982:** continuous lattice ↔ round InfoSys elements of the `↟`-basis. -/
noncomputable def continuousLattice_roundInfoSys_iso :
    D ≃o RoundInfoSysElement (D := D) :=
  (continuousLattice_roundFilter_iso hD).trans roundFilter_infoSys_iso

/-- Round InfoSys elements ↔ ideals of finite elements that come from round InfoSys
elements (via the ideal-completion iso). -/
noncomputable def roundInfoSys_ideal_iso :
    RoundInfoSysElement (D := D) ≃o
      { I : Ideal (InfoSysToIdealCompletion.FiniteElement
          (wayBelowNbhdBasis (D := D)).toInfoSys) //
        IsRoundInfoSysElement (D := D)
          ((InfoSysToIdealCompletion.domainOrderIso
            (wayBelowNbhdBasis (D := D)).toInfoSys).symm I) } := by
  let A := (wayBelowNbhdBasis (D := D)).toInfoSys
  let ιE := InfoSysToIdealCompletion.domainOrderIso A
  refine {
    toFun := fun e => ⟨ιE e.1, by
      change IsRoundInfoSysElement (ιE.symm (ιE e.1))
      rw [OrderIso.symm_apply_apply]
      exact e.2⟩
    invFun := fun I => ⟨ιE.symm I.1, I.2⟩
    left_inv := fun e => Subtype.ext (ιE.left_inv e.1)
    right_inv := fun I => Subtype.ext (ιE.right_inv I.1)
    map_rel_iff' := by
      intro e₁ e₂
      exact ιE.map_rel_iff
  }

/-- **Blueprint:** three-presentation equivalence for continuous lattices.

`D ≃o RoundFilter ≃o RoundInfoSysElement`, with the `↟`-system’s `NbhdBasis`
supplying the 1980↔1982 coding. (Raw `|𝒟|` / full `|A|` remain larger.) -/
noncomputable def presentation_domains_equiv :
    D ≃o RoundInfoSysElement (D := D) :=
  continuousLattice_roundInfoSys_iso hD

/-- The three presentations determine the same domain (round corner). -/
theorem exists_presentation_domains_equiv :
    Nonempty (D ≃o RoundInfoSysElement (D := D)) :=
  ⟨presentation_domains_equiv hD⟩

/-- Extended form through ideal completion of finite elements of the `↟`-InfoSys. -/
noncomputable def presentation_domains_equiv_ideal :
    D ≃o
      { I : Ideal (InfoSysToIdealCompletion.FiniteElement
          (wayBelowNbhdBasis (D := D)).toInfoSys) //
        IsRoundInfoSysElement (D := D)
          ((InfoSysToIdealCompletion.domainOrderIso
            (wayBelowNbhdBasis (D := D)).toInfoSys).symm I) } :=
  (presentation_domains_equiv hD).trans (roundInfoSys_ideal_iso (D := D))

end Continuous

end ScottModels

-- Bridge — ScottModels.InfoSysConstructions (from ScottModels/InfoSysConstructions.lean)

/-!
# Construction equivalence — products, separated sums, and function spaces

* **Product:** `|A × B| ≃o |A| × |B|` via `pairElements` / projections (Prop 6.2).
* **Separated sum:** `|A + B| ≃o WithBot (|A| ⊕ |B|)` via `inl`/`inr` (Prop 6.4).
  Classification of sum elements uses classical case-split on token polarity
  (`Classical.choice` in the footprint).
* **Function space:** `|A → B| ≃o ApproximableMap A B` via Theorem 7.2
  `approxMap_toElement` / `element_toApproxMap`.

1972 counterpart: products of continuous lattices (`proposition_2_9_a`); function space
Thm 3.3 in the sibling package.
-/

namespace ScottModels

open Scott1982
open Scott1982.Constructive
open Scott1982.InfoSys
open Scott1982.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

/-- Split a product-domain element into its two projections. -/
def unpair (z : (productSystem A B).Element) : A.Element × B.Element :=
  ((fstMap A B).toElement z, (sndMap A B).toElement z)

theorem unpair_pairElements (x : A.Element) (y : B.Element) :
    unpair A B (pairElements A B x y) = (x, y) := by
  simp [unpair, fstMap_pairElements, sndMap_pairElements]

theorem pairElements_unpair (z : (productSystem A B).Element) :
    pairElements A B ((fstMap A B).toElement z) ((sndMap A B).toElement z) = z :=
  element_eq_of_fst_snd A B _ z (fstMap_pairElements A B _ _) (sndMap_pairElements A B _ _)

theorem pairElements_mono {x₁ x₂ : A.Element} {y₁ y₂ : B.Element}
    (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    pairElements A B x₁ y₁ ≤ pairElements A B x₂ y₂ := by
  intro p hp
  exact ⟨fun hbot => hx (hp.1 hbot), fun hbot => hy (hp.2 hbot)⟩

theorem unpair_mono {z₁ z₂ : (productSystem A B).Element} (hz : z₁ ≤ z₂) :
    unpair A B z₁ ≤ unpair A B z₂ := by
  constructor
  · exact (fstMap A B).toElement_mono hz
  · exact (sndMap A B).toElement_mono hz

/-- **Product domain iso (1982).** `|A × B| ≃o |A| × |B|`. -/
noncomputable def productDomainIso :
    A.Element × B.Element ≃o (productSystem A B).Element where
  toFun := fun p => pairElements A B p.1 p.2
  invFun := unpair A B
  left_inv := fun p => unpair_pairElements A B p.1 p.2
  right_inv := pairElements_unpair A B
  map_rel_iff' := by
    intro p q
    constructor
    · intro h
      change pairElements A B p.1 p.2 ≤ pairElements A B q.1 q.2 at h
      constructor
      · have hp := (fstMap A B).toElement_mono h
        rw [fstMap_pairElements A B p.1 p.2, fstMap_pairElements A B q.1 q.2] at hp
        exact hp
      · have hp := (sndMap A B).toElement_mono h
        rw [sndMap_pairElements A B p.1 p.2, sndMap_pairElements A B q.1 q.2] at hp
        exact hp
    · intro h
      exact pairElements_mono A B h.1 h.2

/-! ## Separated sum `|A + B| ≃o WithBot (|A| ⊕ |B|)` -/

private theorem InfoSysConstructions_rhtFinset_singleton_left (x : α) :
    rhtFinset ({SumToken.left x} : Finset (SumToken α β)) = ∅ := by
  ext y
  constructor
  · intro hy
    have : SumToken.right y ∈ ({SumToken.left x} : Finset _) := (mem_rhtFinset).1 hy
    exact False.elim (nomatch Finset.mem_singleton.mp this)
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

private theorem InfoSysConstructions_lftFinset_singleton_right (y : β) :
    lftFinset ({SumToken.right y} : Finset (SumToken α β)) = ∅ := by
  ext x
  constructor
  · intro hx
    have : SumToken.left x ∈ ({SumToken.right y} : Finset _) := (mem_lftFinset).1 hx
    exact False.elim (nomatch Finset.mem_singleton.mp this)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem left_bot_mem_inlMap_toElement (x : A.Element) :
    SumToken.left A.bot ∈ ((inlMap A B).toElement x).carrier := by
  refine ⟨{A.bot}, ?_, ?_⟩
  · intro a ha
    have : a = A.bot := Finset.mem_singleton.mp (Finset.mem_coe.1 ha)
    subst this
    exact factoid_3_2 A x
  · refine ⟨A.con_sing A.bot, ?_, InfoSysConstructions_rhtFinset_singleton_left (β := β) A.bot, ?_⟩
    · exact Or.inl ⟨by rw [lftFinset_singleton_left]; exact A.con_sing A.bot,
        InfoSysConstructions_rhtFinset_singleton_left (β := β) A.bot⟩
    · rw [lftFinset_singleton_left]
      exact proposition_2_3_iii A (A.con_sing A.bot)

theorem right_bot_mem_inrMap_toElement (y : B.Element) :
    SumToken.right B.bot ∈ ((inrMap A B).toElement y).carrier := by
  refine ⟨{B.bot}, ?_, ?_⟩
  · intro b hb
    have : b = B.bot := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
    subst this
    exact factoid_3_2 B y
  · refine ⟨B.con_sing B.bot, ?_, InfoSysConstructions_lftFinset_singleton_right (α := α) B.bot, ?_⟩
    · exact Or.inr ⟨InfoSysConstructions_lftFinset_singleton_right (α := α) B.bot,
        by rw [rhtFinset_singleton_right]; exact B.con_sing B.bot⟩
    · rw [rhtFinset_singleton_right]
      exact proposition_2_3_iii B (B.con_sing B.bot)

theorem sumElementLft_inlMap_toElement (x : A.Element) :
    sumElementLft A B ((inlMap A B).toElement x) A.bot
      (left_bot_mem_inlMap_toElement A B x) = x := by
  apply le_antisymm
  · intro a ha
    -- ha : left a ∈ inl(x)
    obtain ⟨u, hu, ⟨huCon, hSum, hr, hEnt⟩⟩ := ha
    have hEntA : A.Ent u a := by
      have : lftFinset ({SumToken.left a} : Finset (SumToken α β)) = {a} :=
        lftFinset_singleton_left a
      simpa [this] using hEnt a (Finset.mem_singleton_self a)
    exact x.closed u a hu hEntA
  · intro a ha
    change SumToken.left a ∈ ((inlMap A B).toElement x).carrier
    refine ⟨{a}, ?_, ?_⟩
    · intro b hb
      have : b = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
      subst this; exact ha
    · refine ⟨A.con_sing a, Or.inl ⟨by rw [lftFinset_singleton_left]; exact A.con_sing a,
        InfoSysConstructions_rhtFinset_singleton_left (β := β) a⟩, InfoSysConstructions_rhtFinset_singleton_left (β := β) a, ?_⟩
      rw [lftFinset_singleton_left]
      exact proposition_2_3_iii A (A.con_sing a)

theorem sumElementRht_inrMap_toElement (y : B.Element) :
    sumElementRht A B ((inrMap A B).toElement y) B.bot
      (right_bot_mem_inrMap_toElement A B y) = y := by
  apply le_antisymm
  · intro b hb
    obtain ⟨w, hw, ⟨hwCon, hSum, hl, hEnt⟩⟩ := hb
    have hEntB : B.Ent w b := by
      have : rhtFinset ({SumToken.right b} : Finset (SumToken α β)) = {b} :=
        rhtFinset_singleton_right b
      simpa [this] using hEnt b (Finset.mem_singleton_self b)
    exact y.closed w b hw hEntB
  · intro b hb
    change SumToken.right b ∈ ((inrMap A B).toElement y).carrier
    refine ⟨{b}, ?_, ?_⟩
    · intro c hc
      have : c = b := Finset.mem_singleton.mp (Finset.mem_coe.1 hc)
      subst this; exact hb
    · refine ⟨B.con_sing b, Or.inr ⟨InfoSysConstructions_lftFinset_singleton_right (α := α) b,
        by rw [rhtFinset_singleton_right]; exact B.con_sing b⟩,
        InfoSysConstructions_lftFinset_singleton_right (α := α) b, ?_⟩
      rw [rhtFinset_singleton_right]
      exact proposition_2_3_iii B (B.con_sing b)

theorem inlMap_toElement_injective :
    Function.Injective (inlMap A B).toElement := by
  intro x y h
  refine le_antisymm ?_ ?_
  · intro a ha
    have hx := sumElementLft_inlMap_toElement A B x
    have : SumToken.left a ∈ ((inlMap A B).toElement x).carrier := by
      rw [← hx] at ha; exact ha
    rw [h] at this
    have hy := sumElementLft_inlMap_toElement A B y
    have : a ∈ (sumElementLft A B ((inlMap A B).toElement y) A.bot
        (left_bot_mem_inlMap_toElement A B y)).carrier := this
    rwa [hy] at this
  · intro a ha
    have hy := sumElementLft_inlMap_toElement A B y
    have : SumToken.left a ∈ ((inlMap A B).toElement y).carrier := by
      rw [← hy] at ha; exact ha
    rw [← h] at this
    have hx := sumElementLft_inlMap_toElement A B x
    have : a ∈ (sumElementLft A B ((inlMap A B).toElement x) A.bot
        (left_bot_mem_inlMap_toElement A B x)).carrier := this
    rwa [hx] at this

theorem inrMap_toElement_injective :
    Function.Injective (inrMap A B).toElement := by
  intro x y h
  refine le_antisymm ?_ ?_
  · intro b hb
    have hx := sumElementRht_inrMap_toElement A B x
    have : SumToken.right b ∈ ((inrMap A B).toElement x).carrier := by
      rw [← hx] at hb; exact hb
    rw [h] at this
    have hy := sumElementRht_inrMap_toElement A B y
    have : b ∈ (sumElementRht A B ((inrMap A B).toElement y) B.bot
        (right_bot_mem_inrMap_toElement A B y)).carrier := this
    rwa [hy] at this
  · intro b hb
    have hy := sumElementRht_inrMap_toElement A B y
    have : SumToken.right b ∈ ((inrMap A B).toElement y).carrier := by
      rw [← hy] at hb; exact hb
    rw [← h] at this
    have hx := sumElementRht_inrMap_toElement A B x
    have : b ∈ (sumElementRht A B ((inrMap A B).toElement x) B.bot
        (right_bot_mem_inrMap_toElement A B x)).carrier := this
    rwa [hx] at this

/-- Every sum element is ⊥, a pure left copy, or a pure right copy. Classical. -/
theorem sum_element_trichotomy (z : (sumSystem A B).Element) :
    z = (sumSystem A B).botElement ∨
      (∃ x : A.Element, z = (inlMap A B).toElement x) ∨
        (∃ y : B.Element, z = (inrMap A B).toElement y) := by
  classical
  by_cases hL : ∃ x : α, SumToken.left x ∈ z.carrier
  · obtain ⟨x0, hx0⟩ := hL
    exact Or.inr (Or.inl ⟨sumElementLft A B z x0 hx0, (inlMap_toElement_sumElementLft A B z x0 hx0).symm⟩)
  · by_cases hR : ∃ y : β, SumToken.right y ∈ z.carrier
    · obtain ⟨y0, hy0⟩ := hR
      exact Or.inr (Or.inr ⟨sumElementRht A B z y0 hy0, (inrMap_toElement_sumElementRht A B z y0 hy0).symm⟩)
    · exact Or.inl (eq_botElement_of_no_injections A B z
        (fun x hx => hL ⟨x, hx⟩) (fun y hy => hR ⟨y, hy⟩))

/-- Assemble a sum-domain element from a separated-sum code. -/
def assembleSum : WithBot (A.Element ⊕ B.Element) → (sumSystem A B).Element
  | ⊥ => (sumSystem A B).botElement
  | some (.inl x) => (inlMap A B).toElement x
  | some (.inr y) => (inrMap A B).toElement y

/-- Every sum-domain element has a separated-sum code. -/
private theorem InfoSysConstructions_exists_assembleSum_eq (z : (sumSystem A B).Element) :
    ∃ w : WithBot (A.Element ⊕ B.Element), assembleSum A B w = z := by
  rcases sum_element_trichotomy A B z with hbot | ⟨x, hx⟩ | ⟨y, hy⟩
  · exact ⟨⊥, hbot.symm⟩
  · exact ⟨some (.inl x), hx.symm⟩
  · exact ⟨some (.inr y), hy.symm⟩

/-- Classify a sum-domain element as `WithBot (|A| ⊕ |B|)`. Classical. -/
noncomputable def classifySum (z : (sumSystem A B).Element) :
    WithBot (A.Element ⊕ B.Element) :=
  Classical.choose (InfoSysConstructions_exists_assembleSum_eq A B z)

theorem assembleSum_classifySum (z : (sumSystem A B).Element) :
    assembleSum A B (classifySum A B z) = z :=
  Classical.choose_spec (InfoSysConstructions_exists_assembleSum_eq A B z)

theorem not_left_mem_sum_botElement {x : α} :
    SumToken.left x ∉ ((sumSystem A B).botElement).carrier := by
  intro hx
  have hEnt : (sumSystem A B).Ent {sumBot} (.left x) := hx
  -- Ent {bot} (left x) requires lftFinset {bot} ≠ ∅
  rcases hEnt with ⟨_, ⟨hne, _⟩⟩
  exact hne lftFinset_singleton_bot

theorem not_right_mem_sum_botElement {y : β} :
    SumToken.right y ∉ ((sumSystem A B).botElement).carrier := by
  intro hy
  have hEnt : (sumSystem A B).Ent {sumBot} (.right y) := hy
  rcases hEnt with ⟨_, ⟨hne, _⟩⟩
  exact hne rhtFinset_singleton_bot

theorem sumElementLft_eq {z : (sumSystem A B).Element} {x0 x1 : α}
    (hx0 : SumToken.left x0 ∈ z.carrier) (hx1 : SumToken.left x1 ∈ z.carrier) :
    sumElementLft A B z x0 hx0 = sumElementLft A B z x1 hx1 := by
  refine le_antisymm ?_ ?_ <;> intro a ha <;> exact ha

theorem sumElementRht_eq {z : (sumSystem A B).Element} {y0 y1 : β}
    (hy0 : SumToken.right y0 ∈ z.carrier) (hy1 : SumToken.right y1 ∈ z.carrier) :
    sumElementRht A B z y0 hy0 = sumElementRht A B z y1 hy1 := by
  refine le_antisymm ?_ ?_ <;> intro b hb <;> exact hb

theorem assembleSum_injective :
    Function.Injective (assembleSum A B) := by
  intro w₁ w₂ h
  cases w₁ with
  | bot =>
    cases w₂ with
    | bot => rfl
    | coe s₂ =>
      cases s₂ with
      | inl x =>
        change (sumSystem A B).botElement = (inlMap A B).toElement x at h
        have hx := left_bot_mem_inlMap_toElement A B x
        rw [← h] at hx
        exact False.elim (not_left_mem_sum_botElement A B hx)
      | inr y =>
        change (sumSystem A B).botElement = (inrMap A B).toElement y at h
        have hy := right_bot_mem_inrMap_toElement A B y
        rw [← h] at hy
        exact False.elim (not_right_mem_sum_botElement A B hy)
  | coe s₁ =>
    cases w₂ with
    | bot =>
      cases s₁ with
      | inl x =>
        change (inlMap A B).toElement x = (sumSystem A B).botElement at h
        have hx := left_bot_mem_inlMap_toElement A B x
        rw [h] at hx
        exact False.elim (not_left_mem_sum_botElement A B hx)
      | inr y =>
        change (inrMap A B).toElement y = (sumSystem A B).botElement at h
        have hy := right_bot_mem_inrMap_toElement A B y
        rw [h] at hy
        exact False.elim (not_right_mem_sum_botElement A B hy)
    | coe s₂ =>
      cases s₁ with
      | inl x =>
        cases s₂ with
        | inl x' => exact congrArg (fun t => some (Sum.inl t)) (inlMap_toElement_injective A B h)
        | inr y' =>
          change (inlMap A B).toElement x = (inrMap A B).toElement y' at h
          have hx := left_bot_mem_inlMap_toElement A B x
          rw [h] at hx
          exact False.elim <| not_mem_right_of_mem_left A B ((inrMap A B).toElement y')
            hx
            (right_bot_mem_inrMap_toElement A B y')
      | inr y =>
        cases s₂ with
        | inl x' =>
          change (inrMap A B).toElement y = (inlMap A B).toElement x' at h
          have hy := right_bot_mem_inrMap_toElement A B y
          rw [h] at hy
          exact False.elim <| not_mem_right_of_mem_left A B ((inlMap A B).toElement x')
            (left_bot_mem_inlMap_toElement A B x')
            hy
        | inr y' => exact congrArg (fun t => some (Sum.inr t)) (inrMap_toElement_injective A B h)

theorem classifySum_assembleSum (w : WithBot (A.Element ⊕ B.Element)) :
    classifySum A B (assembleSum A B w) = w := by
  apply assembleSum_injective A B
  exact assembleSum_classifySum A B (assembleSum A B w)

theorem inlMap_toElement_le_iff {x y : A.Element} :
    (inlMap A B).toElement x ≤ (inlMap A B).toElement y ↔ x ≤ y := by
  constructor
  · intro h a ha
    have : SumToken.left a ∈ ((inlMap A B).toElement x).carrier := by
      -- from sumElementLft_inl round-trip carrier
      have hx := sumElementLft_inlMap_toElement A B x
      -- a ∈ x = sumElementLft ⇒ left a ∈ inl x
      have : a ∈ (sumElementLft A B ((inlMap A B).toElement x) A.bot
          (left_bot_mem_inlMap_toElement A B x)).carrier := by
        simpa [hx] using ha
      exact this
    exact (sumElementLft_inlMap_toElement A B y) ▸
      (show a ∈ (sumElementLft A B ((inlMap A B).toElement y) A.bot
          (left_bot_mem_inlMap_toElement A B y)).carrier from h this)
  · exact (inlMap A B).toElement_mono

theorem inrMap_toElement_le_iff {x y : B.Element} :
    (inrMap A B).toElement x ≤ (inrMap A B).toElement y ↔ x ≤ y := by
  constructor
  · intro h b hb
    have : SumToken.right b ∈ ((inrMap A B).toElement x).carrier := by
      have hx := sumElementRht_inrMap_toElement A B x
      have : b ∈ (sumElementRht A B ((inrMap A B).toElement x) B.bot
          (right_bot_mem_inrMap_toElement A B x)).carrier := by
        simpa [hx] using hb
      exact this
    exact (sumElementRht_inrMap_toElement A B y) ▸
      (show b ∈ (sumElementRht A B ((inrMap A B).toElement y) B.bot
          (right_bot_mem_inrMap_toElement A B y)).carrier from h this)
  · exact (inrMap A B).toElement_mono

theorem assembleSum_mono {w₁ w₂ : WithBot (A.Element ⊕ B.Element)} (h : w₁ ≤ w₂) :
    assembleSum A B w₁ ≤ assembleSum A B w₂ := by
  cases w₁ with
  | bot => exact botElement_le _ _
  | coe s₁ =>
    cases w₂ with
    | bot => exact (WithBot.not_coe_le_bot _ h).elim
    | coe s₂ =>
      have hs : s₁ ≤ s₂ := WithBot.coe_le_coe.1 h
      cases s₁ with
      | inl x =>
        cases s₂ with
        | inl x' => exact (inlMap A B).toElement_mono (Sum.inl_le_inl_iff.1 hs)
        | inr y' => exact (Sum.not_inl_le_inr hs).elim
      | inr y =>
        cases s₂ with
        | inl x' => exact (Sum.not_inr_le_inl hs).elim
        | inr y' => exact (inrMap A B).toElement_mono (Sum.inr_le_inr_iff.1 hs)

/-- **Separated-sum domain iso (1982).** `|A + B| ≃o WithBot (|A| ⊕ |B|)`. Classical. -/
noncomputable def sumDomainIso :
    WithBot (A.Element ⊕ B.Element) ≃o (sumSystem A B).Element where
  toFun := assembleSum A B
  invFun := classifySum A B
  left_inv := classifySum_assembleSum A B
  right_inv := assembleSum_classifySum A B
  map_rel_iff' := by
    intro w₁ w₂
    constructor
    · intro h
      cases w₁ with
      | bot => exact bot_le
      | coe s₁ =>
        cases w₂ with
        | bot =>
          cases s₁ with
          | inl x =>
            exact False.elim (not_left_mem_sum_botElement A B
              (h (left_bot_mem_inlMap_toElement A B x)))
          | inr y =>
            exact False.elim (not_right_mem_sum_botElement A B
              (h (right_bot_mem_inrMap_toElement A B y)))
        | coe s₂ =>
          refine WithBot.coe_le_coe.2 ?_
          cases s₁ with
          | inl x =>
            cases s₂ with
            | inl x' => exact Sum.inl_le_inl_iff.2 ((inlMap_toElement_le_iff A B).1 h)
            | inr y' =>
              exact False.elim <|
                not_mem_right_of_mem_left A B ((inrMap A B).toElement y')
                  (h (left_bot_mem_inlMap_toElement A B x))
                  (right_bot_mem_inrMap_toElement A B y')
          | inr y =>
            cases s₂ with
            | inl x' =>
              exact False.elim <|
                not_mem_right_of_mem_left A B ((inlMap A B).toElement x')
                  (left_bot_mem_inlMap_toElement A B x')
                  (h (right_bot_mem_inrMap_toElement A B y))
            | inr y' => exact Sum.inr_le_inr_iff.2 ((inrMap_toElement_le_iff A B).1 h)
    · exact assembleSum_mono A B

/-! ## Function space `|A → B| ≃o ApproximableMap A B` -/

/-- Pointwise relation order on approximable maps (Prop 5.3 `Le`). -/
instance instPartialOrderApproximableMap : PartialOrder (ApproximableMap A B) where
  le := @Le _ _ _ _ A B
  le_refl _ _ _ h := h
  le_trans _ _ _ hfg hgh _ _ hf := hgh (hfg hf)
  le_antisymm _ _ hfg hgf := ApproximableMap.ext fun _ _ => ⟨fun h => hfg h, fun h => hgf h⟩

theorem approxMap_toElement_le_iff {f g : ApproximableMap A B} :
    approxMap_toElement A B f ≤ approxMap_toElement A B g ↔ f ≤ g := by
  constructor
  · intro h u v hrel
    have hp : mkFunToken A B u v (f.rel_dom hrel) (f.rel_cod hrel) ∈
        (approxMap_toElement A B f).carrier :=
      (mem_approxMap_toElement A B f).2 hrel
    exact (mem_approxMap_toElement A B g).1 (h hp)
  · intro hfg p hp
    exact (mem_approxMap_toElement A B g).2 (hfg ((mem_approxMap_toElement A B f).1 hp))

/-- **Function-space domain iso (1982, Thm 7.2).** `|A → B| ≃o ApproximableMap A B`. -/
noncomputable def functionSpaceDomainIso :
    ApproximableMap A B ≃o (functionSystem A B).Element where
  toFun := approxMap_toElement A B
  invFun := element_toApproxMap A B
  left_inv := element_toApproxMap_approxMap_toElement A B
  right_inv := approxMap_toElement_element_toApproxMap A B
  map_rel_iff' := by
    intro f g
    exact approxMap_toElement_le_iff A B

end InfoSysConstructions

/-- Blueprint-facing name for the 1982 product domain isomorphism. -/
noncomputable abbrev infoSys_product_domain_equiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) :
    A.Element × B.Element ≃o (productSystem A B).Element :=
  InfoSysConstructions.productDomainIso A B

/-- Blueprint-facing name for the 1982 separated-sum domain isomorphism (classical). -/
noncomputable abbrev infoSys_sum_domain_equiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) :
    WithBot (A.Element ⊕ B.Element) ≃o (sumSystem A B).Element :=
  InfoSysConstructions.sumDomainIso A B

/-- Blueprint-facing name for the 1982 function-space domain isomorphism. -/
noncomputable abbrev infoSys_function_space_domain_equiv {α β : Type*}
    [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β) :
    ApproximableMap A B ≃o (functionSystem A B).Element :=
  InfoSysConstructions.functionSpaceDomainIso A B

end ScottModels

-- Bridge — ScottModels.ScottMapBridge (from ScottModels/ScottMapBridge.lean)

/-!
# Construction cross-links — ApproximableMap ↔ ScottContinuous ↔ ScottMap

* **Factoid 4.6:** `ApproximableMap A B ≃o ScottContinuous A B` (1982).
* **1972 transport:** `ScottMap D D'` conjugates along `presentation_domains_equiv`
  (or the round-filter iso) to pointwise-ordered maps on the round presentation.
* Blueprint packaging: `infoSys_constructions_equiv` bundles the three 1982 domain
  isos with these cross-links.
-/

namespace ScottModels

open Scott1982
open Scott1982.Constructive
open Scott1982.InfoSys
open Scott1982.InfoSys.ApproximableMap
open Scott1972.ContinuousLattice
open ContinuousLatticeToNeighborhood

/-! ## Factoid 4.6 as an order isomorphism -/

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem scottContinuous_ext {A : InfoSys α} {B : InfoSys β}
    {f g : ScottContinuous A B} (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  obtain ⟨tf, mf, df⟩ := f
  obtain ⟨tg, mg, dg⟩ := g
  have : tf = tg := funext h
  subst this
  rfl

/-- Pointwise order on Scott-continuous maps of InfoSys domains. -/
instance instPartialOrderScottContinuous (A : InfoSys α) (B : InfoSys β) :
    PartialOrder (ScottContinuous A B) where
  le f g := ∀ x, f.toFun x ≤ g.toFun x
  le_refl _ _ := le_refl _
  le_trans _ _ _ hfg hgh x := le_trans (hfg x) (hgh x)
  le_antisymm _ _ hfg hgf :=
    scottContinuous_ext fun x => le_antisymm (hfg x) (hgf x)

theorem ofScottContinuous_toScottContinuous {A : InfoSys α} {B : InfoSys β}
    (f : ApproximableMap A B) :
    ofScottContinuous (toScottContinuous f) = f := by
  refine ApproximableMap.ext fun u v => ?_
  constructor
  · intro ⟨hu, hv, hsub⟩
    exact (f.rel_iff_closure_le hu hv).2
      (B.closure_le_element (f.toElement (A.closure u hu)) hv hsub)
  · intro hrel
    refine ⟨f.rel_dom hrel, f.rel_cod hrel, ?_⟩
    intro y hy
    have hv : v ∈ B.Con := f.rel_cod hrel
    have hu : u ∈ A.Con := f.rel_dom hrel
    exact (f.rel_iff_closure_le hu hv).1 hrel (B.subset_closure hv (Finset.mem_coe.1 hy))

theorem toScottContinuous_ofScottContinuous {A : InfoSys α} {B : InfoSys β}
    (g : ScottContinuous A B) :
    toScottContinuous (ofScottContinuous g) = g :=
  scottContinuous_ext fun x => toElement_ofScottContinuous g x

/-- **Factoid 4.6.** Approximable maps ↔ Scott-continuous maps of domains. -/
noncomputable def approximableMap_scottContinuous_equiv (A : InfoSys α) (B : InfoSys β) :
    ApproximableMap A B ≃o ScottContinuous A B where
  toFun := toScottContinuous
  invFun := ofScottContinuous
  left_inv := ofScottContinuous_toScottContinuous
  right_inv := toScottContinuous_ofScottContinuous
  map_rel_iff' := by
    intro f g
    exact (le_iff_toElement_le f g).symm

/-! ## ScottMap conjugation along the round presentation -/

variable {D E : Type*} [CompleteLattice D] [CompleteLattice E]

/-- Conjugate a Scott map along order isomorphisms of the underlying lattices. -/
noncomputable def conjScottMapFun {D' E' : Type*} [LE D'] [LE E']
    (ιD : D ≃o D') (ιE : E ≃o E') (f : ScottMap D E) : D' → E' :=
  ⇑ιE ∘ (f : D → E) ∘ ⇑ιD.symm

theorem conjScottMapFun_le_iff {D' E' : Type*} [PartialOrder D'] [PartialOrder E']
    (ιD : D ≃o D') (ιE : E ≃o E') {f g : ScottMap D E} :
    (∀ x : D', conjScottMapFun ιD ιE f x ≤ conjScottMapFun ιD ιE g x) ↔ f ≤ g := by
  constructor
  · intro h
    rw [ScottMap.le_def]
    intro x
    have hx : ιE (f x) ≤ ιE (g x) := by
      simpa [conjScottMapFun, OrderIso.symm_apply_apply] using h (ιD x)
    exact ιE.map_rel_iff.mp hx
  · intro hfg x
    exact ιE.monotone (hfg (ιD.symm x))

/-- Scott maps packaged as their conjugates along given presentation isos. -/
structure ConjScottMap {D' E' : Type*} [PartialOrder D'] [PartialOrder E']
    (ιD : D ≃o D') (ιE : E ≃o E') where
  scott : ScottMap D E

namespace ConjScottMap

variable {D' E' : Type*} [PartialOrder D'] [PartialOrder E']
variable (ιD : D ≃o D') (ιE : E ≃o E')

noncomputable instance : CoeFun (ConjScottMap ιD ιE) (fun _ => D' → E') where
  coe g := conjScottMapFun ιD ιE g.scott

theorem ext {f g : ConjScottMap ιD ιE} (h : f.scott = g.scott) : f = g := by
  cases f; cases g; congr

noncomputable instance : PartialOrder (ConjScottMap ιD ιE) where
  le f g := ∀ x, conjScottMapFun ιD ιE f.scott x ≤ conjScottMapFun ιD ιE g.scott x
  le_refl _ _ := le_refl _
  le_trans _ _ _ hfg hgh x := le_trans (hfg x) (hgh x)
  le_antisymm f g hfg hgf := by
    refine ext ιD ιE ?_
    exact le_antisymm
      ((conjScottMapFun_le_iff ιD ιE).1 hfg)
      ((conjScottMapFun_le_iff ιD ιE).1 hgf)

/-- **1972 ↔ round presentation:** Scott maps ≃ conjugates along the given isos. -/
noncomputable def orderIso : ScottMap D E ≃o ConjScottMap ιD ιE where
  toFun f := ⟨f⟩
  invFun g := g.scott
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro f g
    exact conjScottMapFun_le_iff ιD ιE

end ConjScottMap

section ContinuousRoundFilter

variable (hD : IsContinuousLattice D) (hE : IsContinuousLattice E)
include hD hE

/-- Conjugation along round `↟`-filters (no `DecidableEq` needed). -/
noncomputable abbrev scottMap_roundFilter_iso :
    ScottMap D E ≃o
      ConjScottMap (continuousLattice_roundFilter_iso hD)
        (continuousLattice_roundFilter_iso hE) :=
  ConjScottMap.orderIso (continuousLattice_roundFilter_iso hD)
    (continuousLattice_roundFilter_iso hE)

end ContinuousRoundFilter

section ContinuousRoundInfoSys

variable (hD : IsContinuousLattice D) (hE : IsContinuousLattice E)
variable [DecidableEq D] [DecidableEq E]
include hD hE

/-- Conjugation along round InfoSys elements of the `↟`-basis. -/
noncomputable abbrev scottMap_roundInfoSys_iso :
    ScottMap D E ≃o
      ConjScottMap (presentation_domains_equiv hD) (presentation_domains_equiv hE) :=
  ConjScottMap.orderIso (presentation_domains_equiv hD) (presentation_domains_equiv hE)

end ContinuousRoundInfoSys

/-! ## Blueprint packaging

Bundled 1982 construction domain isos + 1972/1982 function-space cross-links. -/
namespace infoSys_constructions_equiv

noncomputable abbrev product := @infoSys_product_domain_equiv
noncomputable abbrev sum := @infoSys_sum_domain_equiv
noncomputable abbrev functionSpace := @infoSys_function_space_domain_equiv
noncomputable abbrev approximable_scottContinuous := @approximableMap_scottContinuous_equiv
noncomputable abbrev scottMap_roundFilter := @scottMap_roundFilter_iso
noncomputable abbrev scottMap_roundInfoSys := @scottMap_roundInfoSys_iso

end infoSys_constructions_equiv

end ScottModels

-- Bridge — ScottModels.SexDomainEquation (from ScottModels/SexDomainEquation.lean)

/-!
# Domain equation `|T| ≃o |A + (T × T)|` via unfolding

Factoid 8.1 presents `T` as an inductive token system whose official
right-hand side is `sumSystem A (productSystem T T)`. The token map
`treeUnfold` is a retraction, identifying only Scott’s two encodings of
the product bottom (`pairL Δ` and `pairR Δ`). After the matching
`ent_bot` clauses, closed elements are saturated for that kernel, so
image and preimage of `treeUnfold` are inverse order isomorphisms of
domains.
-/

namespace ScottModels

open Scott1982
open Scott1982.Constructive
open Scott1982.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

/-- Official product of the tree system with itself. -/
abbrev TreeProd : InfoSys (ProdToken (treeSystem A) (treeSystem A)) :=
  productSystem (treeSystem A) (treeSystem A)

/-- Canonical section of `treeUnfold`. Product bottom folds to `pairL bot`. -/
def treeFold :
    SumToken α (ProdToken (treeSystem A) (treeSystem A)) → TreeToken α
  | .bot => .bot
  | .left x => .atom x
  | .right p =>
      if p.val.2 = treeBot then .pairL p.val.1 else .pairR p.val.2

theorem treeUnfold_treeFold (s : SumToken α (ProdToken (treeSystem A) (treeSystem A))) :
    treeUnfold A (treeFold A s) = s := by
  cases s with
  | bot => rfl
  | left x => rfl
  | right p =>
    dsimp [treeFold, treeUnfold]
    split_ifs with hb
    · apply congrArg SumToken.right
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact hb.symm
    · have ha : p.val.1 = treeBot := by
        rcases p.property with h1 | h2
        · exact h1
        · exact False.elim (hb h2)
      apply congrArg SumToken.right
      apply Subtype.ext
      apply Prod.ext
      · exact ha.symm
      · rfl

theorem treeFold_eq_or_pairBots (t : TreeToken α) :
    treeFold A (treeUnfold A t) = t ∨
      t = .pairR .bot ∧ treeFold A (treeUnfold A t) = .pairL .bot := by
  cases t with
  | bot => exact Or.inl rfl
  | atom x => exact Or.inl rfl
  | pairL t =>
    refine Or.inl ?_
    simp [treeFold, treeUnfold, treeBot]
  | pairR t =>
    simp only [treeFold, treeUnfold, treeBot]
    split_ifs with hb
    · cases t with
      | bot => exact Or.inr ⟨rfl, rfl⟩
      | atom _ | pairL _ | pairR _ => exact False.elim (nomatch hb)
    · exact Or.inl (if_neg hb)

private def SexDomainEquation_unfoldInsert (t : TreeToken α) :
    Finset (SumToken α (ProdToken (treeSystem A) (treeSystem A))) →
      Finset (SumToken α (ProdToken (treeSystem A) (treeSystem A))) :=
  insert (treeUnfold A t)

private instance SexDomainEquation_SexDomainEquation_privInst1 : LeftCommutative (SexDomainEquation_unfoldInsert (A := A)) :=
  ⟨fun p q s => insert_comm' (treeUnfold A p) (treeUnfold A q) s⟩

/-- Choice-free image of a tree finset under `treeUnfold`. -/
def unfoldFinset (u : Finset (TreeToken α)) :
    Finset (SumToken α (ProdToken (treeSystem A) (treeSystem A))) :=
  Multiset.foldr (SexDomainEquation_unfoldInsert A) ∅ u.1

private theorem SexDomainEquation_mem_foldr_unfold (m : Multiset (TreeToken α))
    (s : SumToken α (ProdToken (treeSystem A) (treeSystem A))) :
    s ∈ Multiset.foldr (SexDomainEquation_unfoldInsert A) ∅ m ↔
      ∃ t ∈ m, treeUnfold A t = s := by
  refine Multiset.induction_on m ?_ ?_
  · constructor
    · intro hs; exact False.elim (Finset.notMem_empty s hs)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro t rest ih
    simp only [Multiset.foldr_cons, SexDomainEquation_unfoldInsert, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (h | ⟨q, hq, hq'⟩)
      · exact ⟨t, Or.inl rfl, h.symm⟩
      · exact ⟨q, Or.inr hq, hq'⟩
    · rintro ⟨q, hq, hq'⟩
      rcases hq with rfl | hq
      · exact Or.inl hq'.symm
      · exact Or.inr ⟨q, hq, hq'⟩

theorem mem_unfoldFinset {u : Finset (TreeToken α)}
    {s : SumToken α (ProdToken (treeSystem A) (treeSystem A))} :
    s ∈ unfoldFinset A u ↔ ∃ t ∈ u, treeUnfold A t = s := by
  unfold unfoldFinset
  rw [SexDomainEquation_mem_foldr_unfold]
  simp only [Finset.mem_def]

private def SexDomainEquation_foldInsert (s : SumToken α (ProdToken (treeSystem A) (treeSystem A))) :
    Finset (TreeToken α) → Finset (TreeToken α) :=
  insert (treeFold A s)

private instance SexDomainEquation_SexDomainEquation_privInst2 : LeftCommutative (SexDomainEquation_foldInsert (A := A)) :=
  ⟨fun p q t => insert_comm' (treeFold A p) (treeFold A q) t⟩

/-- Choice-free image of an RHS finset under `treeFold`. -/
def foldFinset (Y : Finset (SumToken α (ProdToken (treeSystem A) (treeSystem A)))) :
    Finset (TreeToken α) :=
  Multiset.foldr (SexDomainEquation_foldInsert A) ∅ Y.1

private theorem SexDomainEquation_mem_foldr_fold
    (m : Multiset (SumToken α (ProdToken (treeSystem A) (treeSystem A))))
    (t : TreeToken α) :
    t ∈ Multiset.foldr (SexDomainEquation_foldInsert A) ∅ m ↔
      ∃ s ∈ m, treeFold A s = t := by
  refine Multiset.induction_on m ?_ ?_
  · constructor
    · intro ht; exact False.elim (Finset.notMem_empty t ht)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro s rest ih
    simp only [Multiset.foldr_cons, SexDomainEquation_foldInsert, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (h | ⟨q, hq, hq'⟩)
      · exact ⟨s, Or.inl rfl, h.symm⟩
      · exact ⟨q, Or.inr hq, hq'⟩
    · rintro ⟨q, hq, hq'⟩
      rcases hq with rfl | hq
      · exact Or.inl hq'.symm
      · exact Or.inr ⟨q, hq, hq'⟩

theorem mem_foldFinset
    {Y : Finset (SumToken α (ProdToken (treeSystem A) (treeSystem A)))}
    {t : TreeToken α} :
    t ∈ foldFinset A Y ↔ ∃ s ∈ Y, treeFold A s = t := by
  unfold foldFinset
  rw [SexDomainEquation_mem_foldr_fold]
  simp only [Finset.mem_def]

theorem unfoldFinset_foldFinset
    (Y : Finset (SumToken α (ProdToken (treeSystem A) (treeSystem A)))) :
    unfoldFinset A (foldFinset A Y) = Y := by
  ext s
  constructor
  · intro hs
    rcases (mem_unfoldFinset A).1 hs with ⟨t, ht, hU⟩
    rcases (mem_foldFinset A).1 ht with ⟨s', hs', rfl⟩
    rw [treeUnfold_treeFold] at hU
    rwa [← hU]
  · intro hs
    exact (mem_unfoldFinset A).2 ⟨treeFold A s,
      (mem_foldFinset A).2 ⟨s, hs, rfl⟩, treeUnfold_treeFold A s⟩

theorem lftFinset_image_unfold (u : Finset (TreeToken α)) :
    lftFinset (unfoldFinset A u) = atomFinset u := by
  ext x
  constructor
  · intro hx
    have : SumToken.left x ∈ unfoldFinset A u := (mem_lftFinset).1 hx
    rcases (mem_unfoldFinset A).1 this with ⟨t, ht, hU⟩
    cases t with
    | atom y =>
      have : y = x := SumToken.left.inj hU
      subst this
      exact mem_atomFinset.2 ht
    | bot | pairL _ | pairR _ => exact nomatch hU
  · intro hx
    exact (mem_lftFinset).2
      ((mem_unfoldFinset A).2 ⟨.atom x, mem_atomFinset.1 hx, rfl⟩)

theorem rhtFinset_image_unfold_mem (u : Finset (TreeToken α))
    (y : ProdToken (treeSystem A) (treeSystem A)) :
    y ∈ rhtFinset (unfoldFinset A u) ↔
      (∃ t, .pairL t ∈ u ∧ y = ⟨(t, treeBot), Or.inr rfl⟩) ∨
        (∃ t, .pairR t ∈ u ∧ y = ⟨(treeBot, t), Or.inl rfl⟩) := by
  constructor
  · intro hy
    have : SumToken.right y ∈ unfoldFinset A u := (mem_rhtFinset).1 hy
    rcases (mem_unfoldFinset A).1 this with ⟨t, ht, hU⟩
    cases t with
    | pairL s =>
      refine Or.inl ⟨s, ht, ?_⟩
      exact SumToken.right.inj hU.symm
    | pairR s =>
      refine Or.inr ⟨s, ht, ?_⟩
      exact SumToken.right.inj hU.symm
    | bot | atom _ => exact nomatch hU
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact (mem_rhtFinset).2 ((mem_unfoldFinset A).2 ⟨.pairL t, ht, rfl⟩)
    · exact (mem_rhtFinset).2 ((mem_unfoldFinset A).2 ⟨.pairR t, ht, rfl⟩)

theorem TreeCon_image_sumCon {u : Finset (TreeToken α)} (hu : TreeCon A u) :
    SumCon A (TreeProd A) (unfoldFinset A u) := by
  cases hu with
  | left _ hA hL hR =>
    refine Or.inl ⟨?_, ?_⟩
    · rw [lftFinset_image_unfold]; exact hA
    · ext y
      constructor
      · intro hy
        rcases (rhtFinset_image_unfold_mem A u y).1 hy with ⟨t, ht, _⟩ | ⟨t, ht, _⟩
        · exact False.elim (Finset.notMem_empty t (hL ▸ mem_pairLFinset.2 ht))
        · exact False.elim (Finset.notMem_empty t (hR ▸ mem_pairRFinset.2 ht))
      · intro hy
        exact False.elim (Finset.notMem_empty y hy)
  | right _ hA hL hR =>
    refine Or.inr ⟨?_, ?_⟩
    · rw [lftFinset_image_unfold]; exact hA
    · refine ⟨?_, ?_⟩
      · -- fst of the product tokens is a TreeCon set (pairL, plus bot if needed)
        have hsub :
            fstFinset (treeSystem A) (treeSystem A)
                (rhtFinset (unfoldFinset A u)) ⊆
              insert .bot (pairLFinset u) := by
          intro t ht
          rcases (mem_fstFinset (treeSystem A) (treeSystem A)).1 ht with ⟨p, hp, hb, rfl⟩
          rcases (rhtFinset_image_unfold_mem A u p).1 hp with ⟨s, hs, hp'⟩ | ⟨s, hs, hp'⟩
          · subst hp'
            exact Finset.mem_insert_of_mem (mem_pairLFinset.2 hs)
          · subst hp'
            exact Finset.mem_insert_self _ _
        exact (treeSystem A).con_subset (TreeCon_insert_bot A hL) hsub
      · have hsub :
            sndFinset (treeSystem A) (treeSystem A)
                (rhtFinset (unfoldFinset A u)) ⊆
              insert .bot (pairRFinset u) := by
          intro t ht
          rcases (mem_sndFinset (treeSystem A) (treeSystem A)).1 ht with ⟨p, hp, ha, rfl⟩
          rcases (rhtFinset_image_unfold_mem A u p).1 hp with ⟨s, hs, hp'⟩ | ⟨s, hs, hp'⟩
          · subst hp'
            exact Finset.mem_insert_self _ _
          · subst hp'
            exact Finset.mem_insert_of_mem (mem_pairRFinset.2 hs)
        exact (treeSystem A).con_subset (TreeCon_insert_bot A hR) hsub

theorem SumCon_image_treeCon {u : Finset (TreeToken α)}
    (hu : SumCon A (TreeProd A) (unfoldFinset A u)) : TreeCon A u := by
  rcases hu with ⟨hL, hr⟩ | ⟨hl, hR⟩
  · refine TreeCon.left _ (by rwa [lftFinset_image_unfold] at hL) ?_ ?_
    · ext t
      constructor
      · intro ht
        have : (⟨(t, treeBot), Or.inr rfl⟩ : ProdToken (treeSystem A) (treeSystem A)) ∈
            rhtFinset (unfoldFinset A u) :=
          (rhtFinset_image_unfold_mem A u _).2 (Or.inl ⟨t, mem_pairLFinset.1 ht, rfl⟩)
        rw [hr] at this
        exact False.elim (Finset.notMem_empty _ this)
      · intro ht
        exact False.elim (Finset.notMem_empty t ht)
    · ext t
      constructor
      · intro ht
        have : (⟨(treeBot, t), Or.inl rfl⟩ : ProdToken (treeSystem A) (treeSystem A)) ∈
            rhtFinset (unfoldFinset A u) :=
          (rhtFinset_image_unfold_mem A u _).2 (Or.inr ⟨t, mem_pairRFinset.1 ht, rfl⟩)
        rw [hr] at this
        exact False.elim (Finset.notMem_empty _ this)
      · intro ht
        exact False.elim (Finset.notMem_empty t ht)
  · refine TreeCon.right _ (by rwa [lftFinset_image_unfold] at hl) ?_ ?_
    · have hsub : pairLFinset u ⊆
          fstFinset (treeSystem A) (treeSystem A)
            (rhtFinset (unfoldFinset A u)) := by
        intro t ht
        exact (mem_fstFinset (treeSystem A) (treeSystem A)).2
          ⟨⟨(t, treeBot), Or.inr rfl⟩,
            (rhtFinset_image_unfold_mem A u _).2 (Or.inl ⟨t, mem_pairLFinset.1 ht, rfl⟩),
            rfl, rfl⟩
      exact (treeSystem A).con_subset hR.1 hsub
    · have hsub : pairRFinset u ⊆
          sndFinset (treeSystem A) (treeSystem A)
            (rhtFinset (unfoldFinset A u)) := by
        intro t ht
        exact (mem_sndFinset (treeSystem A) (treeSystem A)).2
          ⟨⟨(treeBot, t), Or.inl rfl⟩,
            (rhtFinset_image_unfold_mem A u _).2 (Or.inr ⟨t, mem_pairRFinset.1 ht, rfl⟩),
            rfl, rfl⟩
      exact (treeSystem A).con_subset hR.2 hsub

theorem TreeEnt_sumEnt {u : Finset (TreeToken α)} {p : TreeToken α}
    (h : TreeEnt A u p) :
    SumEnt A (TreeProd A) (unfoldFinset A u) (treeUnfold A p) := by
  have hCon : SumCon A (TreeProd A) (unfoldFinset A u) :=
    TreeCon_image_sumCon A h.1
  refine ⟨hCon, ?_⟩
  cases p with
  | bot => exact trivial
  | atom x =>
    refine ⟨?_, ?_⟩
    · rw [lftFinset_image_unfold]; exact h.2.1
    · rw [lftFinset_image_unfold]; exact h.2.2
  | pairL t =>
    have hr : rhtFinset (unfoldFinset A u) ≠ ∅ := by
      rcases h.2.2.2.2 with ⟨hne, _⟩ | ⟨_, hR⟩
      · obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hne
        exact Finset.ne_empty_of_mem
          ((rhtFinset_image_unfold_mem A u _).2
            (Or.inl ⟨s, mem_pairLFinset.1 hs, rfl⟩))
      · obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hR
        exact Finset.ne_empty_of_mem
          ((rhtFinset_image_unfold_mem A u _).2
            (Or.inr ⟨s, mem_pairRFinset.1 hs, rfl⟩))
    refine ⟨hr, ?_⟩
    refine ⟨hCon.elim (fun hL => False.elim (hr hL.2)) (fun hR => hR.2), ?_, ?_⟩
    · intro
      -- T.Ent fst t
      have hsub : pairLFinset u ⊆
          fstFinset (treeSystem A) (treeSystem A)
            (rhtFinset (unfoldFinset A u)) := by
        intro s hs
        exact (mem_fstFinset (treeSystem A) (treeSystem A)).2
          ⟨⟨(s, treeBot), Or.inr rfl⟩,
            (rhtFinset_image_unfold_mem A u _).2 (Or.inl ⟨s, mem_pairLFinset.1 hs, rfl⟩),
            rfl, rfl⟩
      have hFstCon : fstFinset (treeSystem A) (treeSystem A)
          (rhtFinset (unfoldFinset A u)) ∈ (treeSystem A).Con :=
        hCon.elim (fun hL => False.elim (hr hL.2)) (fun hR => hR.2.1)
      rcases h.2.2.2.2 with ⟨hne, hPay⟩ | ⟨rfl, _⟩
      · exact (treeSystem A).ent_trans hFstCon h.2.2.1
          (fun y hy => (treeSystem A).ent_refl hFstCon (hsub hy)) ⟨h.2.2.1, hPay⟩
      · exact (treeSystem A).ent_bot hFstCon
    · intro ht
      have hSndCon : sndFinset (treeSystem A) (treeSystem A)
          (rhtFinset (unfoldFinset A u)) ∈ (treeSystem A).Con :=
        hCon.elim (fun hL => False.elim (hr hL.2)) (fun hR => hR.2.2)
      exact (treeSystem A).ent_bot hSndCon

  | pairR t =>
    have hr : rhtFinset (unfoldFinset A u) ≠ ∅ := by
      rcases h.2.2.2.2 with ⟨hne, _⟩ | ⟨_, hL⟩
      · obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hne
        exact Finset.ne_empty_of_mem
          ((rhtFinset_image_unfold_mem A u _).2
            (Or.inr ⟨s, mem_pairRFinset.1 hs, rfl⟩))
      · obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hL
        exact Finset.ne_empty_of_mem
          ((rhtFinset_image_unfold_mem A u _).2
            (Or.inl ⟨s, mem_pairLFinset.1 hs, rfl⟩))
    refine ⟨hr, ?_⟩
    refine ⟨hCon.elim (fun hL => False.elim (hr hL.2)) (fun hR => hR.2), ?_, ?_⟩
    · intro
      have hFstCon : fstFinset (treeSystem A) (treeSystem A)
          (rhtFinset (unfoldFinset A u)) ∈ (treeSystem A).Con :=
        hCon.elim (fun hL => False.elim (hr hL.2)) (fun hR => hR.2.1)
      exact (treeSystem A).ent_bot hFstCon
    · intro
      have hsub : pairRFinset u ⊆
          sndFinset (treeSystem A) (treeSystem A)
            (rhtFinset (unfoldFinset A u)) := by
        intro s hs
        exact (mem_sndFinset (treeSystem A) (treeSystem A)).2
          ⟨⟨(treeBot, s), Or.inl rfl⟩,
            (rhtFinset_image_unfold_mem A u _).2 (Or.inr ⟨s, mem_pairRFinset.1 hs, rfl⟩),
            rfl, rfl⟩
      have hSndCon : sndFinset (treeSystem A) (treeSystem A)
          (rhtFinset (unfoldFinset A u)) ∈ (treeSystem A).Con :=
        hCon.elim (fun hL => False.elim (hr hL.2)) (fun hR => hR.2.2)
      rcases h.2.2.2.2 with ⟨hne, hPay⟩ | ⟨rfl, _⟩
      · exact (treeSystem A).ent_trans hSndCon h.2.2.1
          (fun y hy => (treeSystem A).ent_refl hSndCon (hsub hy)) ⟨h.2.2.1, hPay⟩
      · exact (treeSystem A).ent_bot hSndCon

theorem SumEnt_treeFold {u : Finset (TreeToken α)}
    {s : SumToken α (ProdToken (treeSystem A) (treeSystem A))}
    (h : SumEnt A (TreeProd A) (unfoldFinset A u) s) :
    TreeEnt A u (treeFold A s) := by
  have hu : TreeCon A u := SumCon_image_treeCon A h.1
  refine ⟨hu, ?_⟩
  cases s with
  | bot => exact trivial
  | left x =>
    dsimp [treeFold]
    refine ⟨?_, ?_⟩
    · rw [← lftFinset_image_unfold A u]; exact h.2.1
    · rw [← lftFinset_image_unfold A u]; exact h.2.2
  | right p =>
    dsimp [treeFold]
    have hAt : atomFinset u = ∅ := by
      have hl := (lftFinset_image_unfold A u)
      have : lftFinset (unfoldFinset A u) = ∅ :=
        SumCon_lft_empty_of_rht_nonempty A (TreeProd A) h.1 h.2.1
      rwa [hl] at this
    split_ifs with hb
    · refine ⟨hAt, TreeCon_pairL_of_right A hu hAt, TreeCon_pairR_of_right A hu hAt, ?_⟩
      have hEnt := h.2.2
      -- ProdEnt: Ent fst p.1 (since p.2 = bot)
      have hFst : (treeSystem A).Ent
          (fstFinset (treeSystem A) (treeSystem A)
            (rhtFinset (unfoldFinset A u))) p.val.1 :=
        hEnt.2.1 hb
      have hsub :
          fstFinset (treeSystem A) (treeSystem A)
              (rhtFinset (unfoldFinset A u)) ⊆
            insert .bot (pairLFinset u) := by
        intro t ht
        rcases (mem_fstFinset (treeSystem A) (treeSystem A)).1 ht with ⟨q, hq, _, rfl⟩
        rcases (rhtFinset_image_unfold_mem A u q).1 hq with ⟨w, hw, hq'⟩ | ⟨w, hw, hq'⟩
        · subst hq'; exact Finset.mem_insert_of_mem (mem_pairLFinset.2 hw)
        · subst hq'; exact Finset.mem_insert_self _ _
      -- Transfer Ent along the subset into pairL ∪ {bot}
      have hIns : TreeCon A (insert .bot (pairLFinset u)) :=
        TreeCon_insert_bot A (TreeCon_pairL_of_right A hu hAt)
      have hPay : TreeEntPayload A (insert .bot (pairLFinset u)) p.val.1 :=
        ((treeSystem A).ent_trans hIns
          (SumCon_rht_con_of_rht_nonempty A (TreeProd A) h.1 h.2.1).1
          (fun y hy => (treeSystem A).ent_refl hIns (hsub hy)) hFst).2
      obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty h.2.1
      rcases (rhtFinset_image_unfold_mem A u y).1 hy with ⟨w, hwL, _⟩ | ⟨w, hwR, _⟩
      · refine Or.inl ⟨Finset.ne_empty_of_mem (mem_pairLFinset.2 hwL), ?_⟩
        exact ((treeSystem A).ent_trans (TreeCon_pairL_of_right A hu hAt) hIns
          (fun z hz => by
            rw [Finset.mem_insert] at hz
            rcases hz with rfl | hz
            · exact (treeSystem A).ent_bot (TreeCon_pairL_of_right A hu hAt)
            · exact (treeSystem A).ent_refl (TreeCon_pairL_of_right A hu hAt) hz)
          ⟨hIns, hPay⟩).2
      · if ht : p.val.1 = .bot then
          exact Or.inr ⟨ht, Finset.ne_empty_of_mem (mem_pairRFinset.2 hwR)⟩
        else
          refine Or.inl ⟨?_, ?_⟩
          · intro hempty
            have hEq : insert (.bot : TreeToken α) (pairLFinset u) = {.bot} := by
              rw [hempty]; rfl
            exact ht (TreeEntPayload_of_no_atoms_no_pairs A
              atomFinset_singleton_bot pairLFinset_singleton_bot
              pairRFinset_singleton_bot (hEq ▸ hPay))
          · exact ((treeSystem A).ent_trans (TreeCon_pairL_of_right A hu hAt) hIns
              (fun z hz => by
                rw [Finset.mem_insert] at hz
                rcases hz with rfl | hz
                · exact (treeSystem A).ent_bot (TreeCon_pairL_of_right A hu hAt)
                · exact (treeSystem A).ent_refl (TreeCon_pairL_of_right A hu hAt) hz)
              ⟨hIns, hPay⟩).2
    · -- pairR p.2
      refine ⟨hAt, TreeCon_pairR_of_right A hu hAt, TreeCon_pairL_of_right A hu hAt, ?_⟩
      have ha : p.val.1 = treeBot := by
        rcases p.property with h1 | h2
        · exact h1
        · exact False.elim (hb h2)
      have hEnt := h.2.2
      have hSnd : (treeSystem A).Ent
          (sndFinset (treeSystem A) (treeSystem A)
            (rhtFinset (unfoldFinset A u))) p.val.2 :=
        hEnt.2.2 ha
      have hIns : TreeCon A (insert .bot (pairRFinset u)) :=
        TreeCon_insert_bot A (TreeCon_pairR_of_right A hu hAt)
      have hsub :
          sndFinset (treeSystem A) (treeSystem A)
              (rhtFinset (unfoldFinset A u)) ⊆
            insert .bot (pairRFinset u) := by
        intro t ht
        rcases (mem_sndFinset (treeSystem A) (treeSystem A)).1 ht with ⟨q, hq, _, rfl⟩
        rcases (rhtFinset_image_unfold_mem A u q).1 hq with ⟨w, hw, hq'⟩ | ⟨w, hw, hq'⟩
        · subst hq'; exact Finset.mem_insert_self _ _
        · subst hq'; exact Finset.mem_insert_of_mem (mem_pairRFinset.2 hw)
      have hPay : TreeEntPayload A (insert .bot (pairRFinset u)) p.val.2 :=
        ((treeSystem A).ent_trans hIns
          (SumCon_rht_con_of_rht_nonempty A (TreeProd A) h.1 h.2.1).2
          (fun y hy => (treeSystem A).ent_refl hIns (hsub hy)) hSnd).2
      refine Or.inl ⟨?_, ?_⟩
      · intro hempty
        have hEq : insert (.bot : TreeToken α) (pairRFinset u) = {.bot} := by
          rw [hempty]; rfl
        have ht : p.val.2 = .bot :=
          TreeEntPayload_of_no_atoms_no_pairs A
            atomFinset_singleton_bot pairLFinset_singleton_bot
            pairRFinset_singleton_bot (hEq ▸ hPay)
        exact hb (ht ▸ rfl)
      · exact ((treeSystem A).ent_trans (TreeCon_pairR_of_right A hu hAt) hIns
          (fun z hz => by
            rw [Finset.mem_insert] at hz
            rcases hz with rfl | hz
            · exact (treeSystem A).ent_bot (TreeCon_pairR_of_right A hu hAt)
            · exact (treeSystem A).ent_refl (TreeCon_pairR_of_right A hu hAt) hz)
          ⟨hIns, hPay⟩).2

theorem TreeEnt_pairL_bot_of_pairs {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (h : pairLFinset u ≠ ∅ ∨ pairRFinset u ≠ ∅) :
    TreeEnt A u (.pairL .bot) :=
  ⟨hu, TreeCon_atoms_empty_of_right A hu h,
    TreeCon_pairL_of_right A hu (TreeCon_atoms_empty_of_right A hu h),
    TreeCon_pairR_of_right A hu (TreeCon_atoms_empty_of_right A hu h),
    h.elim (fun hL => Or.inl ⟨hL, trivial⟩) (fun hR => Or.inr ⟨rfl, hR⟩)⟩

theorem TreeEnt_pairR_bot_of_pairs {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (h : pairLFinset u ≠ ∅ ∨ pairRFinset u ≠ ∅) :
    TreeEnt A u (.pairR .bot) :=
  ⟨hu, TreeCon_atoms_empty_of_right A hu h,
    TreeCon_pairR_of_right A hu (TreeCon_atoms_empty_of_right A hu h),
    TreeCon_pairL_of_right A hu (TreeCon_atoms_empty_of_right A hu h),
    h.elim (fun hL => Or.inr ⟨rfl, hL⟩) (fun hR => Or.inl ⟨hR, trivial⟩)⟩

theorem mem_closed_pair_bots (x : (treeSystem A).Element) :
    .pairL .bot ∈ x.carrier ↔ .pairR .bot ∈ x.carrier := by
  constructor
  · intro h
    have hsub : (({TreeToken.pairL treeBot} : Finset (TreeToken α)) : Set _) ⊆
        x.carrier := by
      intro a ha
      have : a = .pairL treeBot := Finset.mem_singleton.mp (Finset.mem_coe.1 ha)
      subst this; exact h
    exact x.closed {TreeToken.pairL treeBot} (.pairR treeBot) hsub
      (TreeEnt_pairR_bot_of_pairs A (x.consistent _ hsub)
        (Or.inl (Finset.ne_empty_of_mem (by
          rw [pairLFinset_singleton_pairL]; exact Finset.mem_singleton_self _))))
  · intro h
    have hsub : (({TreeToken.pairR treeBot} : Finset (TreeToken α)) : Set _) ⊆
        x.carrier := by
      intro a ha
      have : a = .pairR treeBot := Finset.mem_singleton.mp (Finset.mem_coe.1 ha)
      subst this; exact h
    exact x.closed {TreeToken.pairR treeBot} (.pairL treeBot) hsub
      (TreeEnt_pairL_bot_of_pairs A (x.consistent _ hsub)
        (Or.inr (Finset.ne_empty_of_mem (by
          rw [pairRFinset_singleton_pairR]; exact Finset.mem_singleton_self _))))

theorem saturated_of_closed (x : (treeSystem A).Element) {t : TreeToken α}
    (ht : t ∈ x.carrier) : treeFold A (treeUnfold A t) ∈ x.carrier := by
  rcases treeFold_eq_or_pairBots A t with h | ⟨rfl, hf⟩
  · rwa [h]
  · rw [hf]
    exact (mem_closed_pair_bots A x).2 ht

/-- Image of a tree element under `treeUnfold` is an official RHS element. -/
def unfoldElement (x : (treeSystem A).Element) : (treeRhs A).Element where
  carrier := treeUnfold A '' x.carrier
  consistent := by
    intro Y hY
    have hFold : ↑(foldFinset A Y) ⊆ x.carrier := by
      intro t ht
      rcases (mem_foldFinset A).1 (Finset.mem_coe.1 ht) with ⟨s, hs, rfl⟩
      have hs' : s ∈ treeUnfold A '' x.carrier := hY (Finset.mem_coe.2 hs)
      rcases hs' with ⟨t', ht', hU⟩
      have : treeFold A (treeUnfold A t') ∈ x.carrier := saturated_of_closed A x ht'
      rwa [hU] at this
    have hCon : TreeCon A (foldFinset A Y) := x.consistent _ hFold
    have : SumCon A (TreeProd A) (unfoldFinset A (foldFinset A Y)) :=
      TreeCon_image_sumCon A hCon
    rwa [unfoldFinset_foldFinset] at this
  closed := by
    intro Y s hY hEnt
    have hFold : ↑(foldFinset A Y) ⊆ x.carrier := by
      intro t ht
      rcases (mem_foldFinset A).1 (Finset.mem_coe.1 ht) with ⟨s', hs', rfl⟩
      have hs'' : s' ∈ treeUnfold A '' x.carrier := hY (Finset.mem_coe.2 hs')
      rcases hs'' with ⟨t', ht', hU⟩
      have : treeFold A (treeUnfold A t') ∈ x.carrier := saturated_of_closed A x ht'
      rwa [hU] at this
    have hEnt' : SumEnt A (TreeProd A)
        (unfoldFinset A (foldFinset A Y)) s := by
      rwa [unfoldFinset_foldFinset]
    have hT : TreeEnt A (foldFinset A Y) (treeFold A s) :=
      SumEnt_treeFold A hEnt'
    have ht : treeFold A s ∈ x.carrier :=
      x.closed _ _ hFold hT
    refine ⟨treeFold A s, ht, treeUnfold_treeFold A s⟩

/-- Preimage of an official RHS element under `treeUnfold` is a tree element. -/
def foldElement (y : (treeRhs A).Element) : (treeSystem A).Element where
  carrier := treeUnfold A ⁻¹' y.carrier
  consistent := by
    intro Y hY
    have him : ↑(unfoldFinset A Y) ⊆ y.carrier := by
      intro s hs
      rcases (mem_unfoldFinset A).1 (Finset.mem_coe.1 hs) with ⟨t, ht, rfl⟩
      exact hY (Finset.mem_coe.2 ht)
    have : SumCon A (TreeProd A) (unfoldFinset A Y) := y.consistent _ him
    exact SumCon_image_treeCon A this
  closed := by
    intro Y p hY hEnt
    have him : ↑(unfoldFinset A Y) ⊆ y.carrier := by
      intro s hs
      rcases (mem_unfoldFinset A).1 (Finset.mem_coe.1 hs) with ⟨t, ht, rfl⟩
      exact hY (Finset.mem_coe.2 ht)
    have hS : SumEnt A (TreeProd A) (unfoldFinset A Y) (treeUnfold A p) :=
      TreeEnt_sumEnt A hEnt
    exact y.closed _ _ him hS

theorem unfoldElement_foldElement (y : (treeRhs A).Element) :
    unfoldElement A (foldElement A y) = y := by
  refine le_antisymm ?_ ?_
  · intro s hs
    rcases hs with ⟨t, ht, rfl⟩
    exact ht
  · intro s hs
    refine ⟨treeFold A s, ?_, treeUnfold_treeFold A s⟩
    change treeUnfold A (treeFold A s) ∈ y.carrier
    rwa [treeUnfold_treeFold]

theorem foldElement_unfoldElement (x : (treeSystem A).Element) :
    foldElement A (unfoldElement A x) = x := by
  refine le_antisymm ?_ ?_
  · intro t ht
    rcases ht with ⟨t', ht', hU⟩
    have : treeFold A (treeUnfold A t') ∈ x.carrier := saturated_of_closed A x ht'
    have hft : treeFold A (treeUnfold A t) ∈ x.carrier := by
      rwa [hU] at this
    rcases treeFold_eq_or_pairBots A t with h | ⟨rfl, hf⟩
    · rwa [h] at hft
    · exact (mem_closed_pair_bots A x).1 (by rwa [hf] at hft)
  · intro t ht
    exact ⟨t, ht, rfl⟩

/-- **Factoid 8.1 at domain level.** `|T| ≃o |A + (T × T)|` via `treeUnfold`. -/
def treeDomainIso : (treeSystem A).Element ≃o (treeRhs A).Element where
  toFun := unfoldElement A
  invFun := foldElement A
  left_inv := foldElement_unfoldElement A
  right_inv := unfoldElement_foldElement A
  map_rel_iff' := by
    intro x₁ x₂
    constructor
    · intro h t ht
      have : treeUnfold A t ∈ (unfoldElement A x₁).carrier := ⟨t, ht, rfl⟩
      have : treeUnfold A t ∈ (unfoldElement A x₂).carrier := h this
      have : t ∈ (foldElement A (unfoldElement A x₂)).carrier := this
      rwa [foldElement_unfoldElement] at this
    · intro h s hs
      rcases hs with ⟨t, ht, rfl⟩
      exact ⟨t, h ht, rfl⟩

end ScottModels

-- Bridge — ScottModels.WorkedExampleSExpr (from ScottModels/WorkedExampleSExpr.lean)

/-!
# Worked example — S-expression / tree domain `T ≅ A + (T × T)`

Scott 1982 Factoid 8.1 (`treeSystem`) over the ℕ lower-bound atom system
(Factoid 2.4), walked through this package’s bridges: information system →
neighbourhood filters → ideal completion, plus identity approximable maps as
Scott-continuous maps (Factoid 4.6).
-/

namespace ScottModels

open Scott1982
open Scott1982.Constructive
open Scott1982.InfoSys
open Scott1982.InfoSys.ApproximableMap
open Order

/-! ## Atom system (Factoid 2.4, named) -/

/-- Scott’s ℕ lower-bound information system (Factoid 2.4), as a named definition. -/
def lowerBoundSystem : InfoSys ℕ where
  bot := 0
  Con := Set.univ
  Ent := Factoid24.lowerBoundEnt
  con_subset := by
    intro u v _ _
    exact Set.mem_univ v
  con_sing := by
    intro _
    exact Set.mem_univ _
  ent_con := by
    intro u a _
    exact Set.mem_univ _
  ent_bot := by
    intro u _
    exact Or.inl rfl
  ent_refl := by
    intro u a _ ha
    exact Or.inr ⟨a, ha, le_rfl⟩
  ent_trans := by
    intro u v c _ _ hvEnt huEnt
    rcases huEnt with rfl | ⟨n, hn, hcn⟩
    · exact Or.inl rfl
    · rcases hvEnt n hn with rfl | ⟨k, hk, hnk⟩
      · exact Or.inl (Nat.le_zero.mp hcn)
      · exact Or.inr ⟨k, hk, le_trans hcn hnk⟩

/-! ## S-expression system -/

/-- Tree / S-expression information system over lower-bound atoms. -/
abbrev SexSys : InfoSys (TreeToken ℕ) :=
  treeSystem lowerBoundSystem

/-- Official right-hand side `A + (T × T)`. -/
abbrev SexRhs : InfoSys (SumToken ℕ (ProdToken SexSys SexSys)) :=
  treeRhs lowerBoundSystem

theorem sexRhs_eq_sum_product :
    SexRhs = sumSystem lowerBoundSystem (productSystem SexSys SexSys) :=
  treeRhs_eq_sum_product lowerBoundSystem

/-- Unfolding tokens into the sum-of-product carrier (Factoid 8.1). -/
theorem sexUnfold_atom (n : ℕ) :
    treeUnfold lowerBoundSystem (.atom n) = SumToken.left n :=
  treeUnfold_atom lowerBoundSystem n

/-! ## Concrete finite elements -/

/-- Closure of a singleton atom token `{atom n}`. -/
noncomputable def sexAtom (n : ℕ) : SexSys.Element :=
  SexSys.closure {TreeToken.atom n} (SexSys.con_sing _)

theorem sexAtom_mem_self (n : ℕ) : TreeToken.atom n ∈ (sexAtom n).carrier :=
  SexSys.subset_closure (SexSys.con_sing _) (Finset.mem_singleton_self _)

/-! ## 1982 → 1980: basic-open neighbourhood filters -/

/-- `|T| ≃o` filters of basic opens `[u]`. -/
noncomputable abbrev sexNeighborhoodIso :
    SexSys.Element ≃o (InfoSysToNeighborhood.toNeighborhoodSystem SexSys).Element :=
  InfoSysToNeighborhood.domainOrderIso SexSys

/-! ## 1982 → ideal completion -/

/-- `|T| ≃o Ideal (FiniteElement T)`. -/
noncomputable abbrev sexIdealIso :
    SexSys.Element ≃o Ideal (InfoSysToIdealCompletion.FiniteElement SexSys) :=
  InfoSysToIdealCompletion.domainOrderIso SexSys

/-- Neighbourhood filters ≃ ideals of finite elements (constructive triangle). -/
noncomputable abbrev sexNeighborhoodIdealIso :=
  neighborhood_ideal_iso SexSys

/-! ## Domain equation at the level of domains (1982 constructions) -/

/--
Semantic factor: `|A + (T × T)| ≃o WithBot (|A| ⊕ (|T| × |T|))` via the generic
product and separated-sum isos. Not the fixed-point equation itself.
-/
noncomputable def sexRhsSemanticIso :
    WithBot (lowerBoundSystem.Element ⊕ (SexSys.Element × SexSys.Element)) ≃o
      SexRhs.Element :=
  let ιProd := InfoSysConstructions.productDomainIso SexSys SexSys
  let ιSum := InfoSysConstructions.sumDomainIso lowerBoundSystem (productSystem SexSys SexSys)
  let mid :=
    (OrderIso.refl lowerBoundSystem.Element).sumCongr ιProd |>.withBotCongr
  mid.trans ιSum

/--
**S-expression fixed-point equation.** `|T| ≃o |A + (T × T)|`, the order
isomorphism of `SexSys.Element` with `SexRhs.Element` induced by
`treeUnfold` / `treeFold` (`treeDomainIso`).
-/
noncomputable def sexDomainEquationIso :
    SexSys.Element ≃o SexRhs.Element :=
  treeDomainIso lowerBoundSystem

theorem sexDomainEquationIso_unfold (x : SexSys.Element) :
    (sexDomainEquationIso x).carrier =
      treeUnfold lowerBoundSystem '' x.carrier :=
  rfl

theorem sexDomainEquationIso_fold (y : SexRhs.Element) :
    (sexDomainEquationIso.symm y).carrier =
      treeUnfold lowerBoundSystem ⁻¹' y.carrier :=
  rfl

theorem exists_sexNeighborhoodIso :
    Nonempty (SexSys.Element ≃o
      (InfoSysToNeighborhood.toNeighborhoodSystem SexSys).Element) :=
  ⟨sexNeighborhoodIso⟩

theorem exists_sexIdealIso :
    Nonempty (SexSys.Element ≃o
      Ideal (InfoSysToIdealCompletion.FiniteElement SexSys)) :=
  ⟨sexIdealIso⟩

theorem exists_sexDomainEquationIso :
    Nonempty (SexSys.Element ≃o SexRhs.Element) :=
  ⟨sexDomainEquationIso⟩

/-! ## Morphisms: identity is Scott-continuous (Factoid 4.6) -/

/-- Identity approximable map on `T`, as a Scott-continuous endomap. -/
noncomputable abbrev sexIdScottContinuous : ScottContinuous SexSys SexSys :=
  (approximableMap_scottContinuous_equiv SexSys SexSys) (idMap SexSys)

theorem sexId_toElement (x : SexSys.Element) :
    sexIdScottContinuous.toFun x = x :=
  idMap_toElement SexSys x

end ScottModels


/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Definition83
import Scott1980.Neighborhood.Product

/-!
# Lecture VIII — Examples 8.4 (Scott 1981, PRG-19): `check`/`fade` and the two-point retraction

Scott's **EXAMPLES 8.4** is really three worked examples built from the *same* pair of
combinators `check`/`fade`. This file formalizes the first, headline example, labelled
**Example 8.4(a)** in `arxiv.md`; the other two (`strict`/`smash` as projections, Example 8.4(b))
are a separate, larger effort building on the same `check`/`fade` machinery — see the strategy note
on the 8.4(b) row of `arxiv.md`.

**Example 8.4(a).** If a system `D` is not trivial (there is some `u ∈ |D|` with `u ≠ ⊥`), then the
two-element system `O = {{0},{0,1}}` arises from a retraction on `D`. Scott's construction:

* `check : D → O` by `X check Y ↔ Y = {0,1} ∨ X ≠ Δ`. So `check(x) = ⊥_O` iff `x = ⊥_D`.
* `fade : O × D → D` (left to the reader) by `fade(t, x) = ⊥_D` if `t = ⊥_O`, else `x`.
* Fix any `u ≠ ⊥_D` and set `a(x) = fade(check(x), u)`. Then `a` is a retraction (not generally a
  projection) and the range of `a` is isomorphic to `O`.

## Formalization strategy

* `O` is built directly as a `NeighborhoodSystem (Fin 2)` with `mem = {{0},{0,1}}`.
* `check` is built as a literal `ApproximableMap D O` from Scott's formula (a `Prop`-valued
  relation, no case-splitting/decidability needed for the *definition* itself).
* `fade` is built via the two-variable bridge `ApproximableMap₂`/`ofMap₂` (Theorem 3.5): the
  two-variable relation `fade₂ : ApproximableMap₂ O D D` is `Z = Δ_D ∨ (X = {0} ∧ Y ⊆ Z)` — the
  disjunct `Z = Δ_D` is always a safe ("least informative") output regardless of the `O`-input,
  and `X = {0} ∧ Y ⊆ Z` is the "pass `x` through" branch.
* `a := fade.comp (paired check (constMap D u))` is Scott's literal composite. Unfolding it via
  `toElementMap_comp`/`toElementMap_paired`/`toElementMap_constMap`/the `ApproximableMap₂` bridge
  gives the clean closed form `mem_toElementMap_a`: `a(x) ∋ Z ↔ Z = Δ_D ∨ (x ≠ ⊥_D ∧ u ∋ Z)` — i.e.
  literally "`a(x) = ⊥_D` if `x = ⊥_D`, else `u`" (`a_bot`, `a_of_ne_bot`).
* From the closed form, `IsRetraction a` is immediate case analysis (`x = ⊥` is fixed at `⊥`;
  `x ≠ ⊥` lands on `u ≠ ⊥`, itself fixed).
* The fixed-point set is exactly `{⊥_D, u}`. Rather than characterizing it abstractly, the
  isomorphism to `O` is built *directly* and choice-freely from the same closed-form data:
  `fixOfO t` (for `t : O.Element`) is the filter `Z ↦ Z = Δ_D ∨ (t ∋ {0} ∧ u ∋ Z)` (the "plug `t`'s
  informativeness into `a`'s formula" filter — a genuine `Element`, no `if`/`Classical.choice` in
  the *data*), and `invOfFix y := check.toElementMap y`. The round-trip/order-preservation facts
  needed for the `OrderIso` are proved from the closed forms; a few individual `Prop`-level steps
  use classical case splits (`by_contra`/`push_neg`), consistent with the project's choice
  discipline (data stays choice-free; supporting propositions may use `Classical.choice`, flagged
  in the axiom audit recorded in `HANDOFF.md`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂

/-! ### The two-point domain `O = {{0},{0,1}}`. -/

theorem fin2_zero_subset_zero_one : ({0} : Set (Fin 2)) ⊆ ({0, 1} : Set (Fin 2)) := by
  intro x hx; simp only [Set.mem_singleton_iff] at hx; subst hx; simp

theorem fin2_zero_ne_zero_one : ({0} : Set (Fin 2)) ≠ ({0, 1} : Set (Fin 2)) := by
  intro h
  have h1 : (1 : Fin 2) ∈ ({0, 1} : Set (Fin 2)) := by simp
  rw [← h] at h1
  simp at h1

/-- **Example 8.4's two-point system `O = {{0},{0,1}}`.** Tokens `Δ = {0,1} : Fin 2`; the only
neighbourhoods are `{0}` (most informative) and `{0,1}` (the master, least informative). -/
def O : NeighborhoodSystem (Fin 2) where
  mem X := X = ({0} : Set (Fin 2)) ∨ X = ({0, 1} : Set (Fin 2))
  master := ({0, 1} : Set (Fin 2))
  master_mem := Or.inr rfl
  inter_mem := by
    rintro X Y Z (rfl | rfl) (rfl | rfl) _ _
    · exact Or.inl (Set.inter_self _)
    · exact Or.inl (Set.inter_eq_left.mpr fin2_zero_subset_zero_one)
    · exact Or.inl (Set.inter_eq_right.mpr fin2_zero_subset_zero_one)
    · exact Or.inr (Set.inter_self _)
  sub_master := by
    rintro X (rfl | rfl)
    · exact fin2_zero_subset_zero_one
    · exact subset_rfl

theorem O_master_eq : O.master = ({0, 1} : Set (Fin 2)) := rfl

@[simp] theorem O_mem_iff {X : Set (Fin 2)} :
    O.mem X ↔ X = ({0} : Set (Fin 2)) ∨ X = ({0, 1} : Set (Fin 2)) := Iff.rfl

theorem O_mem_zero : O.mem ({0} : Set (Fin 2)) := Or.inl rfl

/-- `O`'s top element `⊤ = ↑{0}` (the more informative of the two elements; `O.bot = ↑{0,1}` is the
generic `NeighborhoodSystem.bot`). -/
def Otop : O.Element := O.principal O_mem_zero

@[simp] theorem mem_Otop {Y : Set (Fin 2)} : Otop.mem Y ↔ O.mem Y ∧ ({0} : Set (Fin 2)) ⊆ Y :=
  Iff.rfl

theorem Otop_ne_Obot : Otop ≠ O.bot := by
  intro h
  have h1 : Otop.mem ({0} : Set (Fin 2)) := ⟨O_mem_zero, subset_rfl⟩
  rw [h, mem_bot, O_master_eq] at h1
  have h2 : (1 : Fin 2) ∈ ({0} : Set (Fin 2)) := by rw [h1]; simp
  simp at h2

/-! ### `check : D → O` (Scott's `X check Y ↔ Y = {0,1} ∨ X ≠ Δ`). -/

variable {α : Type*} {D : NeighborhoodSystem α}

/-- A non-bottom element of `D` always has *some* member neighbourhood other than the master.
(Classical: uses `by_contra`/`push_neg`, an allowed `Prop`-level use of `Classical.choice`.) -/
theorem exists_mem_ne_master_of_ne_bot {y : D.Element} (hy : y ≠ D.bot) :
    ∃ Z, y.mem Z ∧ Z ≠ D.master := by
  by_contra hcon
  push Not at hcon
  apply hy
  apply Element.ext
  intro Z
  rw [mem_bot]
  exact ⟨fun hZ => hcon Z hZ, fun hZ => hZ ▸ y.master_mem⟩

/-- **Example 8.4's `check` combinator.** `X check Y ↔ Y = {0,1} ∨ X ≠ Δ_D`. -/
def check : ApproximableMap D O where
  rel X Y := D.mem X ∧ O.mem Y ∧ (Y = ({0, 1} : Set (Fin 2)) ∨ X ≠ D.master)
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨D.master_mem, O.master_mem, Or.inl rfl⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hY1⟩ ⟨-, hY', hY1'⟩
    refine ⟨hX, ?_, ?_⟩
    · rcases hY with rfl | rfl <;> rcases hY' with rfl | rfl
      · exact Or.inl (Set.inter_self _)
      · exact Or.inl (Set.inter_eq_left.mpr fin2_zero_subset_zero_one)
      · exact Or.inl (Set.inter_eq_right.mpr fin2_zero_subset_zero_one)
      · exact Or.inr (Set.inter_self _)
    · rcases hY1 with h1 | hXne
      · rcases hY1' with h1' | hXne'
        · left; rw [h1, h1']; simp
        · right; exact hXne'
      · right; exact hXne
  mono := by
    rintro X X' Y Y' ⟨hX, hY, hY1⟩ hXX' hYY' hX' hY'
    refine ⟨hX', hY', ?_⟩
    rcases hY1 with hYeq | hXne
    · left
      subst hYeq
      rcases hY' with rfl | rfl
      · exfalso
        have h1 : (1 : Fin 2) ∈ ({0, 1} : Set (Fin 2)) := by simp
        have h2 : (1 : Fin 2) ∈ ({0} : Set (Fin 2)) := hYY' h1
        simp at h2
      · rfl
    · right
      intro hX'eq
      apply hXne
      exact Set.Subset.antisymm (D.sub_master hX) (hX'eq ▸ hXX')

@[simp] theorem check_rel {X : Set α} {Y : Set (Fin 2)} :
    (check : ApproximableMap D O).rel X Y ↔
      D.mem X ∧ O.mem Y ∧ (Y = ({0, 1} : Set (Fin 2)) ∨ X ≠ D.master) :=
  Iff.rfl

/-- The closed form of `check`'s elementwise action: `check(x) ∋ Y ↔ Y ∈ O ∧ (Y = {0,1} ∨ x ≠ ⊥)`.
So `check(x) = ⊥_O` when `x = ⊥_D`, and `check(x) = ⊤_O` otherwise. -/
theorem mem_toElementMap_check {x : D.Element} {Y : Set (Fin 2)} :
    (check.toElementMap x).mem Y ↔ O.mem Y ∧ (Y = ({0, 1} : Set (Fin 2)) ∨ x ≠ D.bot) := by
  rw [mem_toElementMap]
  constructor
  · rintro ⟨X, hxX, hXD, hYO, hcase⟩
    refine ⟨hYO, ?_⟩
    rcases hcase with h | hXne
    · exact Or.inl h
    · refine Or.inr fun hxbot => hXne ?_
      have hxX' : x.mem X := hxX
      rw [hxbot, mem_bot] at hxX'
      exact hxX'
  · rintro ⟨hYO, hYeq | hxne⟩
    · exact ⟨D.master, x.master_mem, D.master_mem, hYO, Or.inl hYeq⟩
    · obtain ⟨X, hxX, hXne⟩ := exists_mem_ne_master_of_ne_bot hxne
      exact ⟨X, hxX, x.sub hxX, hYO, Or.inr hXne⟩

/-! ### `fade : O × D → D` (Scott leaves the formula to the reader). -/

/-- **Example 8.4's `fade` combinator, as a two-variable map.** `X, Y fade Z ↔ Z = Δ_D ∨ (X = {0}
∧ Y ⊆ Z)`: the master is always a safe output; `X = {0}` (the informative `O`-input) lets `Y` pass
straight through. -/
def fade₂ : ApproximableMap₂ O D D where
  rel X Y Z := O.mem X ∧ D.mem Y ∧ D.mem Z ∧ (Z = D.master ∨ (X = ({0} : Set (Fin 2)) ∧ Y ⊆ Z))
  rel_dom₀ h := h.1
  rel_dom₁ h := h.2.1
  rel_cod h := h.2.2.1
  master_rel := ⟨O.master_mem, D.master_mem, D.master_mem, Or.inl rfl⟩
  inter_right := by
    rintro X Y Z Z' ⟨hX, hY, hZ, hZ1⟩ ⟨-, -, hZ', hZ1'⟩
    refine ⟨hX, hY, ?_, ?_⟩
    · rcases hZ1 with rfl | ⟨-, hYZ⟩
      · rwa [Set.inter_eq_right.mpr (D.sub_master hZ')]
      · rcases hZ1' with rfl | ⟨-, hYZ'⟩
        · rwa [Set.inter_eq_left.mpr (D.sub_master hZ)]
        · exact D.inter_mem hZ hZ' hY (Set.subset_inter hYZ hYZ')
    · rcases hZ1 with rfl | ⟨hXeq, hYZ⟩
      · rcases hZ1' with rfl | ⟨hXeq', hYZ'⟩
        · left; exact Set.inter_self _
        · right
          refine ⟨hXeq', ?_⟩
          rw [Set.inter_eq_right.mpr (D.sub_master hZ')]
          exact hYZ'
      · right
        refine ⟨hXeq, ?_⟩
        rcases hZ1' with rfl | ⟨-, hYZ'⟩
        · rw [Set.inter_eq_left.mpr (D.sub_master hZ)]
          exact hYZ
        · exact Set.subset_inter hYZ hYZ'
  mono := by
    rintro X X' Y Y' Z Z' ⟨hX, hY, hZ, hZ1⟩ hXX' hYY' hZZ' hX' hY' hZ'
    refine ⟨hX', hY', hZ', ?_⟩
    rcases hZ1 with rfl | ⟨hXeq, hYZ⟩
    · left; exact Set.Subset.antisymm (D.sub_master hZ') hZZ'
    · have hX'eq : X' = ({0} : Set (Fin 2)) := by
        rcases hX' with rfl | rfl
        · rfl
        · exfalso
          have h1 : (1 : Fin 2) ∈ ({0, 1} : Set (Fin 2)) := by simp
          have h2 : (1 : Fin 2) ∈ X := hXX' h1
          rw [hXeq] at h2
          simp at h2
      right
      exact ⟨hX'eq, hYY'.trans (hYZ.trans hZZ')⟩

/-- **Example 8.4's `fade` combinator**, packaged as a genuine `ApproximableMap (prod O D) D`
via the Theorem 3.5 bridge (`ofMap₂`). -/
def fade : ApproximableMap (prod O D) D := ofMap₂ fade₂

/-- The two-variable elementwise bridge for a general `ApproximableMap₂`, specialized to a pair. -/
theorem toElementMap_ofMap₂_pair {β γ δ : Type*} {V₀ : NeighborhoodSystem β}
    {V₁ : NeighborhoodSystem γ} {V₂ : NeighborhoodSystem δ} (f₂ : ApproximableMap₂ V₀ V₁ V₂)
    (p : V₀.Element) (q : V₁.Element) :
    (ofMap₂ f₂).toElementMap (pair p q) = f₂.toElementMap₂ p q := by
  have h := toElementMap₂_toMap₂ (ofMap₂ f₂) p q
  rw [toMap₂_ofMap₂] at h
  exact h.symm

/-- The closed form of `fade`'s elementwise action on a pair `⟨t, y⟩`: `fade(t,y) ∋ Z ↔ Z = Δ_D ∨
(t ∋ {0} ∧ y ∋ Z)`. -/
theorem mem_toElementMap₂_fade (t : O.Element) (y : D.Element) {Z : Set α} :
    (fade₂.toElementMap₂ t y).mem Z ↔
      D.mem Z ∧ (Z = D.master ∨ (t.mem ({0} : Set (Fin 2)) ∧ y.mem Z)) := by
  rw [mem_toElementMap₂]
  constructor
  · rintro ⟨X, Y, htX, hyY, hXO, hYD, hZD, hcase⟩
    refine ⟨hZD, ?_⟩
    rcases hcase with h | ⟨hXeq, hYZ⟩
    · exact Or.inl h
    · exact Or.inr ⟨hXeq ▸ htX, y.up_mem hyY hZD hYZ⟩
  · rintro ⟨hZD, hZeq | ⟨ht0, hyZ⟩⟩
    · exact ⟨O.master, D.master, t.master_mem, y.master_mem, O.master_mem, D.master_mem, hZD,
        Or.inl hZeq⟩
    · exact ⟨({0} : Set (Fin 2)), Z, ht0, hyZ, O_mem_zero, hZD, hZD, Or.inr ⟨rfl, subset_rfl⟩⟩

/-! ### `a(x) = fade(check(x), u)`: the retraction. -/

variable (u : D.Element) (hu : u ≠ D.bot)

/-- **Example 8.4(a)'s retraction** `a(x) = fade(check(x), u)`. -/
def a : ApproximableMap D D := fade.comp (paired check (constMap D u))

theorem mem_toElementMap_a {x : D.Element} {Z : Set α} :
    ((a u).toElementMap x).mem Z ↔ D.mem Z ∧ (Z = D.master ∨ (x ≠ D.bot ∧ u.mem Z)) := by
  show ((fade.comp (paired check (constMap D u))).toElementMap x).mem Z ↔ _
  rw [toElementMap_comp, toElementMap_paired, toElementMap_constMap]
  show (fade.toElementMap (pair (check.toElementMap x) u)).mem Z ↔ _
  rw [show fade = ofMap₂ fade₂ from rfl, toElementMap_ofMap₂_pair, mem_toElementMap₂_fade,
    mem_toElementMap_check]
  constructor
  · rintro ⟨hZD, hZeq | ⟨⟨-, hcase⟩, huZ⟩⟩
    · exact ⟨hZD, Or.inl hZeq⟩
    · rcases hcase with hYeq | hxne
      · exact absurd hYeq fin2_zero_ne_zero_one
      · exact ⟨hZD, Or.inr ⟨hxne, huZ⟩⟩
  · rintro ⟨hZD, hZeq | ⟨hxne, huZ⟩⟩
    · exact ⟨hZD, Or.inl hZeq⟩
    · exact ⟨hZD, Or.inr ⟨⟨O_mem_zero, Or.inr hxne⟩, huZ⟩⟩

theorem a_bot : (a u).toElementMap D.bot = D.bot := by
  apply Element.ext
  intro Z
  rw [mem_toElementMap_a, mem_bot]
  exact ⟨fun ⟨_, h⟩ => h.resolve_right (fun h' => h'.1 rfl) |>.symm ▸ rfl,
    fun h => ⟨h ▸ D.master_mem, Or.inl h⟩⟩

theorem a_of_ne_bot {x : D.Element} (hx : x ≠ D.bot) : (a u).toElementMap x = u := by
  apply Element.ext
  intro Z
  rw [mem_toElementMap_a]
  constructor
  · rintro ⟨-, hZeq | ⟨-, huZ⟩⟩
    · exact hZeq ▸ u.master_mem
    · exact huZ
  · intro huZ
    exact ⟨u.sub huZ, Or.inr ⟨hx, huZ⟩⟩

/-- **Example 8.4(a) (Scott 1981, PRG-19).** `a` is a retraction. -/
theorem isRetraction_a (hu : u ≠ D.bot) : IsRetraction (a u) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp]
  by_cases hx : x = D.bot
  · subst hx; rw [a_bot, a_bot]
  · rw [a_of_ne_bot u hx, a_of_ne_bot u hu]

/-! ### The range of `a` is isomorphic to `O`. -/

/-- The `D`-element corresponding to `t : O.Element` under `a`'s formula: `Z ↦ Z = Δ_D ∨ (t ∋ {0}
∧ u ∋ Z)`. This is a genuine `Element` (filter), built with no case-split on `t`. -/
def fixOfO (t : O.Element) : D.Element where
  mem Z := D.mem Z ∧ (Z = D.master ∨ (t.mem ({0} : Set (Fin 2)) ∧ u.mem Z))
  sub h := h.1
  master_mem := ⟨D.master_mem, Or.inl rfl⟩
  inter_mem := by
    rintro Z Z' ⟨hZ, hZ1⟩ ⟨hZ', hZ1'⟩
    refine ⟨?_, ?_⟩
    · rcases hZ1 with rfl | ⟨-, huZ⟩
      · rwa [Set.inter_eq_right.mpr (D.sub_master hZ')]
      · rcases hZ1' with rfl | ⟨-, huZ'⟩
        · rwa [Set.inter_eq_left.mpr (D.sub_master hZ)]
        · exact u.sub (u.inter_mem huZ huZ')
    · rcases hZ1 with rfl | ⟨ht, huZ⟩
      · rcases hZ1' with rfl | ⟨ht', huZ'⟩
        · left; exact Set.inter_self _
        · right
          refine ⟨ht', ?_⟩
          rw [Set.inter_eq_right.mpr (D.sub_master hZ')]
          exact huZ'
      · right
        refine ⟨ht, ?_⟩
        rcases hZ1' with rfl | ⟨-, huZ'⟩
        · rw [Set.inter_eq_left.mpr (D.sub_master hZ)]
          exact huZ
        · exact u.inter_mem huZ huZ'
  up_mem := by
    rintro Z Z' ⟨hZ, hZ1⟩ hZ'D hZZ'
    refine ⟨hZ'D, ?_⟩
    rcases hZ1 with rfl | ⟨ht, huZ⟩
    · left; exact Set.Subset.antisymm (D.sub_master hZ'D) hZZ'
    · right; exact ⟨ht, u.up_mem huZ hZ'D hZZ'⟩

@[simp] theorem mem_fixOfO {t : O.Element} {Z : Set α} :
    (fixOfO u t).mem Z ↔ D.mem Z ∧ (Z = D.master ∨ (t.mem ({0} : Set (Fin 2)) ∧ u.mem Z)) :=
  Iff.rfl

theorem fixOfO_ne_bot_iff (hu : u ≠ D.bot) {t : O.Element} :
    fixOfO u t ≠ D.bot ↔ t.mem ({0} : Set (Fin 2)) := by
  constructor
  · intro hne
    by_contra ht0
    apply hne
    apply Element.ext
    intro Z
    rw [mem_fixOfO, mem_bot]
    constructor
    · rintro ⟨-, rfl | ⟨ht0', -⟩⟩
      · rfl
      · exact absurd ht0' ht0
    · rintro rfl
      exact ⟨D.master_mem, Or.inl rfl⟩
  · intro ht0 hbot
    obtain ⟨Z, huZ, hZne⟩ := exists_mem_ne_master_of_ne_bot hu
    have : (fixOfO u t).mem Z := ⟨u.sub huZ, Or.inr ⟨ht0, huZ⟩⟩
    rw [hbot, mem_bot] at this
    exact hZne this

theorem toElementMap_a_fixOfO (hu : u ≠ D.bot) (t : O.Element) :
    (a u).toElementMap (fixOfO u t) = fixOfO u t := by
  apply Element.ext
  intro Z
  rw [mem_toElementMap_a, mem_fixOfO, fixOfO_ne_bot_iff u hu]

theorem check_toElementMap_fixOfO (hu : u ≠ D.bot) (t : O.Element) :
    check.toElementMap (fixOfO u t) = t := by
  apply Element.ext
  intro Y
  rw [mem_toElementMap_check, fixOfO_ne_bot_iff u hu]
  constructor
  · rintro ⟨hYO, hYeq | ht0⟩
    · rw [hYeq, ← O_master_eq]; exact t.master_mem
    · rcases hYO with rfl | rfl
      · exact ht0
      · rw [← O_master_eq]; exact t.master_mem
  · intro htY
    have hYO : O.mem Y := t.sub htY
    refine ⟨hYO, ?_⟩
    rcases O_mem_iff.mp hYO with rfl | rfl
    · exact Or.inr htY
    · exact Or.inl rfl

/-- `fixOfO` and `check.toElementMap` intertwine `a` and the identity on `D`: applying `fixOfO`
after `check.toElementMap` recovers `a` itself. -/
theorem fixOfO_check_toElementMap (x : D.Element) :
    fixOfO u (check.toElementMap x) = (a u).toElementMap x := by
  apply Element.ext
  intro Z
  rw [mem_fixOfO, mem_toElementMap_a]
  have hcheck : (check.toElementMap x).mem ({0} : Set (Fin 2)) ↔ x ≠ D.bot := by
    rw [mem_toElementMap_check]
    constructor
    · rintro ⟨-, h | h⟩
      · exact absurd h fin2_zero_ne_zero_one
      · exact h
    · intro h; exact ⟨O_mem_zero, Or.inr h⟩
  rw [hcheck]

theorem O_le_iff {t t' : O.Element} :
    t ≤ t' ↔ (t.mem ({0} : Set (Fin 2)) → t'.mem ({0} : Set (Fin 2))) := by
  constructor
  · intro h; exact h _
  · intro h Y hY
    rcases O_mem_iff.mp (t.sub hY) with rfl | rfl
    · exact h hY
    · exact t'.master_mem

theorem fixOfO_mono {t t' : O.Element} (h : t ≤ t') : fixOfO u t ≤ fixOfO u t' := by
  intro Z hZ
  rw [mem_fixOfO] at hZ ⊢
  obtain ⟨hZD, hZeq | ⟨ht0, huZ⟩⟩ := hZ
  · exact ⟨hZD, Or.inl hZeq⟩
  · exact ⟨hZD, Or.inr ⟨O_le_iff.mp h ht0, huZ⟩⟩

/-- **Example 8.4(a) (Scott 1981, PRG-19), packaged.** The range (fixed-point set) of `a` is
order-isomorphic to `O`. -/
def fixIso (hu : u ≠ D.bot) : O.Element ≃o {y : D.Element // (a u).toElementMap y = y} where
  toFun t := ⟨fixOfO u t, toElementMap_a_fixOfO u hu t⟩
  invFun y := check.toElementMap y.1
  left_inv t := check_toElementMap_fixOfO u hu t
  right_inv y := by
    apply Subtype.ext
    show fixOfO u (check.toElementMap y.1) = y.1
    rw [fixOfO_check_toElementMap, y.2]
  map_rel_iff' := by
    intro t t'
    show fixOfO u t ≤ fixOfO u t' ↔ t ≤ t'
    constructor
    · intro h
      have := toElementMap_mono check h
      rwa [check_toElementMap_fixOfO u hu, check_toElementMap_fixOfO u hu] at this
    · exact fixOfO_mono u

/-- **Example 8.4(a) (Scott 1981, PRG-19), final statement.** If `D` is not trivial (`u ≠ ⊥`),
`a(x) = fade(check(x), u)` is a retraction on `D` whose range is isomorphic to `O = {{0},{0,1}}`. -/
theorem example84a (hu : u ≠ D.bot) :
    IsRetraction (a u) ∧ Nonempty (O.Element ≃o {y : D.Element // (a u).toElementMap y = y}) :=
  ⟨isRetraction_a u hu, ⟨fixIso u hu⟩⟩

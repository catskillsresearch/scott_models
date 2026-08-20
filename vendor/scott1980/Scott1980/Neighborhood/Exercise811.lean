/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Theorem85
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Exercise 8.11 (Scott 1981, PRG-19, Lecture VIII)

> Let `Q` be the set of rational numbers and define a neighbourhood system by the equation
> `R = {[0,r) ∣ r ∈ Q and 0 < r ≤ 1}`. Show that the following defines an approximable map
> `a : R → R`: `[0,r) a [0,s) iff r < s or r = s = 1`. Show in addition that `a` is a projection
> where the fixed-point set of `a` is in a one-one correspondence with the real numbers between
> `0` and `1` inclusive. (Hint: recall Dedekind cuts and show `≤` matches `⊑`.) Conclude that `a`
> is *not* finitary. (Hint: aside from `1`, there are no finite elements for `{x ∣ x = a(x)}`.)

## Contents

* `R` — the chain neighbourhood system `{[0,r) ∣ 0 < r ≤ 1}` over `ℚ` (`ofNestedOrDisjoint`, since
  the intervals are literally nested by `r`).
* `a` — Scott's map (`aRel`), shown approximable (`Exercise811.a`).
* `isRetraction_a` / `isProjection_a` — the two closure facts Scott asks for.
* `fixOrderIso` — the order isomorphism `Fix(a) ≃o Set.Icc (0:ℝ) 1` realizing Scott's Dedekind-cut
  correspondence (`c := 1 - t` is the "cut point", `t` the represented real, chosen so that `≤`
  literally matches `⊑`, i.e. `fixOrderIso` is monotone both ways by construction).
* `not_isFinitary_a` — `a` is *not* finitary: if it were, `Fix(a) ≃o Set.Icc (0:ℝ) 1` would transport
  to *some* domain `F`'s element poset, but every non-bottom element of `Set.Icc (0:ℝ) 1` fails
  Theorem 8.5's algebraic-compactness test (only `0`, matching Scott's lone finite element `⊥`, is
  compact) — contradicting that `F` (being a domain) has a non-bottom *principal* element as soon as
  it has more than one element.

Everything here inherits the ambient `Classical.choice` taint of Mathlib's `ℚ`/`ℝ` order
instances (as with `Definition87.lean`'s `𝒰`); no *further* choice is introduced beyond that and
one genuine classical case split (`by_contra`) used for the compactness contradiction.
-/

namespace Scott1980.Neighborhood.Exercise811

open NeighborhoodSystem ApproximableMap

/-! ### The chain neighbourhood system `R = {[0,r) ∣ 0 < r ≤ 1}` -/

/-- **Exercise 8.11's `R`.** The neighbourhoods are exactly the half-open rational intervals
`[0,r)` for `0 < r ≤ 1`, nested by `r` (`Ico0_subset_or_supset`), so `ofNestedOrDisjoint` applies
directly with no disjoint case ever needed. -/
def R : NeighborhoodSystem ℚ :=
  NeighborhoodSystem.ofNestedOrDisjoint
    (mem := fun X => ∃ r : ℚ, 0 < r ∧ r ≤ 1 ∧ X = Set.Ico (0 : ℚ) r)
    (master := Set.Ico (0 : ℚ) 1)
    (master_mem := ⟨1, one_pos, le_refl 1, rfl⟩)
    (hnd := by
      rintro X Y ⟨r, hr0, hr1, rfl⟩ ⟨s, hs0, hs1, rfl⟩
      rcases le_total r s with h | h
      · exact Or.inl (Set.Ico_subset_Ico le_rfl h)
      · exact Or.inr (Or.inl (Set.Ico_subset_Ico le_rfl h)))
    (sub_master := by
      rintro X ⟨r, hr0, hr1, rfl⟩
      exact Set.Ico_subset_Ico le_rfl hr1)

@[simp] theorem R_mem_iff {X : Set ℚ} :
    R.mem X ↔ ∃ r : ℚ, 0 < r ∧ r ≤ 1 ∧ X = Set.Ico (0 : ℚ) r := Iff.rfl

@[simp] theorem R_master : R.master = Set.Ico (0 : ℚ) 1 := rfl

/-- The parametrization `r ↦ [0,r)` is injective on positive `r`: if `r < s` then `r` itself
witnesses the difference (`r ∈ [0,s)` but `r ∉ [0,r)`). -/
theorem Ico0_inj {r s : ℚ} (hr : 0 < r) (hs : 0 < s)
    (h : Set.Ico (0 : ℚ) r = Set.Ico (0 : ℚ) s) : r = s := by
  rcases lt_trichotomy r s with hlt | heq | hgt
  · have hmem : r ∈ Set.Ico (0 : ℚ) s := ⟨hr.le, hlt⟩
    rw [← h] at hmem
    exact absurd hmem.2 (lt_irrefl r)
  · exact heq
  · have hmem : s ∈ Set.Ico (0 : ℚ) r := ⟨hs.le, hgt⟩
    rw [h] at hmem
    exact absurd hmem.2 (lt_irrefl s)

/-- If `[0,p) ⊆ [0,q)` and `p > 0`, then `p ≤ q`. (The converse direction of nestedness; note `q > 0`
is *derived*, from `0 ∈ [0,p) ⊆ [0,q)`, not assumed.) -/
theorem Ico0_le_of_subset {p q : ℚ} (hp : 0 < p)
    (hsub : Set.Ico (0 : ℚ) p ⊆ Set.Ico (0 : ℚ) q) : p ≤ q := by
  have hq : (0 : ℚ) < q := (hsub ⟨le_refl 0, hp⟩).2
  by_contra hlt
  rw [not_le] at hlt
  exact absurd (hsub ⟨hq.le, hlt⟩).2 (lt_irrefl q)

/-- Two `[0,·)`-intervals intersect to a third, with the endpoint `min r s`. -/
theorem Ico0_inter (r s : ℚ) :
    Set.Ico (0 : ℚ) r ∩ Set.Ico (0 : ℚ) s = Set.Ico (0 : ℚ) (min r s) := by
  rw [Set.Ico_inter_Ico, sup_idem]

/-! ### Scott's map `a : R → R` -/

/-- Scott's relation: `[0,r) a [0,s)` iff `r < s` or `r = s = 1`. -/
def aRel (X Y : Set ℚ) : Prop :=
  ∃ r s : ℚ, 0 < r ∧ r ≤ 1 ∧ 0 < s ∧ s ≤ 1 ∧
    X = Set.Ico (0 : ℚ) r ∧ Y = Set.Ico (0 : ℚ) s ∧ (r < s ∨ (r = 1 ∧ s = 1))

/-- `aRel` unwound at concrete endpoints: exactly Scott's displayed condition. -/
theorem aRel_iff {r s : ℚ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    aRel (Set.Ico (0 : ℚ) r) (Set.Ico (0 : ℚ) s) ↔ (r < s ∨ (r = 1 ∧ s = 1)) := by
  constructor
  · rintro ⟨r', s', hr0', hr1', hs0', hs1', hXr, hXs, hcond⟩
    rw [Ico0_inj hr0 hr0' hXr, Ico0_inj hs0 hs0' hXs]
    exact hcond
  · intro h
    exact ⟨r, s, hr0, hr1, hs0, hs1, rfl, rfl, h⟩

theorem aRel_le {r s : ℚ} (h : r < s ∨ (r = 1 ∧ s = 1)) : r ≤ s := by
  rcases h with h | ⟨rfl, rfl⟩
  · exact h.le
  · exact le_rfl

/-- **Scott's combinator law**: if `X a Y` and `X a Y'` then `X a (Y ∩ Y')`, unwound to endpoints. -/
theorem aRel_combine {r s s' : ℚ} (hs1 : s ≤ 1) (hs1' : s' ≤ 1)
    (h1 : r < s ∨ (r = 1 ∧ s = 1)) (h2 : r < s' ∨ (r = 1 ∧ s' = 1)) :
    r < min s s' ∨ (r = 1 ∧ min s s' = 1) := by
  rcases h1 with h1 | ⟨rfl, rfl⟩
  · rcases h2 with h2 | ⟨rfl, rfl⟩
    · exact Or.inl (lt_min h1 h2)
    · exact absurd (h1.trans_le hs1) (lt_irrefl _)
  · rcases h2 with h2 | ⟨-, rfl⟩
    · exact absurd (h2.trans_le hs1') (lt_irrefl _)
    · exact Or.inr ⟨rfl, min_self 1⟩

/-- **Exercise 8.11 (first part).** `aRel` defines an approximable map `a : R → R`. -/
def a : ApproximableMap R R where
  rel := aRel
  rel_dom := fun ⟨r, _, hr0, hr1, _, _, hXr, _, _⟩ => ⟨r, hr0, hr1, hXr⟩
  rel_cod := fun ⟨_, s, _, _, hs0, hs1, _, hYs, _⟩ => ⟨s, hs0, hs1, hYs⟩
  master_rel := ⟨1, 1, one_pos, le_rfl, one_pos, le_rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩
  inter_right := by
    rintro X Y Y' ⟨r, s, hr0, hr1, hs0, hs1, rfl, rfl, hcond⟩
      ⟨r', s', hr0', hr1', hs0', hs1', hXr', rfl, hcond'⟩
    have hrr' : r = r' := Ico0_inj hr0 hr0' hXr'
    subst hrr'
    rw [Set.Ico_inter_Ico, sup_idem]
    exact ⟨r, min s s', hr0, hr1, lt_min hs0 hs0', (min_le_left s s').trans hs1, rfl, rfl,
      aRel_combine hs1 hs1' hcond hcond'⟩
  mono := by
    rintro X X' Y Y' ⟨r, s, hr0, hr1, hs0, hs1, rfl, rfl, hcond⟩ hX'X hYY'
      ⟨r', hr0', hr1', rfl⟩ ⟨s', hs0', hs1', rfl⟩
    have hr'r : r' ≤ r := Ico0_le_of_subset hr0' hX'X
    have hss' : s ≤ s' := Ico0_le_of_subset hs0 hYY'
    refine ⟨r', s', hr0', hr1', hs0', hs1', rfl, rfl, ?_⟩
    rcases hcond with hlt | ⟨rfl, rfl⟩
    · exact Or.inl (hr'r.trans_lt (hlt.trans_le hss'))
    · rcases hr1'.lt_or_eq with h | h
      · exact Or.inl (h.trans_le hss')
      · exact Or.inr ⟨h, le_antisymm hs1' hss'⟩

@[simp] theorem a_rel {X Y : Set ℚ} : a.rel X Y ↔ aRel X Y := Iff.rfl

/-! ### `a` is a retraction and a projection -/

/-- **Exercise 8.11 (second part, retraction).** `a ∘ a = a`. -/
theorem isRetraction_a : IsRetraction a := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨Y, ⟨r, s, hr0, hr1, hs0, hs1, rfl, rfl, hcond1⟩,
      ⟨s', t, hs0', hs1', ht0, ht1, hYs', rfl, hcond2⟩⟩
    have hss' : s = s' := Ico0_inj hs0 hs0' hYs'
    subst hss'
    refine ⟨r, t, hr0, hr1, ht0, ht1, rfl, rfl, ?_⟩
    rcases hcond1 with h1 | ⟨rfl, rfl⟩
    · rcases hcond2 with h2 | ⟨rfl, rfl⟩
      · exact Or.inl (h1.trans h2)
      · exact Or.inl h1
    · rcases hcond2 with h2 | ⟨-, rfl⟩
      · exact absurd (h2.trans_le ht1) (lt_irrefl _)
      · exact Or.inr ⟨rfl, rfl⟩
  · rintro ⟨r, t, hr0, hr1, ht0, ht1, rfl, rfl, hcond⟩
    rcases hcond with h | ⟨rfl, rfl⟩
    · obtain ⟨s, hrs, hst⟩ := exists_between h
      have hs0 : 0 < s := hr0.trans hrs
      have hs1 : s ≤ 1 := (hst.trans_le ht1).le
      exact ⟨Set.Ico 0 s, ⟨r, s, hr0, hr1, hs0, hs1, rfl, rfl, Or.inl hrs⟩,
        ⟨s, t, hs0, hs1, ht0, ht1, rfl, rfl, Or.inl hst⟩⟩
    · exact ⟨Set.Ico 0 1, ⟨1, 1, one_pos, le_rfl, one_pos, le_rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩,
        ⟨1, 1, one_pos, le_rfl, one_pos, le_rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩⟩

/-- **Exercise 8.11 (second part, projection).** `a ⊑ I_R`. -/
theorem isProjection_a : IsProjection a := by
  refine ⟨isRetraction_a, ?_⟩
  rintro X Y ⟨r, s, hr0, hr1, hs0, hs1, rfl, rfl, hcond⟩
  exact ⟨⟨r, hr0, hr1, rfl⟩, ⟨s, hs0, hs1, rfl⟩, Set.Ico_subset_Ico le_rfl (aRel_le hcond)⟩

/-! ### The fixed-point set of `a`, via "up-sets" `U : ℚ → Prop` -/

/-- `R`'s elements are entirely determined by their membership at the endpoints `[0,r)`: two
elements agreeing on every `r` agree everywhere (any other `X` with `x.mem X` is forced, by
`x.sub`, to already be some `[0,r)`). -/
theorem Element.ext_U {x y : R.Element} (h : ∀ r : ℚ, x.mem (Set.Ico 0 r) ↔ y.mem (Set.Ico 0 r)) :
    x = y := by
  apply NeighborhoodSystem.Element.ext
  intro X
  constructor
  · intro hx
    obtain ⟨r, _, _, rfl⟩ := x.sub hx
    exact (h r).mp hx
  · intro hy
    obtain ⟨r, _, _, rfl⟩ := y.sub hy
    exact (h r).mpr hy

/-- **Building an `R.Element` from an "up-set" predicate `U`.** `U` must contain `1`, be bounded
to `(0,1]`, and be upward closed within `(0,1]` — exactly Definition 1.6's filter conditions,
transported along the bijection `r ↦ [0,r)`. -/
def mkElement (U : ℚ → Prop) (hU1 : U 1) (hUpos : ∀ r, U r → 0 < r) (hUle1 : ∀ r, U r → r ≤ 1)
    (hUup : ∀ r s, U r → r ≤ s → s ≤ 1 → U s) : R.Element where
  mem X := ∃ r, U r ∧ X = Set.Ico (0 : ℚ) r
  sub := fun ⟨r, hr, hXr⟩ => ⟨r, hUpos r hr, hUle1 r hr, hXr⟩
  master_mem := ⟨1, hU1, rfl⟩
  inter_mem := by
    rintro X Y ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩
    rw [Ico0_inter]
    rcases le_total r s with h | h
    · exact ⟨r, hr, by rw [min_eq_left h]⟩
    · exact ⟨s, hs, by rw [min_eq_right h]⟩
  up_mem := by
    rintro X Y ⟨r, hr, rfl⟩ hY hsub
    obtain ⟨s, hs0, hs1, rfl⟩ := hY
    exact ⟨s, hUup r s hr (Ico0_le_of_subset (hUpos r hr) hsub) hs1, rfl⟩

@[simp] theorem mkElement_mem {U hU1 hUpos hUle1 hUup} {X : Set ℚ} :
    (mkElement U hU1 hUpos hUle1 hUup).mem X ↔ ∃ r, U r ∧ X = Set.Ico (0 : ℚ) r := Iff.rfl

/-- Any `R`-neighbourhood `[0,s)` forces `0 < s ≤ 1` (even though `R_mem_iff` phrases `R.mem X` as
an existential over a *possibly different* endpoint, injectivity pins it down to `s` itself). -/
theorem R_mem_Ico0 {s : ℚ} (h : R.mem (Set.Ico (0 : ℚ) s)) : 0 < s ∧ s ≤ 1 := by
  obtain ⟨r, hr0, hr1, heq⟩ := h
  have hsne : (Set.Ico (0 : ℚ) s).Nonempty := heq ▸ ⟨0, le_refl 0, hr0⟩
  obtain ⟨x, hx0, hxs⟩ := hsne
  have hs0 : 0 < s := lt_of_le_of_lt hx0 hxs
  have hsr : s = r := Ico0_inj hs0 hr0 heq
  exact ⟨hs0, hsr ▸ hr1⟩

/-! ### The correspondence with `Set.Icc (0 : ℝ) 1` -/

/-- **The Dedekind-cut up-set for `t ∈ [0,1]`.** `cutU t r` holds at `r ≤ 1` with `1 - t < r`
(strictly), or at the single endpoint `r = 1`; `1 - t` is Scott's "cut point" `c`, chosen so the
represented real `t` increases exactly as the up-set does (Scott's hint: `⊆` matches `≤`). -/
def cutU (t : ℝ) (r : ℚ) : Prop := r ≤ 1 ∧ ((1 - t : ℝ) < (r : ℝ) ∨ r = 1)

theorem cutU_pos {t : ℝ} (ht1 : t ≤ 1) {r : ℚ} (h : cutU t r) : 0 < r := by
  rcases h.2 with h2 | rfl
  · have hc : (0 : ℝ) ≤ 1 - t := by linarith
    exact_mod_cast lt_of_le_of_lt hc h2
  · norm_num

theorem cutU_le1 {t : ℝ} {r : ℚ} (h : cutU t r) : r ≤ 1 := h.1

theorem cutU_one {t : ℝ} : cutU t 1 := ⟨le_rfl, Or.inr rfl⟩

theorem cutU_up {r s : ℚ} {t : ℝ} (h : cutU t r) (hrs : r ≤ s) (hs1 : s ≤ 1) : cutU t s := by
  refine ⟨hs1, ?_⟩
  rcases h.2 with h2 | rfl
  · left
    have hcast : (r : ℝ) ≤ (s : ℝ) := by exact_mod_cast hrs
    linarith
  · exact Or.inr (le_antisymm hs1 hrs)

/-- The fixed point of `a` corresponding to `t ∈ [0,1]` (Scott's Dedekind cut). -/
def cutElt (t : ℝ) (ht1 : t ≤ 1) : R.Element :=
  mkElement (cutU t) cutU_one (fun _ h => cutU_pos ht1 h) (fun _ h => cutU_le1 h)
    (fun _ _ h hrs hs1 => cutU_up h hrs hs1)

@[simp] theorem cutElt_mem {t : ℝ} {ht1 : t ≤ 1} {r : ℚ} :
    (cutElt t ht1).mem (Set.Ico 0 r) ↔ cutU t r := by
  simp only [cutElt, mkElement_mem]
  constructor
  · rintro ⟨r', hr', heq⟩
    have hr'0 := cutU_pos ht1 hr'
    have hne : (Set.Ico (0 : ℚ) r).Nonempty := heq ▸ ⟨0, le_refl 0, hr'0⟩
    obtain ⟨x, hx0, hxr⟩ := hne
    have hr0 : 0 < r := lt_of_le_of_lt hx0 hxr
    rwa [Ico0_inj hr0 hr'0 heq]
  · exact fun h => ⟨r, h, rfl⟩

/-- **`cutElt t` is a fixed point of `a`**, for every `t ∈ [0,1]`: this is exactly the "open cut"
computation — `a` shifts `[0,r)` strictly forward, so `s` re-enters the up-set from below iff some
smaller `r` was already in it, i.e. iff `1 - t < s` (density of `ℚ` supplies the witness `r`). -/
theorem toElementMap_cutElt {t : ℝ} (ht1 : t ≤ 1) :
    a.toElementMap (cutElt t ht1) = cutElt t ht1 := by
  apply Element.ext_U
  intro s
  simp only [mem_toElementMap, a_rel, cutElt_mem]
  constructor
  · rintro ⟨X, hX, hrel⟩
    obtain ⟨r, hUr, rfl⟩ := hX
    have hs01 := R_mem_Ico0 (a.rel_cod (a_rel.mpr hrel))
    rw [aRel_iff (cutU_pos ht1 hUr) (cutU_le1 hUr) hs01.1 hs01.2] at hrel
    rcases hrel with hlt | ⟨hr1, hs1⟩
    · rcases hUr.2 with hc | hr1
      · exact ⟨hs01.2, Or.inl (lt_trans hc (by exact_mod_cast hlt))⟩
      · exact absurd (hr1 ▸ hlt : (1:ℚ) < s) (not_lt.mpr hs01.2)
    · exact ⟨hs01.2, Or.inr hs1⟩
  · intro hs
    rcases hs.2 with hc | rfl
    · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hc
      have hr0 : 0 < r := by
        have : (0:ℝ) ≤ 1 - t := by linarith
        exact_mod_cast lt_of_le_of_lt this hr1
      have hrle1 : r ≤ 1 := by
        have : (r:ℝ) < (s:ℝ) := hr2
        have hrs : r < s := by exact_mod_cast this
        exact hrs.le.trans hs.1
      exact ⟨Set.Ico 0 r, ⟨r, ⟨hrle1, Or.inl hr1⟩, rfl⟩, r, s, hr0, hrle1, cutU_pos ht1 hs,
        cutU_le1 hs, rfl, rfl, Or.inl (by exact_mod_cast hr2)⟩
    · exact ⟨Set.Ico 0 1, ⟨1, cutU_one, rfl⟩, 1, 1, one_pos, le_rfl, one_pos, le_rfl, rfl, rfl,
        Or.inr ⟨rfl, rfl⟩⟩

/-- Domain order reduces to a statement about `mem` at the endpoints `[0,r)` alone. -/
theorem le_iff_U {x y : R.Element} :
    x ≤ y ↔ ∀ r : ℚ, x.mem (Set.Ico 0 r) → y.mem (Set.Ico 0 r) :=
  ⟨fun h r => h (Set.Ico 0 r), fun h X hX => by
    obtain ⟨r, _, _, rfl⟩ := x.sub hX; exact h r hX⟩

/-- `cutU` is monotone in `t`: raising `t` only weakens the cut point `1 - t`, so it only
*enlarges* the up-set. -/
theorem cutU_mono {t t' : ℝ} (htt' : t ≤ t') {r : ℚ} (h : cutU t r) : cutU t' r := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with hc | rfl
  · exact Or.inl (by linarith)
  · exact Or.inr rfl

/-- **Scott's hint made precise:** `⊆` (the up-sets, i.e. `⊑` on `R.Element`) matches `≤` (on the
represented reals) — `cutElt` is order-preserving *both ways*. -/
theorem cutElt_le_iff {t t' : ℝ} (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ht0' : 0 ≤ t') (ht1' : t' ≤ 1) :
    cutElt t ht1 ≤ cutElt t' ht1' ↔ t ≤ t' := by
  rw [le_iff_U]
  simp only [cutElt_mem]
  constructor
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show (1 - t : ℝ) < 1 - t' by linarith)
    have hrle1 : r ≤ 1 := by
      have : (r : ℝ) < 1 := by linarith
      exact_mod_cast this.le
    have hcutt' : cutU t' r := h r ⟨hrle1, Or.inl hr1⟩
    rcases hcutt'.2 with hc' | hreq
    · linarith
    · rw [hreq] at hr2; norm_num at hr2; linarith
  · exact fun htt' r hr => cutU_mono htt' hr

/-- The (real-valued) image of `x`'s up-set: `{(r:ℝ) ∣ x.mem [0,r)}`. -/
def cutS (x : R.Element) : Set ℝ := (fun r : ℚ => (r : ℝ)) '' {r | x.mem (Set.Ico 0 r)}

theorem cutS_nonempty (x : R.Element) : (cutS x).Nonempty :=
  ⟨1, 1, show x.mem (Set.Ico (0 : ℚ) 1) by rw [← R_master]; exact x.master_mem, by norm_num⟩

theorem cutS_bddBelow (x : R.Element) : BddBelow (cutS x) := by
  refine ⟨0, ?_⟩
  rintro y ⟨r, hr, rfl⟩
  dsimp only
  exact_mod_cast (R_mem_Ico0 (x.sub hr)).1.le

/-- **The canonical Dedekind cut point** `1 - c` of a fixed element `x`, `c := sInf (cutS x)`. -/
noncomputable def cutPoint (x : R.Element) : ℝ := 1 - sInf (cutS x)

theorem cutPoint_nonneg (x : R.Element) : 0 ≤ cutPoint x := by
  have hmem1 : x.mem (Set.Ico (0 : ℚ) 1) := by rw [← R_master]; exact x.master_mem
  have hc1 : sInf (cutS x) ≤ 1 := csInf_le (cutS_bddBelow x) ⟨1, hmem1, by norm_num⟩
  unfold cutPoint; linarith

theorem cutPoint_le_one (x : R.Element) : cutPoint x ≤ 1 := by
  have hc0 : (0:ℝ) ≤ sInf (cutS x) := le_csInf (cutS_nonempty x)
    (by rintro y ⟨r, hr, rfl⟩; dsimp only; exact_mod_cast (R_mem_Ico0 (x.sub hr)).1.le)
  unfold cutPoint; linarith

/-- **Surjectivity**: every fixed point of `a` equals `cutElt (cutPoint x) _`; the fixed-point
equation supplies exactly the "openness" (no minimum, aside from `r = 1`) that makes this work. -/
theorem cutElt_cutPoint {x : R.Element} (hfix : a.toElementMap x = x) :
    cutElt (cutPoint x) (cutPoint_le_one x) = x := by
  have hSne := cutS_nonempty x
  have hSbdd := cutS_bddBelow x
  apply Element.ext_U
  intro r
  rw [cutElt_mem]
  have hcU : cutU (cutPoint x) r ↔ (r ≤ 1 ∧ (sInf (cutS x) < (r : ℝ) ∨ r = 1)) := by
    unfold cutPoint
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact ⟨h1, Or.inl (by linarith)⟩
      · exact ⟨h1, Or.inr h2⟩
    · rintro ⟨h1, h2 | h2⟩
      · exact ⟨h1, Or.inl (by linarith)⟩
      · exact ⟨h1, Or.inr h2⟩
  rw [hcU, Iff.comm]
  have hopen : ∀ Y, x.mem Y ↔ ∃ X, x.mem X ∧ a.rel X Y := by
    intro Y
    conv_lhs => rw [← hfix]
    exact mem_toElementMap a x
  constructor
  · intro hxr
    refine ⟨(R_mem_Ico0 (x.sub hxr)).2, ?_⟩
    by_cases hr1 : r = 1
    · exact Or.inr hr1
    · refine Or.inl ?_
      obtain ⟨X, hXmem, hrel⟩ := (hopen (Set.Ico 0 r)).mp hxr
      obtain ⟨r'', hr''0, hr''1, rfl⟩ := x.sub hXmem
      rw [a_rel, aRel_iff hr''0 hr''1 (R_mem_Ico0 (x.sub hxr)).1 (R_mem_Ico0 (x.sub hxr)).2] at hrel
      rcases hrel with hlt | ⟨-, hreq⟩
      · calc sInf (cutS x) ≤ (r'' : ℝ) := csInf_le hSbdd ⟨r'', hXmem, rfl⟩
          _ < (r : ℝ) := by exact_mod_cast hlt
      · exact absurd hreq hr1
  · rintro ⟨hr1, hc | rfl⟩
    · obtain ⟨q, ⟨r0, hr0mem, rfl⟩, hqlt⟩ := exists_lt_of_csInf_lt hSne hc
      dsimp only at hqlt
      have hr0r : r0 < r := by exact_mod_cast hqlt
      have hr0pos : 0 < r0 := (R_mem_Ico0 (x.sub hr0mem)).1
      exact x.up_mem hr0mem ⟨r, hr0pos.trans hr0r, hr1, rfl⟩ (Set.Ico_subset_Ico le_rfl hr0r.le)
    · rw [← R_master]; exact x.master_mem

/-- `cutElt` is injective on `[0,1]` (antisymmetry of `cutElt_le_iff`). -/
theorem cutElt_injective {t t' : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ht0' : 0 ≤ t') (ht1' : t' ≤ 1)
    (h : cutElt t ht1 = cutElt t' ht1') : t = t' :=
  le_antisymm ((cutElt_le_iff ht0 ht1 ht0' ht1').mp h.le) ((cutElt_le_iff ht0' ht1' ht0 ht1).mp h.ge)

/-- **Exercise 8.11 (Dedekind-cut correspondence).** The fixed-point set of `a` is order
isomorphic to `Set.Icc (0 : ℝ) 1` — a one-one correspondence with the reals between `0` and `1`
inclusive, under which `⊆` (domain order) matches `≤` (Scott's hint). -/
noncomputable def fixOrderIso : {y : R.Element // a.toElementMap y = y} ≃o Set.Icc (0 : ℝ) 1 where
  toFun y := ⟨cutPoint y.1, cutPoint_nonneg y.1, cutPoint_le_one y.1⟩
  invFun t := ⟨cutElt t.1 t.2.2, toElementMap_cutElt t.2.2⟩
  left_inv y := Subtype.ext (cutElt_cutPoint y.2)
  right_inv t := Subtype.ext (cutElt_injective (cutPoint_nonneg _) (cutPoint_le_one _) t.2.1 t.2.2
    (cutElt_cutPoint (toElementMap_cutElt t.2.2)))
  map_rel_iff' := by
    intro y y'
    show cutPoint y.1 ≤ cutPoint y'.1 ↔ y.1 ≤ y'.1
    constructor
    · intro h
      have h' := (cutElt_le_iff (cutPoint_nonneg y.1) (cutPoint_le_one y.1) (cutPoint_nonneg y'.1)
        (cutPoint_le_one y'.1)).mpr h
      rwa [cutElt_cutPoint y.2, cutElt_cutPoint y'.2] at h'
    · intro h
      rw [← cutElt_cutPoint y.2, ← cutElt_cutPoint y'.2] at h
      exact (cutElt_le_iff (cutPoint_nonneg y.1) (cutPoint_le_one y.1) (cutPoint_nonneg y'.1)
        (cutPoint_le_one y'.1)).mp h

/-! ### Non-finitarity -/

/-- **No point `g ⟨t,_,_⟩` with `t > 0` is compact**, for *any* neighbourhood system `F` and order
isomorphism `g : Set.Icc (0:ℝ) 1 ≃o F.Element`: the directed family `{g ⟨s,_,_⟩ ∣ 0 ≤ s < t}` has
supremum exactly `g ⟨t,_,_⟩` (`isLUB_Ico` transported through `g`), yet `g ⟨t,_,_⟩` sits strictly
above every member. This is Scott's hint made precise: aside from `⊥` (`t = 0`), `Set.Icc (0:ℝ) 1`
has no finite/compact elements. -/
theorem not_isCompactElt_pos {β : Type} {F : NeighborhoodSystem β}
    (g : Set.Icc (0 : ℝ) 1 ≃o F.Element) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htpos : 0 < t) :
    ¬ IsCompactElt (g ⟨t, ht0, ht1⟩) := by
  intro hcompact
  set S : Set (Set.Icc (0 : ℝ) 1) := {x | x.1 ∈ Set.Ico (0 : ℝ) t} with hSdef
  have hmem0 : (⟨0, le_refl 0, zero_le_one⟩ : Set.Icc (0 : ℝ) 1) ∈ S := ⟨le_refl 0, htpos⟩
  haveI : Nonempty S := ⟨⟨_, hmem0⟩⟩
  set fam : S → F.Element := fun x => g x.1 with hfamdef
  have hdir : ∀ i j : S, ∃ k : S, fam i ≤ fam k ∧ fam j ≤ fam k := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨⟨⟨max x.1 y.1, le_max_of_le_left x.2.1, (max_lt hx.2 hy.2).le.trans ht1⟩,
      ⟨le_max_of_le_left x.2.1, max_lt hx.2 hy.2⟩⟩, ?_, ?_⟩
    · exact g.monotone (le_max_left x.1 y.1)
    · exact g.monotone (le_max_right x.1 y.1)
  have hSisLUB : IsLUB S (⟨t, ht0, ht1⟩ : Set.Icc (0 : ℝ) 1) := by
    constructor
    · rintro x hx
      exact hx.2.le
    · intro ub hub
      exact (isLUB_Ico htpos).2 (fun y hy =>
        hub (show (⟨y, hy.1, hy.2.le.trans ht1⟩ : Set.Icc (0 : ℝ) 1) ∈ S from hy))
  have hgSisLUB : IsLUB (g '' S) (g ⟨t, ht0, ht1⟩) := g.isLUB_image'.mpr hSisLUB
  have hrange : Set.range fam = g '' S := by
    ext z
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  have hisLUBfam : IsLUB (Set.range fam) (g ⟨t, ht0, ht1⟩) := hrange ▸ hgSisLUB
  have hisLUBiSup : IsLUB (Set.range fam) (iSupDirected fam hdir) :=
    ⟨fun _ ⟨i, hi⟩ => hi ▸ le_iSupDirected fam hdir i,
      fun y hy => iSupDirected_le fam hdir (fun i => hy ⟨i, rfl⟩)⟩
  have heq : iSupDirected fam hdir = g ⟨t, ht0, ht1⟩ := hisLUBiSup.unique hisLUBfam
  obtain ⟨i, hi⟩ := hcompact fam hdir (le_of_eq heq.symm)
  have hle : (⟨t, ht0, ht1⟩ : Set.Icc (0 : ℝ) 1) ≤ i.1 := g.le_iff_le.mp hi
  exact absurd hle (not_le.mpr i.2.2)

/-- **Exercise 8.11 (conclusion).** `a` is *not* finitary: were it, its fixed-point set — order
isomorphic to `Set.Icc (0:ℝ) 1` via `fixOrderIso` — would also be order isomorphic to some `F.Element`,
which is algebraic (`eq_iSupDirected_principal`); but every principal approximant of `g ⟨1,_,_⟩`
would then be compact, hence (`not_isCompactElt_pos`) equal to `g ⟨0,_,_⟩`, forcing
`g ⟨1,_,_⟩ = g ⟨0,_,_⟩` — contradicting injectivity of `g` at `1 ≠ 0`. Exactly Scott's hint: aside
from `⊥`, `{x ∣ x = a(x)}` has no finite elements, so it cannot be algebraic unless it is trivial. -/
theorem not_isFinitary_a : ¬ IsFinitary a := by
  rintro ⟨β, F, ⟨e⟩⟩
  set g : Set.Icc (0 : ℝ) 1 ≃o F.Element := fixOrderIso.symm.trans e with hgdef
  set x : F.Element := g ⟨1, zero_le_one, le_refl 1⟩ with hxdef
  have hcompact_bot : ∀ i : {X : Set β // x.mem X}, F.principal (x.sub i.2) = g ⟨0, le_refl 0, zero_le_one⟩ := by
    intro i
    by_contra hne
    have hc0 : g.symm (F.principal (x.sub i.2)) ≠ ⟨0, le_refl 0, zero_le_one⟩ := fun h => hne (by
      rw [← h, OrderIso.apply_symm_apply])
    have ht0 : (0:ℝ) ≤ (g.symm (F.principal (x.sub i.2))).1 := (g.symm (F.principal (x.sub i.2))).2.1
    have ht1 : (g.symm (F.principal (x.sub i.2))).1 ≤ 1 := (g.symm (F.principal (x.sub i.2))).2.2
    have htpos : 0 < (g.symm (F.principal (x.sub i.2))).1 := by
      rcases ht0.lt_or_eq with h | h
      · exact h
      · exact absurd (Subtype.ext h.symm) hc0
    have hsub : (⟨(g.symm (F.principal (x.sub i.2))).1, ht0, ht1⟩ : Set.Icc (0 : ℝ) 1)
        = g.symm (F.principal (x.sub i.2)) := Subtype.ext rfl
    have heq2 : F.principal (x.sub i.2) = g ⟨(g.symm (F.principal (x.sub i.2))).1, ht0, ht1⟩ := by
      rw [hsub, OrderIso.apply_symm_apply]
    exact not_isCompactElt_pos g ht0 ht1 htpos (heq2 ▸ principal_isCompactElt (x.sub i.2))
  have hxeq : x = g ⟨0, le_refl 0, zero_le_one⟩ := by
    conv_lhs => rw [eq_iSupDirected_principal x]
    apply le_antisymm
    · apply iSupDirected_le
      intro i
      exact le_of_eq (hcompact_bot i)
    · obtain ⟨i0⟩ := (instNonemptyMemSubtype x)
      have hstep : g ⟨0, le_refl 0, zero_le_one⟩ ≤
          iSupDirected (fun j : {X : Set β // x.mem X} => F.principal (x.sub j.2))
            (principalFamily_directed x) := by
        rw [← hcompact_bot i0]
        exact le_iSupDirected (fun j : {X : Set β // x.mem X} => F.principal (x.sub j.2))
          (principalFamily_directed x) i0
      exact hstep
  have : (⟨1, zero_le_one, le_refl 1⟩ : Set.Icc (0:ℝ) 1) = ⟨0, le_refl 0, zero_le_one⟩ :=
    g.injective hxeq
  exact absurd (congrArg Subtype.val this) one_ne_zero

end Scott1980.Neighborhood.Exercise811

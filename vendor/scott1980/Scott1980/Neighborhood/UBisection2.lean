/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.SplitU
import Scott1980.Neighborhood.Exercise812e

/-!
# Exercise 8.12(f), prerequisite — a *presentation-independent* canonical bisection of `U`

`SplitU.lean`'s `splitULeft`/`splitURight` (built for Theorem 8.8(b)) split `Xₙ` at the midpoint of
`canonCode n`'s **first presenting pair** — but `canonCode` only clips/filters, it never *merges*
overlapping or adjacent intervals, so two different (both already-canonical, in the sense of
`canonList_fixed`) presenting lists of the *same* `U`-neighbourhood can have different first pairs
(e.g. `[(0,1)]` vs. `[(0, 1/2), (1/2, 1)]` both present `U.master`, but their first pairs' midpoints
are `1/2` and `1/4`). So `splitULeft`/`splitURight` do **not** satisfy `ComputableBisection`'s
`left_congr`/`right_congr` — this is a genuine gap in reusing `SplitU.lean` "as is" for `8.12(f)`,
mirroring the gap `MinLevel.lean` fixed for `V`'s side of `8.12(e)(d)`.

## The fix: split at the midpoint of `(min, max)` instead of the first pair

Rather than building full interval-merging machinery (as `MinLevel.lean` effectively had to for
`V`'s levels), a much lighter invariant suffices here: for a finite union of half-open rational
intervals `X = ⋃ Ico pᵢ.1 pᵢ.2`,

* `min X = min_i pᵢ.1` (attained — every `Ico` is left-closed, and every point of the union is `≥`
  some `pᵢ.1 ≥ min_i pᵢ.1`), and
* `sup X = max_i pᵢ.2` (not necessarily attained, but this is *still* a fact purely about the set
  `X`, not about which particular representing list computes it — `sup` of a finite union is the
  `max` of the individual `sup`s, and each `Ico pᵢ.1 pᵢ.2` has `sup = pᵢ.2`).

Both quantities are therefore genuinely **intrinsic to the set** `X`, not to the specific
presenting list — so splitting at their midpoint is automatically presentation-independent, with no
need to ever canonicalize/merge/sort the interval list itself. `listMinFst`/`listMaxSnd` below
compute exactly these two quantities as primitive-recursive folds over `canonCode n`'s list, reusing
`SplitU.lean`'s `clipLtListCode`/`clipGeListCode` unchanged for the actual clipping.
-/

namespace Scott1980.Neighborhood

open Domain.Recursive NeighborhoodSystem

/-! ### Every pair of `canonCode c`'s list lies in `[0, 1]` -/

/-- **Every pair of `decodeQPairList (canonCode c)` has both endpoints in `[0, 1]`** — mirrors
`forall_lt_decodeQPairList_canonCode` (nondegeneracy), giving the companion boundedness fact. -/
theorem forall_bounds_decodeQPairList_canonCode (c : ℕ) :
    ∀ p ∈ decodeQPairList (canonCode c), 0 ≤ p.1 ∧ p.2 ≤ 1 := by
  unfold canonCode
  by_cases hz : canonListCode c = 0
  · have hzero : isZero (canonListCode c) = 1 := by rw [hz]; exact (isZero_eq_one_iff 0).mpr rfl
    rw [hzero, selectFn_one]
    intro p hp
    rw [decodeQPairList_masterCode, List.mem_singleton] at hp
    rw [hp]; norm_num
  · have hzero : isZero (canonListCode c) = 0 := by
      by_contra hcontra
      have h1 := isZero_le_one (canonListCode c)
      exact hz ((isZero_eq_one_iff _).mp (by omega))
    rw [hzero, selectFn_zero]
    intro p hp
    obtain ⟨p0, -, -, rfl⟩ := (mem_decodeQPairList_canonListCode c p).mp hp
    exact ⟨le_sup_right, inf_le_right⟩

/-! ### `listMinFst`/`listMaxSnd`: the two intrinsic quantities, at the `List (ℚ × ℚ)` level -/

/-- `min_i pᵢ.1` over a presenting list, folded with seed `1` (safe: every genuine pair has
`p.1 < 1` once bounded, `forall_bounds_decodeQPairList_canonCode`). -/
def listMinFst (L : List (ℚ × ℚ)) : ℚ := L.foldl (fun acc p => min acc p.1) 1

/-- `max_i pᵢ.2` over a presenting list, folded with seed `0`. -/
def listMaxSnd (L : List (ℚ × ℚ)) : ℚ := L.foldl (fun acc p => max acc p.2) 0

theorem foldl_minFst_le_seed (L : List (ℚ × ℚ)) (seed : ℚ) :
    L.foldl (fun acc p => min acc p.1) seed ≤ seed := by
  induction L generalizing seed with
  | nil => exact le_refl seed
  | cons a l ih =>
    rw [List.foldl_cons]
    exact (ih (min seed a.1)).trans (min_le_left seed a.1)

theorem foldl_minFst_le (L : List (ℚ × ℚ)) (seed : ℚ) (p : ℚ × ℚ) (hp : p ∈ L) :
    L.foldl (fun acc q => min acc q.1) seed ≤ p.1 := by
  induction L generalizing seed with
  | nil => cases hp
  | cons a l ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact (foldl_minFst_le_seed l (min seed p.1)).trans (min_le_right seed p.1)
    · exact ih (min seed a.1) hp'

theorem foldl_minFst_mem_or_eq_seed (L : List (ℚ × ℚ)) (seed : ℚ) :
    L.foldl (fun acc p => min acc p.1) seed = seed ∨
      ∃ p ∈ L, L.foldl (fun acc q => min acc q.1) seed = p.1 := by
  induction L generalizing seed with
  | nil => exact Or.inl rfl
  | cons a l ih =>
    rw [List.foldl_cons]
    rcases le_total seed a.1 with hle | hle
    · rw [min_eq_left hle]
      rcases ih seed with h | ⟨p, hp, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨p, List.mem_cons_of_mem a hp, h⟩
    · rw [min_eq_right hle]
      rcases ih a.1 with h | ⟨p, hp, h⟩
      · exact Or.inr ⟨a, List.mem_cons_self .., h⟩
      · exact Or.inr ⟨p, List.mem_cons_of_mem a hp, h⟩

theorem foldl_maxSnd_seed_le (L : List (ℚ × ℚ)) (seed : ℚ) :
    seed ≤ L.foldl (fun acc p => max acc p.2) seed := by
  induction L generalizing seed with
  | nil => exact le_refl seed
  | cons a l ih =>
    rw [List.foldl_cons]
    exact (le_max_left seed a.2).trans (ih (max seed a.2))

theorem foldl_maxSnd_ge (L : List (ℚ × ℚ)) (seed : ℚ) (p : ℚ × ℚ) (hp : p ∈ L) :
    p.2 ≤ L.foldl (fun acc q => max acc q.2) seed := by
  induction L generalizing seed with
  | nil => cases hp
  | cons a l ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact (le_max_right seed p.2).trans (foldl_maxSnd_seed_le l (max seed p.2))
    · exact ih (max seed a.2) hp'

theorem foldl_maxSnd_mem_or_eq_seed (L : List (ℚ × ℚ)) (seed : ℚ) :
    L.foldl (fun acc p => max acc p.2) seed = seed ∨
      ∃ p ∈ L, L.foldl (fun acc q => max acc q.2) seed = p.2 := by
  induction L generalizing seed with
  | nil => exact Or.inl rfl
  | cons a l ih =>
    rw [List.foldl_cons]
    rcases le_total a.2 seed with hle | hle
    · rw [max_eq_left hle]
      rcases ih seed with h | ⟨p, hp, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨p, List.mem_cons_of_mem a hp, h⟩
    · rw [max_eq_right hle]
      rcases ih a.2 with h | ⟨p, hp, h⟩
      · exact Or.inr ⟨a, List.mem_cons_self .., h⟩
      · exact Or.inr ⟨p, List.mem_cons_of_mem a hp, h⟩

theorem listMinFst_le {L : List (ℚ × ℚ)} {p : ℚ × ℚ} (hp : p ∈ L) : listMinFst L ≤ p.1 :=
  foldl_minFst_le L 1 p hp

theorem listMinFst_le_one (L : List (ℚ × ℚ)) : listMinFst L ≤ 1 := foldl_minFst_le_seed L 1

theorem listMaxSnd_ge {L : List (ℚ × ℚ)} {p : ℚ × ℚ} (hp : p ∈ L) : p.2 ≤ listMaxSnd L :=
  foldl_maxSnd_ge L 0 p hp

theorem zero_le_listMaxSnd (L : List (ℚ × ℚ)) : 0 ≤ listMaxSnd L := foldl_maxSnd_seed_le L 0

theorem listMinFst_attained {L : List (ℚ × ℚ)} (hne : L ≠ []) (hub : ∀ p ∈ L, p.1 < 1) :
    ∃ p ∈ L, p.1 = listMinFst L := by
  rcases foldl_minFst_mem_or_eq_seed L 1 with h1 | ⟨p, hp, h1⟩
  · obtain ⟨p0, hp0⟩ := List.exists_mem_of_ne_nil L hne
    exact absurd (h1 ▸ listMinFst_le hp0) (not_le.mpr (hub p0 hp0))
  · exact ⟨p, hp, h1.symm⟩

theorem listMaxSnd_attained {L : List (ℚ × ℚ)} (hne : L ≠ []) (hlb : ∀ p ∈ L, 0 < p.2) :
    ∃ p ∈ L, p.2 = listMaxSnd L := by
  rcases foldl_maxSnd_mem_or_eq_seed L 0 with h1 | ⟨p, hp, h1⟩
  · obtain ⟨p0, hp0⟩ := List.exists_mem_of_ne_nil L hne
    exact absurd (h1 ▸ listMaxSnd_ge hp0) (not_le.mpr (hlb p0 hp0))
  · exact ⟨p, hp, h1.symm⟩

/-- **`listMinFst L` is the genuine minimum of `presentedIntervals L`** (membership half). -/
theorem listMinFst_mem_presentedIntervals {L : List (ℚ × ℚ)} (hne : L ≠ [])
    (hpos : ∀ p ∈ L, p.1 < p.2) (hb : ∀ p ∈ L, 0 ≤ p.1 ∧ p.2 ≤ 1) :
    listMinFst L ∈ presentedIntervals L := by
  have hub : ∀ p ∈ L, p.1 < 1 := fun p hp => (hpos p hp).trans_le (hb p hp).2
  obtain ⟨p, hp, hpeq⟩ := listMinFst_attained hne hub
  exact mem_presentedIntervals.mpr ⟨p, hp, hpeq.le, hpeq ▸ hpos p hp⟩

/-- **`listMinFst L` lower-bounds `presentedIntervals L`.** -/
theorem listMinFst_lower_bound {L : List (ℚ × ℚ)} {x : ℚ} (hx : x ∈ presentedIntervals L) :
    listMinFst L ≤ x := by
  obtain ⟨p, hp, hx1, -⟩ := mem_presentedIntervals.mp hx
  exact (listMinFst_le hp).trans hx1

/-- **`listMaxSnd L` strictly upper-bounds `presentedIntervals L`.** -/
theorem listMaxSnd_upper_bound {L : List (ℚ × ℚ)} {x : ℚ} (hx : x ∈ presentedIntervals L) :
    x < listMaxSnd L := by
  obtain ⟨p, hp, -, hx2⟩ := mem_presentedIntervals.mp hx
  exact hx2.trans_le (listMaxSnd_ge hp)

/-- **`listMaxSnd L` is arbitrarily approached from below by `presentedIntervals L`.** -/
theorem listMaxSnd_tight {L : List (ℚ × ℚ)} (hne : L ≠ [])
    (hpos : ∀ p ∈ L, p.1 < p.2) (hb : ∀ p ∈ L, 0 ≤ p.1 ∧ p.2 ≤ 1) {y : ℚ}
    (hy : y < listMaxSnd L) : ∃ x ∈ presentedIntervals L, y < x := by
  have hlb : ∀ p ∈ L, 0 < p.2 := fun p hp => lt_of_le_of_lt (hb p hp).1 (hpos p hp)
  obtain ⟨p, hp, hpeq⟩ := listMaxSnd_attained hne hlb
  rw [← hpeq] at hy
  rcases lt_or_ge y p.1 with hlt | hge
  · exact ⟨p.1, mem_presentedIntervals.mpr ⟨p, hp, le_refl _, hpos p hp⟩, hlt⟩
  · exact ⟨(y + p.2) / 2, mem_presentedIntervals.mpr ⟨p, hp, hge.trans (left_lt_add_div_two.mpr hy).le,
      add_div_two_lt_right.mpr hy⟩, left_lt_add_div_two.mpr hy⟩

/-- **`listMinFst` is a well-defined function of the presented set alone**, mirroring
`MinLevel.lean`'s `minLevel_unique` for `V`: two (nonempty, nondegenerate, `[0,1]`-bounded)
presenting lists of the *same* set have the same `listMinFst`. -/
theorem listMinFst_congr {L1 L2 : List (ℚ × ℚ)} (hne1 : L1 ≠ []) (hne2 : L2 ≠ [])
    (hpos1 : ∀ p ∈ L1, p.1 < p.2) (hb1 : ∀ p ∈ L1, 0 ≤ p.1 ∧ p.2 ≤ 1)
    (hpos2 : ∀ p ∈ L2, p.1 < p.2) (hb2 : ∀ p ∈ L2, 0 ≤ p.1 ∧ p.2 ≤ 1)
    (heq : presentedIntervals L1 = presentedIntervals L2) :
    listMinFst L1 = listMinFst L2 := by
  have hm1 : listMinFst L1 ∈ presentedIntervals L2 :=
    heq ▸ listMinFst_mem_presentedIntervals hne1 hpos1 hb1
  have hm2 : listMinFst L2 ∈ presentedIntervals L1 :=
    heq ▸ listMinFst_mem_presentedIntervals hne2 hpos2 hb2
  exact le_antisymm (listMinFst_lower_bound hm2) (listMinFst_lower_bound hm1)

/-- **`listMaxSnd` is a well-defined function of the presented set alone.** -/
theorem listMaxSnd_congr {L1 L2 : List (ℚ × ℚ)} (hne1 : L1 ≠ []) (hne2 : L2 ≠ [])
    (hpos1 : ∀ p ∈ L1, p.1 < p.2) (hb1 : ∀ p ∈ L1, 0 ≤ p.1 ∧ p.2 ≤ 1)
    (hpos2 : ∀ p ∈ L2, p.1 < p.2) (hb2 : ∀ p ∈ L2, 0 ≤ p.1 ∧ p.2 ≤ 1)
    (heq : presentedIntervals L1 = presentedIntervals L2) :
    listMaxSnd L1 = listMaxSnd L2 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨x, hx, hyx⟩ := listMaxSnd_tight hne2 hpos2 hb2 hlt
    have hx1 : x ∈ presentedIntervals L1 := heq.symm ▸ hx
    exact absurd (listMaxSnd_upper_bound hx1) (not_lt.mpr hyx.le)
  · obtain ⟨x, hx, hyx⟩ := listMaxSnd_tight hne1 hpos1 hb1 hlt
    have hx2 : x ∈ presentedIntervals L2 := heq ▸ hx
    exact absurd (listMaxSnd_upper_bound hx2) (not_lt.mpr hyx.le)

/-! ### `listMinFst`/`listMaxSnd`, at the code level (`listMinFstCode`/`listMaxSndCode`)

Fold `ratMinCode`/`ratMaxCode` over the raw pair-code list via `Recursive.lean`'s `foldCode`,
mirroring `listMinFst`/`listMaxSnd`'s list-level folds exactly (seed `oneCode`/`zeroCode`, no
`params` needed). -/

/-- The code-level `listMinFst`: fold `ratMinCode` over `c`'s pair-codes, seeded at `oneCode`. -/
def listMinFstCode (c : ℕ) : ℕ :=
  foldCode (fun t => ratMinCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.1)) 0 oneCode c

/-- The code-level `listMaxSnd`: fold `ratMaxCode` over `c`'s pair-codes, seeded at `zeroCode`. -/
def listMaxSndCode (c : ℕ) : ℕ :=
  foldCode (fun t => ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.2)) 0 zeroCode c

theorem primrec_listMinFstCode : Nat.Primrec listMinFstCode := by
  have hstp : Nat.Primrec
      (fun t : ℕ => ratMinCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.1)) :=
    (primrec_ratMinCode.comp ((Nat.Primrec.left.comp Nat.Primrec.right).pair
      (Nat.Primrec.left.comp Nat.Primrec.left))).of_eq fun _ => rfl
  exact (primrec_foldCode hstp (Nat.Primrec.const 0) (Nat.Primrec.const oneCode) primrec_id).of_eq
    fun _ => rfl

theorem primrec_listMaxSndCode : Nat.Primrec listMaxSndCode := by
  have hstp : Nat.Primrec
      (fun t : ℕ => ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.2)) :=
    (primrec_ratMaxCode.comp ((Nat.Primrec.left.comp Nat.Primrec.right).pair
      (Nat.Primrec.right.comp Nat.Primrec.left))).of_eq fun _ => rfl
  exact (primrec_foldCode hstp (Nat.Primrec.const 0) (Nat.Primrec.const zeroCode) primrec_id).of_eq
    fun _ => rfl

/-- Bridging `List.foldl` over raw pair-codes (via `ratMinCode`) to `List.foldl` over decoded
pairs (via `min ·.1`), one step at a time. -/
theorem decodeRat_foldl_ratMin (l : List ℕ) (z : ℕ) :
    decodeRat (l.foldl (fun acc x => ratMinCode (Nat.pair acc x.unpair.1)) z)
      = (l.map decodeRatPair).foldl (fun acc p => min acc p.1) (decodeRat z) := by
  induction l generalizing z with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, ih, decodeRat_ratMinCode]
    rfl

theorem decodeRat_foldl_ratMax (l : List ℕ) (z : ℕ) :
    decodeRat (l.foldl (fun acc x => ratMaxCode (Nat.pair acc x.unpair.2)) z)
      = (l.map decodeRatPair).foldl (fun acc p => max acc p.2) (decodeRat z) := by
  induction l generalizing z with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, ih, decodeRat_ratMaxCode]
    rfl

theorem decodeRat_listMinFstCode (c : ℕ) :
    decodeRat (listMinFstCode c) = listMinFst (decodeQPairList c) := by
  unfold listMinFstCode listMinFst decodeQPairList
  rw [foldCode_eq']
  have hstep : (fun (acc x : ℕ) =>
      (fun t : ℕ => ratMinCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.1))
        (Nat.pair x (Nat.pair acc 0)))
      = (fun acc x : ℕ => ratMinCode (Nat.pair acc x.unpair.1)) := by
    funext acc x; simp only [unpair_pair_fst, unpair_pair_snd]
  rw [hstep, decodeRat_foldl_ratMin, decodeRat_oneCode]

theorem decodeRat_listMaxSndCode (c : ℕ) :
    decodeRat (listMaxSndCode c) = listMaxSnd (decodeQPairList c) := by
  unfold listMaxSndCode listMaxSnd decodeQPairList
  rw [foldCode_eq']
  have hstep : (fun (acc x : ℕ) =>
      (fun t : ℕ => ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.2))
        (Nat.pair x (Nat.pair acc 0)))
      = (fun acc x : ℕ => ratMaxCode (Nat.pair acc x.unpair.2)) := by
    funext acc x; simp only [unpair_pair_fst, unpair_pair_snd]
  rw [hstep, decodeRat_foldl_ratMax, decodeRat_zeroCode]

/-! ### `splitU2`: the presentation-independent midpoint split -/

/-- The midpoint code of `canonCode n`'s intrinsic `(min, max)` pair. -/
def splitU2MidCode (n : ℕ) : ℕ :=
  ratMidCode (Nat.pair (listMinFstCode (canonCode n)) (listMaxSndCode (canonCode n)))

theorem primrec_splitU2MidCode : Nat.Primrec splitU2MidCode :=
  (primrec_ratMidCode.comp
    ((primrec_listMinFstCode.comp primrec_canonCode).pair
      (primrec_listMaxSndCode.comp primrec_canonCode))).of_eq fun n => by
    simp only [splitU2MidCode]

/-- The "left" half of the canonical split of `Xₙ`: `Xₙ ∩ (-∞, m)` for `m` the midpoint of `Xₙ`'s
intrinsic `(min, max)`. -/
def splitU2Left (n : ℕ) : ℕ := clipLtListCode (splitU2MidCode n) (canonCode n)

/-- The "right" half of the canonical split of `Xₙ`: `Xₙ ∩ [m, ∞)`. -/
def splitU2Right (n : ℕ) : ℕ := clipGeListCode (splitU2MidCode n) (canonCode n)

theorem primrec_splitU2Left : Nat.Primrec splitU2Left :=
  (primrec_clipLtListCode.comp (primrec_splitU2MidCode.pair primrec_canonCode)).of_eq
    fun n => by simp only [splitU2Left, unpair_pair_fst, unpair_pair_snd]

theorem primrec_splitU2Right : Nat.Primrec splitU2Right :=
  (primrec_clipGeListCode.comp (primrec_splitU2MidCode.pair primrec_canonCode)).of_eq
    fun n => by simp only [splitU2Right, unpair_pair_fst, unpair_pair_snd]

/-! ### Correctness -/

theorem decodeRat_splitU2MidCode (n : ℕ) :
    decodeRat (splitU2MidCode n) =
      (listMinFst (decodeQPairList (canonCode n)) + listMaxSnd (decodeQPairList (canonCode n)))
        / 2 := by
  unfold splitU2MidCode
  rw [decodeRat_ratMidCode', unpair_pair_fst, unpair_pair_snd, decodeRat_listMinFstCode,
    decodeRat_listMaxSndCode]

/-- **`Xₙ`'s intrinsic minimum is strictly below its intrinsic maximum**, via any single
witnessing pair of `canonCode n`'s presenting list (nonempty, `forall_lt_...`). -/
theorem splitU2_min_lt_max (n : ℕ) :
    listMinFst (decodeQPairList (canonCode n)) < listMaxSnd (decodeQPairList (canonCode n)) := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ (decodeQPairList_canonCode_ne_nil n)
  exact lt_of_le_of_lt (listMinFst_le hp)
    (lt_of_lt_of_le (forall_lt_decodeQPairList_canonCode n p hp) (listMaxSnd_ge hp))

theorem splitU2_min_lt_mid (n : ℕ) :
    listMinFst (decodeQPairList (canonCode n)) < decodeRat (splitU2MidCode n) := by
  rw [decodeRat_splitU2MidCode]; exact left_lt_add_div_two.mpr (splitU2_min_lt_max n)

theorem splitU2_mid_lt_max (n : ℕ) :
    decodeRat (splitU2MidCode n) < listMaxSnd (decodeQPairList (canonCode n)) := by
  rw [decodeRat_splitU2MidCode]; exact add_div_two_lt_right.mpr (splitU2_min_lt_max n)

theorem UX_splitU2Left (n : ℕ) :
    UX (splitU2Left n) = UX n ∩ Set.Iio (decodeRat (splitU2MidCode n)) := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (splitU2Left n))) := by
    show U.mem
      (presentedIntervals (decodeQPairList (clipLtListCode (splitU2MidCode n) (canonCode n))))
    rw [presentedIntervals_decodeQPairList_clipLtListCode]
    refine ⟨⟨(decodeQPairList (canonCode n)).map (qpClipLt (decodeRat (splitU2MidCode n))),
      (presentedIntervals_map_qpClipLt _ _).symm⟩, ?_, ?_⟩
    · refine ⟨listMinFst (decodeQPairList (canonCode n)), ?_, splitU2_min_lt_mid n⟩
      exact listMinFst_mem_presentedIntervals (decodeQPairList_canonCode_ne_nil n)
        (forall_lt_decodeQPairList_canonCode n) (forall_bounds_decodeQPairList_canonCode n)
    · exact Set.inter_subset_left.trans (U_mem_UX n).2.2
  show presentedIntervals (decodeQPairList (canonCode (splitU2Left n))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL]
  show presentedIntervals (decodeQPairList (clipLtListCode (splitU2MidCode n) (canonCode n))) = _
  rw [presentedIntervals_decodeQPairList_clipLtListCode]
  rfl

theorem UX_splitU2Right (n : ℕ) :
    UX (splitU2Right n) = UX n ∩ Set.Ici (decodeRat (splitU2MidCode n)) := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (splitU2Right n))) := by
    show U.mem
      (presentedIntervals (decodeQPairList (clipGeListCode (splitU2MidCode n) (canonCode n))))
    rw [presentedIntervals_decodeQPairList_clipGeListCode]
    refine ⟨⟨(decodeQPairList (canonCode n)).map (qpClipGe (decodeRat (splitU2MidCode n))),
      (presentedIntervals_map_qpClipGe _ _).symm⟩, ?_, ?_⟩
    · obtain ⟨x, hx, hxgt⟩ := listMaxSnd_tight (decodeQPairList_canonCode_ne_nil n)
        (forall_lt_decodeQPairList_canonCode n) (forall_bounds_decodeQPairList_canonCode n)
        (splitU2_mid_lt_max n)
      exact ⟨x, hx, hxgt.le⟩
    · exact Set.inter_subset_left.trans (U_mem_UX n).2.2
  show presentedIntervals (decodeQPairList (canonCode (splitU2Right n))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL]
  show presentedIntervals (decodeQPairList (clipGeListCode (splitU2MidCode n) (canonCode n))) = _
  rw [presentedIntervals_decodeQPairList_clipGeListCode]
  rfl

/-- **Disjointness**: `splitU2Left`/`splitU2Right` cover disjoint pieces. -/
theorem splitU2_disjoint (n : ℕ) : UX (splitU2Left n) ∩ UX (splitU2Right n) = ∅ := by
  rw [UX_splitU2Left, UX_splitU2Right]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨-, h1⟩, -, h2⟩
  exact absurd h1 (not_lt.mpr h2)

/-- **Covering**: `splitU2Left`/`splitU2Right` reunite to `Xₙ`. -/
theorem splitU2_union (n : ℕ) : UX (splitU2Left n) ∪ UX (splitU2Right n) = UX n := by
  rw [UX_splitU2Left, UX_splitU2Right]
  ext x
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    rcases lt_or_ge x (decodeRat (splitU2MidCode n)) with hlt | hge
    · exact Or.inl ⟨h, hlt⟩
    · exact Or.inr ⟨h, hge⟩

/-- **`splitU2Left`/`splitU2Right`'s midpoint depends only on `UX n` as a set** — the key lemma
that `SplitU.lean`'s `splitULeft`/`splitURight` lack, via `listMinFst_congr`/`listMaxSnd_congr`. -/
theorem splitU2MidCode_congr {n n' : ℕ} (h : UX n = UX n') :
    decodeRat (splitU2MidCode n) = decodeRat (splitU2MidCode n') := by
  have heqP : presentedIntervals (decodeQPairList (canonCode n))
      = presentedIntervals (decodeQPairList (canonCode n')) := h
  have hminEq := listMinFst_congr (decodeQPairList_canonCode_ne_nil n)
    (decodeQPairList_canonCode_ne_nil n') (forall_lt_decodeQPairList_canonCode n)
    (forall_bounds_decodeQPairList_canonCode n) (forall_lt_decodeQPairList_canonCode n')
    (forall_bounds_decodeQPairList_canonCode n') heqP
  have hmaxEq := listMaxSnd_congr (decodeQPairList_canonCode_ne_nil n)
    (decodeQPairList_canonCode_ne_nil n') (forall_lt_decodeQPairList_canonCode n)
    (forall_bounds_decodeQPairList_canonCode n) (forall_lt_decodeQPairList_canonCode n')
    (forall_bounds_decodeQPairList_canonCode n') heqP
  rw [decodeRat_splitU2MidCode, decodeRat_splitU2MidCode, hminEq, hmaxEq]

/-- **`splitU2Left`'s output set is a well-defined function of `UX k` as a set.** -/
theorem splitU2Left_congr {n n' : ℕ} (h : UX n = UX n') :
    UX (splitU2Left n) = UX (splitU2Left n') := by
  rw [UX_splitU2Left, UX_splitU2Left, h, splitU2MidCode_congr h]

/-- **`splitU2Right`'s output set is a well-defined function of `UX k` as a set.** -/
theorem splitU2Right_congr {n n' : ℕ} (h : UX n = UX n') :
    UX (splitU2Right n) = UX (splitU2Right n') := by
  rw [UX_splitU2Right, UX_splitU2Right, h, splitU2MidCode_congr h]

/-- **`U`'s computable canonical bisection, packaged as a `ComputableBisection`** — the missing
`(f)`-side prerequisite, fixing `SplitU.lean`'s `left_congr`/`right_congr` gap (see the module
docstring). -/
def UBisection2 : ComputableBisection UComputablePresentation where
  left := splitU2Left
  right := splitU2Right
  left_primrec := primrec_splitU2Left
  right_primrec := primrec_splitU2Right
  disjoint := splitU2_disjoint
  union := splitU2_union
  left_congr := fun _ _ h => splitU2Left_congr h
  right_congr := fun _ _ h => splitU2Right_congr h

end Scott1980.Neighborhood

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.UComputablePresentation

/-!
# Theorem 8.8(b), Part 4 — an explicit, deterministic `splitU`

`Definition87.lean`'s `U_no_minimal` shows every `U`-neighbourhood splits into two proper disjoint
`U`-neighbourhoods, but only as a bare existential (`∃ Y Z, ...`), built via `Classical`-flavoured
case analysis on an arbitrary witness of non-emptiness. Theorem 8.8(b)'s eventual `Y_n` chain
(Part 6) needs to *compute* such a split from an index `n` alone — so here we replace the
existential by a genuinely `Nat.Primrec` pair `splitULeft`/`splitURight : ℕ → ℕ`, and reprove
`U_no_minimal`'s four properties (disjoint, covering, both proper) for this canonical choice.

## The construction

Given an index `n`, canonicalize it (`canonCode n`, Part 3) to get a genuine presenting list, all
of whose pairs are already non-degenerate (`forall_lt_decodeQPairList_canonCode`). Take its
**first** pair `p₀ = decodeRatPair (firstElemCode (canonCode n))` (no search needed — the *first*
pair always works, unlike `U_no_minimal`'s arbitrary witness of non-emptiness) and split at its
rational midpoint `m := (p₀.1 + p₀.2)/2` (`ratMidCode`, computed with no genuine division — see
`RationalPrimrec.lean`): `splitULeft n` re-clips every pair of `canonCode n` into `(-∞, m)`
(`clipLtListCode`), `splitURight n` into `[m, ∞)` (`clipGeListCode`). Both are realized at the code
level via `RecursiveCross.lean`'s `flatMapCode`, threading `m` through as the fixed parameter.

Correctness (`UX_splitULeft`/`UX_splitURight`) shows these compute exactly `Xₙ ∩ (-∞,m)` /
`Xₙ ∩ [m,∞)` as *sets*, mirroring `U_no_minimal`'s own proof almost verbatim; `splitU_disjoint`/
`splitU_union`/`splitU_left_ne`/`splitU_right_ne` package the four properties.
-/

namespace Scott1980.Neighborhood

open Domain.Recursive NeighborhoodSystem

/-! ### Public one-sided clips (`Definition87.lean`'s `clipLt`/`clipGe` are `private`) -/

/-- Clip a pair down to `(-∞, m)`: leave the left endpoint, clamp the right endpoint at `m`. -/
def qpClipLt (m : ℚ) (p : ℚ × ℚ) : ℚ × ℚ := (p.1, p.2 ⊓ m)

/-- Clip a pair up to `[m, ∞)`: clamp the left endpoint at `m`, leave the right endpoint. -/
def qpClipGe (m : ℚ) (p : ℚ × ℚ) : ℚ × ℚ := (p.1 ⊔ m, p.2)

theorem presentedIntervals_map_qpClipLt (m : ℚ) (L : List (ℚ × ℚ)) :
    presentedIntervals (L.map (qpClipLt m)) = presentedIntervals L ∩ Set.Iio m := by
  ext x
  simp only [mem_presentedIntervals, List.mem_map, Set.mem_inter_iff, Set.mem_Iio, qpClipLt]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hx1, hx2⟩
    exact ⟨⟨q, hq, hx1, hx2.trans_le inf_le_left⟩, hx2.trans_le inf_le_right⟩
  · rintro ⟨⟨q, hq, hxq1, hxq2⟩, hxm⟩
    exact ⟨(q.1, q.2 ⊓ m), ⟨q, hq, rfl⟩, hxq1, lt_inf_iff.mpr ⟨hxq2, hxm⟩⟩

theorem presentedIntervals_map_qpClipGe (m : ℚ) (L : List (ℚ × ℚ)) :
    presentedIntervals (L.map (qpClipGe m)) = presentedIntervals L ∩ Set.Ici m := by
  ext x
  simp only [mem_presentedIntervals, List.mem_map, Set.mem_inter_iff, Set.mem_Ici, qpClipGe]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hx1, hx2⟩
    exact ⟨⟨q, hq, le_sup_left.trans hx1, hx2⟩, le_sup_right.trans hx1⟩
  · rintro ⟨⟨q, hq, hxq1, hxq2⟩, hxm⟩
    exact ⟨(q.1 ⊔ m, q.2), ⟨q, hq, rfl⟩, sup_le hxq1 hxm, hxq2⟩

/-! ### One-sided clips, at the code level -/

/-- Clip a rational-pair code `e` to `(-∞, decodeRat m)`, given `t = pair m e`. -/
def clipLtCode (t : ℕ) : ℕ :=
  Nat.pair t.unpair.2.unpair.1 (ratMinCode (Nat.pair t.unpair.2.unpair.2 t.unpair.1))

/-- Clip a rational-pair code `e` to `[decodeRat m, ∞)`, given `t = pair m e`. -/
def clipGeCode (t : ℕ) : ℕ :=
  Nat.pair (ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1)) t.unpair.2.unpair.2

theorem primrec_clipLtCode : Nat.Primrec clipLtCode := by
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have he1 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have he2 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact (Nat.Primrec.pair he1 (primrec_ratMinCode.comp (he2.pair hm))).of_eq
    fun t => by simp only [clipLtCode]

theorem primrec_clipGeCode : Nat.Primrec clipGeCode := by
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have he1 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have he2 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact (Nat.Primrec.pair (primrec_ratMaxCode.comp (he1.pair hm)) he2).of_eq
    fun t => by simp only [clipGeCode]

theorem decodeRatPair_clipLtCode (m e : ℕ) :
    decodeRatPair (clipLtCode (Nat.pair m e)) = qpClipLt (decodeRat m) (decodeRatPair e) := by
  unfold clipLtCode decodeRatPair qpClipLt
  simp only [unpair_pair_fst, unpair_pair_snd, decodeRat_ratMinCode]

theorem decodeRatPair_clipGeCode (m e : ℕ) :
    decodeRatPair (clipGeCode (Nat.pair m e)) = qpClipGe (decodeRat m) (decodeRatPair e) := by
  unfold clipGeCode decodeRatPair qpClipGe
  simp only [unpair_pair_fst, unpair_pair_snd, decodeRat_ratMaxCode]

/-! ### Mapping a one-sided clip over a whole list, at the code level

`flatMapCode f x c` codes `(decodeList c).flatMap (fun y => decodeList (f (pair x y)))`, with `x`
threaded through as a *fixed* parameter — exactly what's needed here, with `x := m` the (already
computed) midpoint code and `f := fun t => [clip t]` (singleton). -/

/-- Clip every pair of the list-code `c` into `(-∞, decodeRat m)`. -/
def clipLtListCode (m c : ℕ) : ℕ := flatMapCode (fun t => Nat.pair (clipLtCode t) 0 + 1) m c

/-- Clip every pair of the list-code `c` into `[decodeRat m, ∞)`. -/
def clipGeListCode (m c : ℕ) : ℕ := flatMapCode (fun t => Nat.pair (clipGeCode t) 0 + 1) m c

theorem primrec_clipLtListCode : Nat.Primrec (fun t : ℕ => clipLtListCode t.unpair.1 t.unpair.2) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair (clipLtCode t) 0 + 1) :=
    Nat.Primrec.succ.comp (primrec_clipLtCode.pair (Nat.Primrec.const 0))
  exact (primrec_flatMapCode hg).of_eq fun _ => rfl

theorem primrec_clipGeListCode : Nat.Primrec (fun t : ℕ => clipGeListCode t.unpair.1 t.unpair.2) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair (clipGeCode t) 0 + 1) :=
    Nat.Primrec.succ.comp (primrec_clipGeCode.pair (Nat.Primrec.const 0))
  exact (primrec_flatMapCode hg).of_eq fun _ => rfl

theorem decodeQPairList_singletonCode (v : ℕ) :
    decodeQPairList (Nat.pair v 0 + 1) = [decodeRatPair v] := by
  unfold decodeQPairList
  rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero]
  rfl

theorem mem_decodeQPairList_clipLtListCode (m c : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (clipLtListCode m c) ↔
      ∃ p0 ∈ decodeQPairList c, p = qpClipLt (decodeRat m) p0 := by
  unfold clipLtListCode
  rw [mem_decodeQPairList_flatMapCode]
  constructor
  · rintro ⟨y, hy, hp⟩
    rw [decodeQPairList_singletonCode, List.mem_singleton, decodeRatPair_clipLtCode] at hp
    exact ⟨decodeRatPair y, (mem_decodeQPairList c (decodeRatPair y)).mpr ⟨y, hy, rfl⟩, hp⟩
  · rintro ⟨p0, hp0, hp⟩
    obtain ⟨y, hy, rfl⟩ := (mem_decodeQPairList c p0).mp hp0
    exact ⟨y, hy, by
      rw [decodeQPairList_singletonCode, List.mem_singleton, decodeRatPair_clipLtCode]; exact hp⟩

theorem mem_decodeQPairList_clipGeListCode (m c : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (clipGeListCode m c) ↔
      ∃ p0 ∈ decodeQPairList c, p = qpClipGe (decodeRat m) p0 := by
  unfold clipGeListCode
  rw [mem_decodeQPairList_flatMapCode]
  constructor
  · rintro ⟨y, hy, hp⟩
    rw [decodeQPairList_singletonCode, List.mem_singleton, decodeRatPair_clipGeCode] at hp
    exact ⟨decodeRatPair y, (mem_decodeQPairList c (decodeRatPair y)).mpr ⟨y, hy, rfl⟩, hp⟩
  · rintro ⟨p0, hp0, hp⟩
    obtain ⟨y, hy, rfl⟩ := (mem_decodeQPairList c p0).mp hp0
    exact ⟨y, hy, by
      rw [decodeQPairList_singletonCode, List.mem_singleton, decodeRatPair_clipGeCode]; exact hp⟩

theorem presentedIntervals_decodeQPairList_clipLtListCode (m c : ℕ) :
    presentedIntervals (decodeQPairList (clipLtListCode m c)) =
      presentedIntervals (decodeQPairList c) ∩ Set.Iio (decodeRat m) := by
  rw [← presentedIntervals_map_qpClipLt]
  apply presentedIntervals_congr
  intro p
  rw [mem_decodeQPairList_clipLtListCode, List.mem_map]
  simp only [eq_comm]

theorem presentedIntervals_decodeQPairList_clipGeListCode (m c : ℕ) :
    presentedIntervals (decodeQPairList (clipGeListCode m c)) =
      presentedIntervals (decodeQPairList c) ∩ Set.Ici (decodeRat m) := by
  rw [← presentedIntervals_map_qpClipGe]
  apply presentedIntervals_congr
  intro p
  rw [mem_decodeQPairList_clipGeListCode, List.mem_map]
  simp only [eq_comm]

/-! ### The first pair of a non-empty list code -/

/-- The code of the head element of a non-empty list-code `c` (`decodeList c`'s head). Junk
(`0`'s `unpair.1`) when `c = 0`, but we only ever apply it to `canonCode n ≠ 0`
(`canonCode_ne_zero`). -/
def firstElemCode (c : ℕ) : ℕ := (c - 1).unpair.1

theorem primrec_firstElemCode : Nat.Primrec firstElemCode :=
  Nat.Primrec.left.comp primrec_pred

theorem mem_decodeQPairList_firstElemCode {c : ℕ} (hc : c ≠ 0) :
    decodeRatPair (firstElemCode c) ∈ decodeQPairList c := by
  obtain ⟨c', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hc
  have : firstElemCode (c' + 1) = c'.unpair.1 := by unfold firstElemCode; simp
  unfold decodeQPairList
  rw [this, decodeList_succ]
  exact List.mem_map_of_mem (by simp)

/-! ### `splitU`: the canonical midpoint split -/

/-- The midpoint code of the first pair of `canonCode n`'s presenting list. -/
def splitMidCode (n : ℕ) : ℕ := ratMidCode (firstElemCode (canonCode n))

theorem primrec_splitMidCode : Nat.Primrec splitMidCode :=
  (primrec_ratMidCode.comp (primrec_firstElemCode.comp primrec_canonCode)).of_eq fun n => by
    simp only [splitMidCode]

/-- The "left" half of the canonical split of `Xₙ`: `Xₙ ∩ (-∞, m)` for `m` the midpoint of `Xₙ`'s
first presenting pair. -/
def splitULeft (n : ℕ) : ℕ := clipLtListCode (splitMidCode n) (canonCode n)

/-- The "right" half of the canonical split of `Xₙ`: `Xₙ ∩ [m, ∞)`. -/
def splitURight (n : ℕ) : ℕ := clipGeListCode (splitMidCode n) (canonCode n)

theorem primrec_splitULeft : Nat.Primrec splitULeft :=
  (primrec_clipLtListCode.comp (primrec_splitMidCode.pair primrec_canonCode)).of_eq
    fun n => by simp only [splitULeft, unpair_pair_fst, unpair_pair_snd]

theorem primrec_splitURight : Nat.Primrec splitURight :=
  (primrec_clipGeListCode.comp (primrec_splitMidCode.pair primrec_canonCode)).of_eq
    fun n => by simp only [splitURight, unpair_pair_fst, unpair_pair_snd]

/-! ### Correctness -/

/-- The first pair `p₀` of `canonCode n`'s presenting list is non-degenerate, `p₀.1 < p₀.2`. -/
theorem splitU_p0_lt (n : ℕ) :
    (decodeRatPair (firstElemCode (canonCode n))).1 < (decodeRatPair (firstElemCode (canonCode n))).2 :=
  forall_lt_decodeQPairList_canonCode n _
    (mem_decodeQPairList_firstElemCode (canonCode_ne_zero n))

theorem splitU_mid_gt (n : ℕ) :
    (decodeRatPair (firstElemCode (canonCode n))).1 < decodeRat (splitMidCode n) := by
  show decodeRat (firstElemCode (canonCode n)).unpair.1 < decodeRat (splitMidCode n)
  unfold splitMidCode
  rw [decodeRat_ratMidCode']
  have h := splitU_p0_lt n
  unfold decodeRatPair at h
  exact left_lt_add_div_two.mpr h

theorem splitU_mid_lt (n : ℕ) :
    decodeRat (splitMidCode n) < (decodeRatPair (firstElemCode (canonCode n))).2 := by
  show decodeRat (splitMidCode n) < decodeRat (firstElemCode (canonCode n)).unpair.2
  unfold splitMidCode
  rw [decodeRat_ratMidCode']
  have h := splitU_p0_lt n
  unfold decodeRatPair at h
  exact add_div_two_lt_right.mpr h

theorem UX_splitULeft (n : ℕ) :
    UX (splitULeft n) = UX n ∩ Set.Iio (decodeRat (splitMidCode n)) := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (splitULeft n))) := by
    show U.mem (presentedIntervals (decodeQPairList (clipLtListCode (splitMidCode n) (canonCode n))))
    rw [presentedIntervals_decodeQPairList_clipLtListCode]
    refine ⟨⟨(decodeQPairList (canonCode n)).map (qpClipLt (decodeRat (splitMidCode n))),
      (presentedIntervals_map_qpClipLt _ _).symm⟩, ?_, ?_⟩
    · refine ⟨(decodeRatPair (firstElemCode (canonCode n))).1, ?_, splitU_mid_gt n⟩
      exact mem_presentedIntervals.mpr ⟨decodeRatPair (firstElemCode (canonCode n)),
        mem_decodeQPairList_firstElemCode (canonCode_ne_zero n), le_refl _, splitU_p0_lt n⟩
    · exact Set.inter_subset_left.trans (U_mem_UX n).2.2
  show presentedIntervals (decodeQPairList (canonCode (splitULeft n))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL]
  show presentedIntervals (decodeQPairList (clipLtListCode (splitMidCode n) (canonCode n))) = _
  rw [presentedIntervals_decodeQPairList_clipLtListCode]
  rfl

theorem UX_splitURight (n : ℕ) :
    UX (splitURight n) = UX n ∩ Set.Ici (decodeRat (splitMidCode n)) := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (splitURight n))) := by
    show U.mem (presentedIntervals (decodeQPairList (clipGeListCode (splitMidCode n) (canonCode n))))
    rw [presentedIntervals_decodeQPairList_clipGeListCode]
    refine ⟨⟨(decodeQPairList (canonCode n)).map (qpClipGe (decodeRat (splitMidCode n))),
      (presentedIntervals_map_qpClipGe _ _).symm⟩, ?_, ?_⟩
    · refine ⟨decodeRat (splitMidCode n), ?_, Set.self_mem_Ici⟩
      exact mem_presentedIntervals.mpr ⟨decodeRatPair (firstElemCode (canonCode n)),
        mem_decodeQPairList_firstElemCode (canonCode_ne_zero n), (splitU_mid_gt n).le, splitU_mid_lt n⟩
    · exact Set.inter_subset_left.trans (U_mem_UX n).2.2
  show presentedIntervals (decodeQPairList (canonCode (splitURight n))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL]
  show presentedIntervals (decodeQPairList (clipGeListCode (splitMidCode n) (canonCode n))) = _
  rw [presentedIntervals_decodeQPairList_clipGeListCode]
  rfl

/-- **Theorem 8.8(b) Part 4, disjointness**: `splitULeft`/`splitURight` cover disjoint pieces. -/
theorem splitU_disjoint (n : ℕ) : UX (splitULeft n) ∩ UX (splitURight n) = ∅ := by
  rw [UX_splitULeft, UX_splitURight]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨-, h1⟩, -, h2⟩
  exact absurd h1 (not_lt.mpr h2)

/-- **Theorem 8.8(b) Part 4, covering**: `splitULeft`/`splitURight` reunite to `Xₙ`. -/
theorem splitU_union (n : ℕ) : UX (splitULeft n) ∪ UX (splitURight n) = UX n := by
  rw [UX_splitULeft, UX_splitURight]
  ext x
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    rcases lt_or_ge x (decodeRat (splitMidCode n)) with hlt | hge
    · exact Or.inl ⟨h, hlt⟩
    · exact Or.inr ⟨h, hge⟩

/-- **Theorem 8.8(b) Part 4, properness (left)**: `splitULeft n` is a *proper* subset of `Xₙ`. -/
theorem splitU_left_ne (n : ℕ) : UX (splitULeft n) ≠ UX n := by
  intro hEq
  have hZsub : UX (splitURight n) ⊆ UX (splitULeft n) := by
    rw [hEq, UX_splitURight]; exact Set.inter_subset_left
  have hZempty : UX (splitURight n) ⊆ (∅ : Set ℚ) := by
    rw [← splitU_disjoint n]; exact Set.subset_inter hZsub subset_rfl
  exact (U_mem_UX (splitURight n)).2.1.ne_empty (Set.subset_empty_iff.mp hZempty)

/-- **Theorem 8.8(b) Part 4, properness (right)**: `splitURight n` is a *proper* subset of `Xₙ`. -/
theorem splitU_right_ne (n : ℕ) : UX (splitURight n) ≠ UX n := by
  intro hEq
  have hYsub : UX (splitULeft n) ⊆ UX (splitURight n) := by
    rw [hEq, UX_splitULeft]; exact Set.inter_subset_left
  have hYempty : UX (splitULeft n) ⊆ (∅ : Set ℚ) := by
    rw [← splitU_disjoint n]; exact Set.subset_inter subset_rfl hYsub
  exact (U_mem_UX (splitULeft n)).2.1.ne_empty (Set.subset_empty_iff.mp hYempty)

end Scott1980.Neighborhood

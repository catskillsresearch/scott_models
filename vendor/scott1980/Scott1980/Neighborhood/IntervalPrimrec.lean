/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Definition87
import Scott1980.Neighborhood.RationalPrimrec
import Scott1980.Neighborhood.RecursiveCross

/-!
# Primitive-recursive interval-list arithmetic for `𝒰` (Definition 8.7)

Builds the code-level analogue of `Definition87.lean`'s `List (ℚ × ℚ)` interval-presentation
machinery: encoding `List (ℚ × ℚ)` by `ℕ` (reusing `RationalPrimrec.lean`'s rational codes and
`Recursive.lean`'s `encodeList`), a genuinely `Nat.Primrec` **`combineCode`** realizing
`combineIntervals` at the code level (via `RecursiveCross.lean`'s `crossCombine`), and a
**canonicalization** `canonCode` that clips every code to a bona fide `𝒰`-neighbourhood (nonempty,
`⊆ [0,1)`), needed so `𝒰`'s eventual `ComputablePresentation.X` (`Definition71.lean`) is *total*
(every code indexes an actual neighbourhood).

All the `Nat.Primrec`/encoding results here are `⊆ {propext, Quot.sound}`. The set-level correctness
lemmas (`presentedIntervals_decodeQPairList_combineCode` and its helpers) additionally report
`Classical.choice` in `#print axioms`, but — exactly as documented in `Definition87.lean`'s own
"Axiom footprint" section — this is inherited from the *pinned Mathlib's* `ℚ` order instance itself
being `Classical.choice`-tainted, not from any classical reasoning performed in this file.
-/

namespace Scott1980.Neighborhood

open Domain.Recursive

/-! ### Encoding `List (ℚ × ℚ)` -/

/-- Encode a pair of rationals as a single natural. -/
def encodeRatPair (p : ℚ × ℚ) : ℕ := Nat.pair (encodeRat p.1) (encodeRat p.2)

/-- Decode a natural as a pair of rationals. -/
def decodeRatPair (c : ℕ) : ℚ × ℚ := (decodeRat c.unpair.1, decodeRat c.unpair.2)

@[simp] theorem decodeRatPair_encodeRatPair (p : ℚ × ℚ) : decodeRatPair (encodeRatPair p) = p := by
  unfold decodeRatPair encodeRatPair
  simp only [unpair_pair_fst, unpair_pair_snd, decodeRat_encodeRat]

/-- Encode a list of rational pairs as a single natural, via `encodeList`. -/
def encodeQPairList (L : List (ℚ × ℚ)) : ℕ := encodeList (L.map encodeRatPair)

/-- Decode a natural as a list of rational pairs. -/
def decodeQPairList (c : ℕ) : List (ℚ × ℚ) := (decodeList c).map decodeRatPair

/-- **Exact round trip**: `decodeQPairList (encodeQPairList L) = L` for every `L`. -/
@[simp] theorem decodeQPairList_encodeQPairList (L : List (ℚ × ℚ)) :
    decodeQPairList (encodeQPairList L) = L := by
  unfold decodeQPairList encodeQPairList
  rw [decodeList_encodeList, List.map_map]
  simp only [Function.comp_def, decodeRatPair_encodeRatPair, List.map_id_fun', id]

theorem mem_decodeQPairList (c : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList c ↔ ∃ e ∈ decodeList c, p = decodeRatPair e := by
  unfold decodeQPairList; rw [List.mem_map]; simp [eq_comm]

/-! ### `combineIntervals` at the code level -/

/-- The per-pair-code operation `(pc, qc) ↦ (max, min)` realizing `(p.1 ⊔ q.1, p.2 ⊓ q.2)`. -/
def qpCombineBop (t : ℕ) : ℕ :=
  Nat.pair (ratMaxCode (Nat.pair t.unpair.1.unpair.1 t.unpair.2.unpair.1))
    (ratMinCode (Nat.pair t.unpair.1.unpair.2 t.unpair.2.unpair.2))

theorem primrec_qpCombineBop : Nat.Primrec qpCombineBop := by
  have h11 : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.left
  have h12 : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.left
  have h21 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have h22 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact ((primrec_ratMaxCode.comp (h11.pair h21)).pair
    (primrec_ratMinCode.comp (h12.pair h22))).of_eq fun _ => rfl

theorem decodeRatPair_qpCombineBop (e1 e2 : ℕ) :
    decodeRatPair (qpCombineBop (Nat.pair e1 e2))
      = ((decodeRatPair e1).1 ⊔ (decodeRatPair e2).1, (decodeRatPair e1).2 ⊓ (decodeRatPair e2).2) := by
  unfold qpCombineBop decodeRatPair
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [decodeRat_ratMaxCode, decodeRat_ratMinCode]

/-- `combineCode` realizes `combineIntervals` on codes: `Nat.Primrec` in both arguments. -/
def combineCode (c1 c2 : ℕ) : ℕ := crossCombine qpCombineBop c1 c2

theorem primrec_combineCode : Nat.Primrec (fun t => combineCode t.unpair.1 t.unpair.2) :=
  primrec_crossCombine primrec_qpCombineBop

theorem mem_decodeQPairList_combineCode (c1 c2 : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (combineCode c1 c2) ↔
      ∃ p1 ∈ decodeQPairList c1, ∃ p2 ∈ decodeQPairList c2, p = (p1.1 ⊔ p2.1, p1.2 ⊓ p2.2) := by
  unfold decodeQPairList combineCode
  rw [List.mem_map]
  constructor
  · rintro ⟨z, hz, hpz⟩
    rw [mem_decodeList_crossCombine] at hz
    obtain ⟨e1, he1, e2, he2, hze⟩ := hz
    refine ⟨decodeRatPair e1, List.mem_map_of_mem he1, decodeRatPair e2, List.mem_map_of_mem he2, ?_⟩
    rw [← hpz, hze, decodeRatPair_qpCombineBop]
  · rintro ⟨p1, hp1, p2, hp2, hp⟩
    obtain ⟨e1, he1, he1'⟩ := List.mem_map.mp hp1
    obtain ⟨e2, he2, he2'⟩ := List.mem_map.mp hp2
    refine ⟨qpCombineBop (Nat.pair e1 e2),
      (mem_decodeList_crossCombine (bop := qpCombineBop) c1 c2 _).mpr ⟨e1, he1, e2, he2, rfl⟩, ?_⟩
    rw [decodeRatPair_qpCombineBop, he1', he2', hp]

/-- Two lists with the same **elements** present the same set. -/
theorem presentedIntervals_congr {L1 L2 : List (ℚ × ℚ)} (h : ∀ p, p ∈ L1 ↔ p ∈ L2) :
    presentedIntervals L1 = presentedIntervals L2 := by
  ext x
  simp only [mem_presentedIntervals]
  constructor
  · rintro ⟨p, hp, h1, h2⟩; exact ⟨p, (h p).mp hp, h1, h2⟩
  · rintro ⟨p, hp, h1, h2⟩; exact ⟨p, (h p).mpr hp, h1, h2⟩

theorem mem_combineIntervals {L1 L2 : List (ℚ × ℚ)} {p : ℚ × ℚ} :
    p ∈ combineIntervals L1 L2 ↔ ∃ p1 ∈ L1, ∃ p2 ∈ L2, p = (p1.1 ⊔ p2.1, p1.2 ⊓ p2.2) := by
  unfold combineIntervals
  rw [List.mem_flatMap]
  simp only [List.mem_map, eq_comm]

/-- **`combineCode` realizes `combineIntervals` at the set level.** -/
theorem presentedIntervals_decodeQPairList_combineCode (c1 c2 : ℕ) :
    presentedIntervals (decodeQPairList (combineCode c1 c2))
      = presentedIntervals (decodeQPairList c1) ∩ presentedIntervals (decodeQPairList c2) := by
  rw [presentedIntervals_inter]
  apply presentedIntervals_congr
  intro p
  rw [mem_decodeQPairList_combineCode, mem_combineIntervals]

/-! ## Interval-list *difference*, needed for subset/equality decidability

`ComputablePresentation`'s relations (i)/(ii) (`Definition71.lean`) both ultimately reduce to
deciding whether one presented set is *empty* or a *subset* of another. Non-emptiness is a cheap
bounded-`∃` (`p.1 < p.2` for some `p` in the list, via `Recursive.lean`'s `existsListChar`), but
subset needs genuine interval-covering arithmetic: `L1 ⊆ L2 ↔ presentedIntervals L1 \ presentedIntervals L2
= ∅`, computed here by an explicit `diffLists`. As with `combineIntervals`, everything is built from
the *unconditional* identity `Set.Ico_diff_Ico` (no side conditions on endpoint order), first at the
pure list level (`diffOneList`/`diffSingleList`/`diffAllList`/`diffLists`), then mirrored at the
`Nat.Primrec` code level (`diffOneCode`/`diffSingleCode`/`diffAllCode`/`diffCode`) via
`RecursiveCross.lean`'s `flatMapCode`. -/

/-- **Unconditional interval difference**: `Ico a b \ Ico c d = Ico a (b ⊓ c) ∪ Ico (a ⊔ d) b`, with
no ordering hypotheses on `a, b, c, d` (mirrors `Set.Ico_inter_Ico`'s unconditional intersection
formula). -/
theorem Ico_diff_Ico (a b c d : ℚ) :
    Set.Ico a b \ Set.Ico c d = Set.Ico a (b ⊓ c) ∪ Set.Ico (a ⊔ d) b := by
  ext x
  simp only [Set.mem_diff, Set.mem_Ico, Set.mem_union, lt_inf_iff, sup_le_iff]
  constructor
  · rintro ⟨⟨ha, hb⟩, hcd⟩
    rcases lt_or_ge x c with hc | hc
    · exact Or.inl ⟨ha, hb, hc⟩
    · rcases lt_or_ge x d with hd | hd
      · exact absurd ⟨hc, hd⟩ hcd
      · exact Or.inr ⟨⟨ha, hd⟩, hb⟩
  · rintro (⟨ha, hb, hc⟩ | ⟨⟨ha, hd⟩, hb⟩)
    · exact ⟨⟨ha, hb⟩, fun ⟨hc', _⟩ => absurd hc' (not_le.mpr hc)⟩
    · exact ⟨⟨ha, hb⟩, fun ⟨_, hd'⟩ => absurd hd' (not_lt.mpr hd)⟩

/-- **Difference of a single interval-pair by another**, as a `≤ 2`-element list, via the
unconditional `Ico_diff_Ico`. -/
def diffOneList (p q : ℚ × ℚ) : List (ℚ × ℚ) := [(p.1, p.2 ⊓ q.1), (p.1 ⊔ q.2, p.2)]

theorem presentedIntervals_diffOneList (p q : ℚ × ℚ) :
    presentedIntervals (diffOneList p q) = Set.Ico p.1 p.2 \ Set.Ico q.1 q.2 := by
  unfold diffOneList
  rw [presentedIntervals_cons, presentedIntervals_cons, presentedIntervals_nil, Set.union_empty]
  exact (Ico_diff_Ico p.1 p.2 q.1 q.2).symm

/-- **Subtract a single interval-pair `q` from a whole presenting list `L`.** -/
def diffSingleList (L : List (ℚ × ℚ)) (q : ℚ × ℚ) : List (ℚ × ℚ) :=
  L.flatMap (fun p => diffOneList p q)

theorem presentedIntervals_diffSingleList (L : List (ℚ × ℚ)) (q : ℚ × ℚ) :
    presentedIntervals (diffSingleList L q) = presentedIntervals L \ Set.Ico q.1 q.2 := by
  induction L with
  | nil => simp [diffSingleList]
  | cons a l ih =>
    rw [show diffSingleList (a :: l) q = diffOneList a q ++ diffSingleList l q from rfl,
      presentedIntervals_append, presentedIntervals_diffOneList, ih, presentedIntervals_cons,
      Set.union_diff_distrib]

/-- **Subtract a whole presenting list `L2` from a single interval-pair `p`**, by folding
`diffSingleList` over `L2`, starting from `[p]`. -/
def diffAllList (p : ℚ × ℚ) (L2 : List (ℚ × ℚ)) : List (ℚ × ℚ) := L2.foldl diffSingleList [p]

theorem presentedIntervals_foldl_diffSingleList (L2 : List (ℚ × ℚ)) :
    ∀ acc : List (ℚ × ℚ),
      presentedIntervals (L2.foldl diffSingleList acc) = presentedIntervals acc \ presentedIntervals L2 := by
  induction L2 with
  | nil => intro acc; simp
  | cons a l ih =>
    intro acc
    rw [List.foldl_cons, ih (diffSingleList acc a), presentedIntervals_diffSingleList,
      presentedIntervals_cons, Set.diff_diff]

theorem presentedIntervals_diffAllList (p : ℚ × ℚ) (L2 : List (ℚ × ℚ)) :
    presentedIntervals (diffAllList p L2) = Set.Ico p.1 p.2 \ presentedIntervals L2 := by
  unfold diffAllList
  rw [presentedIntervals_foldl_diffSingleList, presentedIntervals_cons, presentedIntervals_nil,
    Set.union_empty]

/-- **Subtract `L2` from `L1`**, presenting the set difference `presentedIntervals L1 \\
presentedIntervals L2`. -/
def diffLists (L1 L2 : List (ℚ × ℚ)) : List (ℚ × ℚ) := L1.flatMap (fun p => diffAllList p L2)

theorem presentedIntervals_diffLists (L1 L2 : List (ℚ × ℚ)) :
    presentedIntervals (diffLists L1 L2) = presentedIntervals L1 \ presentedIntervals L2 := by
  induction L1 with
  | nil => simp [diffLists]
  | cons a l ih =>
    rw [show diffLists (a :: l) L2 = diffAllList a L2 ++ diffLists l L2 from rfl,
      presentedIntervals_append, presentedIntervals_diffAllList, ih, presentedIntervals_cons,
      Set.union_diff_distrib]

/-! ### The code level: `diffOneCode`/`diffSingleCode`/`diffAllCode`/`diffCode` -/

/-- Code-level `diffOneList`, taking `t = pair qc pc` (subtracted interval `q` **first**, matching
`flatMapCode`'s calling convention). -/
def diffOneCode (t : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair t.unpair.2.unpair.1 (ratMinCode (Nat.pair t.unpair.2.unpair.2 t.unpair.1.unpair.1)))
    (Nat.pair (Nat.pair (ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.2))
      t.unpair.2.unpair.2) 0 + 1) + 1

theorem primrec_diffOneCode : Nat.Primrec diffOneCode := by
  have ha : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hb : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hc : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have hd : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.left
  have hleft : Nat.Primrec (fun t : ℕ =>
      Nat.pair t.unpair.2.unpair.1 (ratMinCode (Nat.pair t.unpair.2.unpair.2 t.unpair.1.unpair.1))) :=
    ha.pair (primrec_ratMinCode.comp (hb.pair hc))
  have hright : Nat.Primrec (fun t : ℕ =>
      Nat.pair (ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.2)) t.unpair.2.unpair.2) :=
    (primrec_ratMaxCode.comp (ha.pair hd)).pair hb
  exact (Nat.Primrec.succ.comp (hleft.pair
    (Nat.Primrec.succ.comp (hright.pair (Nat.Primrec.const 0))))).of_eq fun _ => rfl

theorem decodeQPairList_diffOneCode (qc pc : ℕ) :
    decodeQPairList (diffOneCode (Nat.pair qc pc)) = diffOneList (decodeRatPair pc) (decodeRatPair qc) := by
  unfold diffOneCode decodeQPairList diffOneList decodeRatPair
  simp only [unpair_pair_fst, unpair_pair_snd, decodeList_succ, decodeList_zero, List.map_cons,
    List.map_nil]
  rw [decodeRat_ratMinCode, decodeRat_ratMaxCode]

/-- **`flatMapCode`'s membership correctness, lifted to `decodeQPairList`.** -/
theorem mem_decodeQPairList_flatMapCode (f : ℕ → ℕ) (x c : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (flatMapCode f x c) ↔ ∃ y ∈ decodeList c, p ∈ decodeQPairList (f (Nat.pair x y)) := by
  unfold decodeQPairList
  rw [List.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_decodeList_flatMapCode] at hz
    obtain ⟨y, hy, hz'⟩ := hz
    exact ⟨y, hy, List.mem_map_of_mem hz'⟩
  · rintro ⟨y, hy, hp⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
    exact ⟨e, (mem_decodeList_flatMapCode (f := f) x c e).mpr ⟨y, hy, he⟩, rfl⟩

/-- `diffSingleCode accL q` subtracts the single interval-pair coded by `q` from the whole
QPair-list coded by `accL`. -/
def diffSingleCode (accL q : ℕ) : ℕ := flatMapCode diffOneCode q accL

theorem primrec_diffSingleCode : Nat.Primrec (fun t : ℕ => diffSingleCode t.unpair.1 t.unpair.2) := by
  unfold diffSingleCode
  exact ((primrec_flatMapCode primrec_diffOneCode).comp (Nat.Primrec.right.pair Nat.Primrec.left)).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]

theorem mem_decodeQPairList_diffSingleCode (accL q : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (diffSingleCode accL q) ↔ p ∈ diffSingleList (decodeQPairList accL) (decodeRatPair q) := by
  unfold diffSingleCode
  rw [mem_decodeQPairList_flatMapCode]
  simp only [decodeQPairList_diffOneCode]
  unfold diffSingleList decodeQPairList
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨y, hy, hp⟩; exact ⟨decodeRatPair y, ⟨y, hy, rfl⟩, hp⟩
  · rintro ⟨p', ⟨y, hy, rfl⟩, hp⟩; exact ⟨y, hy, hp⟩

theorem presentedIntervals_decodeQPairList_diffSingleCode (accL q : ℕ) :
    presentedIntervals (decodeQPairList (diffSingleCode accL q))
      = presentedIntervals (decodeQPairList accL) \ Set.Ico (decodeRatPair q).1 (decodeRatPair q).2 := by
  rw [presentedIntervals_congr (mem_decodeQPairList_diffSingleCode accL q), presentedIntervals_diffSingleList]

/-- `foldCode`'s step for `diffAllCode`'s fold over `L2` (params unused): pops `q`, subtracts it
from the "remaining pieces" accumulator via `diffSingleCode`. -/
def diffAllStep (w : ℕ) : ℕ := diffSingleCode w.unpair.2.unpair.1 w.unpair.1

theorem primrec_diffAllStep : Nat.Primrec diffAllStep := by
  unfold diffAllStep
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hq : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  exact (primrec_diffSingleCode.comp (hacc.pair hq)).of_eq fun w => by
    simp only [unpair_pair_fst, unpair_pair_snd]

/-- `diffAllCode pc L2` subtracts the whole QPair-list coded by `L2` from the single interval-pair
coded by `pc`, folding `diffSingleCode` over `L2` from the seed `[pc]`. -/
def diffAllCode (pc L2 : ℕ) : ℕ := foldCode diffAllStep 0 (Nat.pair pc 0 + 1) L2

theorem primrec_diffAllCode : Nat.Primrec (fun t : ℕ => diffAllCode t.unpair.1 t.unpair.2) :=
  (primrec_foldCode primrec_diffAllStep (Nat.Primrec.const 0)
    (Nat.Primrec.succ.comp (Nat.Primrec.left.pair (Nat.Primrec.const 0)))
    Nat.Primrec.right).of_eq fun _ => rfl

theorem diffAllStep_eq (acc x : ℕ) : diffAllStep (Nat.pair x (Nat.pair acc 0)) = diffSingleCode acc x := by
  unfold diffAllStep; simp only [unpair_pair_fst, unpair_pair_snd]

theorem presentedIntervals_decodeQPairList_foldl_diffAllStep (L2list : List ℕ) :
    ∀ acc : ℕ, presentedIntervals (decodeQPairList
        (List.foldl (fun acc x => diffAllStep (Nat.pair x (Nat.pair acc 0))) acc L2list))
      = presentedIntervals (decodeQPairList acc) \ presentedIntervals (L2list.map decodeRatPair) := by
  induction L2list with
  | nil => intro acc; simp
  | cons a l ih =>
    intro acc
    rw [List.foldl_cons, diffAllStep_eq, ih (diffSingleCode acc a),
      presentedIntervals_decodeQPairList_diffSingleCode, List.map_cons, presentedIntervals_cons,
      Set.diff_diff]

theorem presentedIntervals_decodeQPairList_diffAllCode (pc L2 : ℕ) :
    presentedIntervals (decodeQPairList (diffAllCode pc L2))
      = Set.Ico (decodeRatPair pc).1 (decodeRatPair pc).2 \ presentedIntervals (decodeQPairList L2) := by
  unfold diffAllCode
  rw [foldCode_eq', presentedIntervals_decodeQPairList_foldl_diffAllStep]
  unfold decodeQPairList
  simp only [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero, List.map_cons,
    List.map_nil, presentedIntervals_cons, presentedIntervals_nil, Set.union_empty]

/-- `diffCode c1 c2` subtracts the QPair-list coded by `c2` from the QPair-list coded by `c1`. -/
def diffCode (c1 c2 : ℕ) : ℕ := flatMapCode (fun t => diffAllCode t.unpair.2 t.unpair.1) c2 c1

theorem primrec_diffCode : Nat.Primrec (fun t : ℕ => diffCode t.unpair.1 t.unpair.2) := by
  unfold diffCode
  have hf : Nat.Primrec (fun t : ℕ => diffAllCode t.unpair.2 t.unpair.1) :=
    (primrec_diffAllCode.comp (Nat.Primrec.right.pair Nat.Primrec.left)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact ((primrec_flatMapCode hf).comp (Nat.Primrec.right.pair Nat.Primrec.left)).of_eq fun t => by
    simp only [unpair_pair_fst, unpair_pair_snd]

theorem mem_decodeQPairList_diffCode (c1 c2 : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (diffCode c1 c2) ↔ ∃ y ∈ decodeList c1, p ∈ decodeQPairList (diffAllCode y c2) := by
  unfold diffCode
  rw [mem_decodeQPairList_flatMapCode]
  refine exists_congr fun y => and_congr_right fun _ => ?_
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem presentedIntervals_decodeQPairList_flatMap_diffAllCode (c1list : List ℕ) (c2 : ℕ) :
    presentedIntervals (c1list.flatMap (fun y => decodeQPairList (diffAllCode y c2)))
      = presentedIntervals (c1list.map decodeRatPair) \ presentedIntervals (decodeQPairList c2) := by
  induction c1list with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_cons, presentedIntervals_append,
      presentedIntervals_decodeQPairList_diffAllCode, ih, presentedIntervals_cons,
      Set.union_diff_distrib]

/-- **`diffCode` realizes `diffLists` (hence set difference) at the set level.** -/
theorem presentedIntervals_decodeQPairList_diffCode (c1 c2 : ℕ) :
    presentedIntervals (decodeQPairList (diffCode c1 c2))
      = presentedIntervals (decodeQPairList c1) \ presentedIntervals (decodeQPairList c2) := by
  rw [presentedIntervals_congr
      (fun p => (mem_decodeQPairList_diffCode c1 c2 p).trans (List.mem_flatMap).symm),
    presentedIntervals_decodeQPairList_flatMap_diffAllCode]
  rfl

/-! ## Decidability of non-emptiness, subset, and equality of `presentedIntervals`

`ComputablePresentation`'s relations (i)/(ii) (`Definition71.lean`) reduce, via `𝒰`'s canonical
enumeration (Part 3), to deciding membership questions about `presentedIntervals`-coded sets. The
key primitive is **non-emptiness**: `presentedIntervals L` is non-empty iff some pair `p ∈ L` has
`p.1 < p.2` (`presentedIntervals_nonempty_iff`), a cheap bounded-`∃` over the list
(`Recursive.lean`'s `existsListChar`). Subset and equality then reduce to non-emptiness of
`diffCode`, reusing `presentedIntervals_decodeQPairList_diffCode` above — no new arithmetic is
needed. -/

/-- **A presented union of intervals is non-empty iff some pair in the list is itself non-degenerate**
(`p.1 < p.2`): every degenerate pair contributes the empty interval, and a single non-degenerate pair
already witnesses non-emptiness (via its left endpoint). -/
theorem presentedIntervals_nonempty_iff (L : List (ℚ × ℚ)) :
    (presentedIntervals L).Nonempty ↔ ∃ p ∈ L, p.1 < p.2 := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨p, hp, hx1, hx2⟩ := mem_presentedIntervals.mp hx
    exact ⟨p, hp, lt_of_le_of_lt hx1 hx2⟩
  · rintro ⟨p, hp, hlt⟩
    exact ⟨p.1, mem_presentedIntervals.mpr ⟨p, hp, le_refl _, hlt⟩⟩

/-- The `{0,1}` flag: does the rational-pair code `e` decode to a non-degenerate pair `p.1 < p.2`? -/
def qpNonemptyBop (e : ℕ) : ℕ := ratLtCode (Nat.pair e.unpair.1 e.unpair.2)

theorem primrec_qpNonemptyBop : Nat.Primrec qpNonemptyBop :=
  primrec_ratLtCode.comp (Nat.Primrec.left.pair Nat.Primrec.right)

theorem qpNonemptyBop_eq_one_iff (e : ℕ) :
    qpNonemptyBop e = 1 ↔ (decodeRatPair e).1 < (decodeRatPair e).2 := by
  unfold qpNonemptyBop decodeRatPair; exact ratLtCode_eq_one_iff e.unpair.1 e.unpair.2

/-- The `{0,1}` flag: does the QPair-list code `c` present a non-empty set? A bounded `∃` over
`decodeList c` via `Recursive.lean`'s `existsListChar` (the second argument of `existsListChar` is
an unused parameter, fixed to `0`). -/
def qpNonemptyChar (c : ℕ) : ℕ := existsListChar (fun t => qpNonemptyBop t.unpair.1) 0 c

theorem primrec_qpNonemptyChar : Nat.Primrec qpNonemptyChar := by
  have hg : Nat.Primrec (fun t : ℕ => qpNonemptyBop t.unpair.1) :=
    primrec_qpNonemptyBop.comp Nat.Primrec.left
  exact ((primrec_existsListChar hg).comp (primrec_id.pair (Nat.Primrec.const 0))).of_eq
    fun c => by
      unfold qpNonemptyChar
      simp only [id, unpair_pair_fst, unpair_pair_snd]

theorem qpNonemptyChar_le_one (c : ℕ) : qpNonemptyChar c ≤ 1 := existsListChar_le_one _ 0 c

theorem qpNonemptyChar_eq_one_iff (c : ℕ) :
    qpNonemptyChar c = 1 ↔ ∃ e ∈ decodeList c, (decodeRatPair e).1 < (decodeRatPair e).2 := by
  unfold qpNonemptyChar
  rw [existsListChar_eq_one_iff]
  refine exists_congr fun e => and_congr_right fun _ => ?_
  rw [unpair_pair_fst, qpNonemptyBop_eq_one_iff]

/-- **`presentedIntervals (decodeQPairList c)` is non-empty iff `qpNonemptyChar c = 1`.** -/
theorem presentedIntervals_decodeQPairList_nonempty_iff (c : ℕ) :
    (presentedIntervals (decodeQPairList c)).Nonempty ↔ qpNonemptyChar c = 1 := by
  rw [presentedIntervals_nonempty_iff, qpNonemptyChar_eq_one_iff]
  constructor
  · rintro ⟨p, hp, hlt⟩
    obtain ⟨e, he, rfl⟩ := (mem_decodeQPairList c p).mp hp
    exact ⟨e, he, hlt⟩
  · rintro ⟨e, he, hlt⟩
    exact ⟨decodeRatPair e, (mem_decodeQPairList c (decodeRatPair e)).mpr ⟨e, he, rfl⟩, hlt⟩

/-- **Non-emptiness of the set presented by a QPair-list code is recursively decidable.** -/
theorem recDecidable_presentedIntervals_nonempty :
    RecDecidable (fun c => (presentedIntervals (decodeQPairList c)).Nonempty) :=
  RecDecidable.of_zero_one_char primrec_qpNonemptyChar
    (fun c => by have := qpNonemptyChar_le_one c; omega)
    presentedIntervals_decodeQPairList_nonempty_iff

/-- **Subset between `presentedIntervals`-coded sets reduces to non-emptiness of `diffCode`.** -/
theorem presentedIntervals_decodeQPairList_subset_iff (c1 c2 : ℕ) :
    presentedIntervals (decodeQPairList c1) ⊆ presentedIntervals (decodeQPairList c2) ↔
      ¬ (presentedIntervals (decodeQPairList (diffCode c1 c2))).Nonempty := by
  rw [presentedIntervals_decodeQPairList_diffCode, Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty]

/-- **Subset between `presentedIntervals`-coded sets is recursively decidable.** -/
theorem recDecidable₂_presentedIntervals_subset :
    RecDecidable₂ (fun c1 c2 =>
      presentedIntervals (decodeQPairList c1) ⊆ presentedIntervals (decodeQPairList c2)) := by
  unfold RecDecidable₂
  refine RecDecidable.of_iff (fun t => ?_)
    (recDecidable_presentedIntervals_nonempty.comp primrec_diffCode).not
  exact presentedIntervals_decodeQPairList_subset_iff t.unpair.1 t.unpair.2

/-- **Equality between `presentedIntervals`-coded sets is recursively decidable**, from
`recDecidable₂_presentedIntervals_subset` in both directions (`Set.Subset.antisymm_iff`). -/
theorem recDecidable₂_presentedIntervals_eq :
    RecDecidable₂ (fun c1 c2 =>
      presentedIntervals (decodeQPairList c1) = presentedIntervals (decodeQPairList c2)) := by
  unfold RecDecidable₂
  refine RecDecidable.of_iff (fun t => ?_)
    (recDecidable₂_presentedIntervals_subset.and recDecidable₂_presentedIntervals_subset.swap)
  exact Set.Subset.antisymm_iff

end Scott1980.Neighborhood

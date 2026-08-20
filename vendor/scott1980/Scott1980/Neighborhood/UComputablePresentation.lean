/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.IntervalPrimrec
import Scott1980.Neighborhood.Definition71

/-!
# Theorem 8.8(b), Part 3 — `𝒰` (Definition 8.7) has a genuine `ComputablePresentation`

Assembles `Definition71.lean`'s `ComputablePresentation U` from `IntervalPrimrec.lean`'s code-level
interval arithmetic and decidability results, proving `U.IsEffectivelyGiven`.

## The enumeration

Every natural `c` codes a `List (ℚ × ℚ)` (`decodeQPairList`), but not every such list presents a
genuine `U`-neighbourhood (it may be empty, or stray outside `[0,1)`). `canonList` **canonicalizes**
an arbitrary list to one that does: clip every pair into `[0,1)` (`qpClip`, mirroring
`Definition87.lean`'s private `clip`) and discard now-degenerate pairs, falling back to the single
pair `(0,1)` (presenting `U.master`) if nothing survives. `canonList_fixed` is the key reuse lemma:
canonicalizing a list that **already** presents a `U`-neighbourhood changes nothing (as a set) — this
drives both `surj` (every `U`-neighbourhood has a Scott-literal presenting list, by `U_mem_iff_scott`,
on which `canonList` is a no-op) and `inter_spec` (the raw `combineCode` output, when non-empty, is
already a `U`-neighbourhood, so re-canonicalizing it is also a no-op).

`canonCode` mirrors `canonList` at the `Nat.Primrec` level (`canonListCode` performs the clip/filter
via `RecursiveCross.lean`'s `flatMapCode`; a final `selectFn`/`isZero` test supplies the `(0,1)`
fallback), with `presentedIntervals_decodeQPairList_canonCode` bridging the two. `X n :=
presentedIntervals (decodeQPairList (canonCode n))` is then `𝒰`'s enumeration, and Scott's two
relations reduce directly to `IntervalPrimrec.lean`'s `recDecidable₂_presentedIntervals_eq`/
`recDecidable_presentedIntervals_nonempty` (intersection is a *raw* `combineCode`, and — since `U`
is so permissive — is automatically a genuine `U`-neighbourhood whenever it is non-empty, so
"consistent" reduces to "non-empty").
-/

namespace Scott1980.Neighborhood

open Domain.Recursive NeighborhoodSystem

/-! ### List-level canonicalization -/

/-- Clip a rational pair to `[0,1)`, moving `r` up to `0` and `s` down to `1` when needed. Mirrors
`Definition87.lean`'s `private def clip`, redefined here (public) since `canonList`/`canonCode` need
both a list-level and a code-level version of it. -/
def qpClip (p : ℚ × ℚ) : ℚ × ℚ := (p.1 ⊔ 0, p.2 ⊓ 1)

theorem presentedIntervals_map_qpClip (L : List (ℚ × ℚ)) :
    presentedIntervals (L.map qpClip) = presentedIntervals L ∩ Set.Ico (0 : ℚ) 1 := by
  ext x
  simp only [mem_presentedIntervals, List.mem_map, Set.mem_inter_iff, Set.mem_Ico, qpClip]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hx1, hx2⟩
    exact ⟨⟨q, hq, le_sup_left.trans hx1, hx2.trans_le inf_le_left⟩,
      le_sup_right.trans hx1, hx2.trans_le inf_le_right⟩
  · rintro ⟨⟨q, hq, hxq1, hxq2⟩, hx0, hx1⟩
    exact ⟨(q.1 ⊔ 0, q.2 ⊓ 1), ⟨q, hq, rfl⟩, sup_le hxq1 hx0, lt_inf_iff.mpr ⟨hxq2, hx1⟩⟩

theorem presentedIntervals_filter_qpPos (L : List (ℚ × ℚ)) :
    presentedIntervals (L.filter (fun p => decide (p.1 < p.2))) = presentedIntervals L := by
  ext x
  simp only [mem_presentedIntervals, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨p, ⟨hp, -⟩, hx⟩
    exact ⟨p, hp, hx⟩
  · rintro ⟨p, hp, hx1, hx2⟩
    exact ⟨p, ⟨hp, lt_of_le_of_lt hx1 hx2⟩, hx1, hx2⟩

/-- **Canonicalize** an arbitrary presenting list into one that presents a genuine
`U`-neighbourhood: clip every pair into `[0,1)` and discard degenerate pairs, falling back to the
single pair `(0,1)` (presenting `U.master`) if nothing survives. -/
def canonList (L : List (ℚ × ℚ)) : List (ℚ × ℚ) :=
  match (L.map qpClip).filter (fun p => decide (p.1 < p.2)) with
  | [] => [((0 : ℚ), (1 : ℚ))]
  | L' => L'

/-- Unfolding equation for `canonList` on the `nil` branch, stated so `rw` can fire on a literal
occurrence of `canonList L` (rather than needing to see through the `match`). -/
theorem canonList_eq_of_filter_eq_nil {L : List (ℚ × ℚ)}
    (h : (L.map qpClip).filter (fun p => decide (p.1 < p.2)) = []) :
    canonList L = [((0 : ℚ), (1 : ℚ))] := by
  unfold canonList; rw [h]

/-- Unfolding equation for `canonList` on the `cons` branch. -/
theorem canonList_eq_of_filter_eq_cons {L : List (ℚ × ℚ)} {a : ℚ × ℚ} {l : List (ℚ × ℚ)}
    (h : (L.map qpClip).filter (fun p => decide (p.1 < p.2)) = a :: l) :
    canonList L = a :: l := by
  unfold canonList; rw [h]

/-- **`canonList` always presents a genuine `U`-neighbourhood.** -/
theorem U_mem_presentedIntervals_canonList (L : List (ℚ × ℚ)) :
    U.mem (presentedIntervals (canonList L)) := by
  rcases hL : (L.map qpClip).filter (fun p => decide (p.1 < p.2)) with _ | ⟨a, l⟩
  · rw [canonList_eq_of_filter_eq_nil hL]
    have heq : presentedIntervals ([((0 : ℚ), (1 : ℚ))]) = U.master := by
      rw [presentedIntervals_cons, presentedIntervals_nil, Set.union_empty]; rfl
    rw [heq]; exact U.master_mem
  · rw [canonList_eq_of_filter_eq_cons hL]
    have hL'eq : presentedIntervals (a :: l) = presentedIntervals L ∩ Set.Ico (0 : ℚ) 1 := by
      rw [← hL, presentedIntervals_filter_qpPos, presentedIntervals_map_qpClip]
    have hmem : a ∈ (L.map qpClip).filter (fun p => decide (p.1 < p.2)) := by
      rw [hL]; exact List.mem_cons.mpr (Or.inl rfl)
    have ha : a.1 < a.2 := by simpa using (List.mem_filter.mp hmem).2
    refine ⟨⟨a :: l, rfl⟩, ?_, hL'eq ▸ Set.inter_subset_right⟩
    exact ⟨a.1, mem_presentedIntervals.mpr ⟨a, List.mem_cons.mpr (Or.inl rfl), le_refl _, ha⟩⟩

/-- **`canonList` is a no-op (as a set) on a list that already presents a `U`-neighbourhood.** -/
theorem canonList_fixed {L : List (ℚ × ℚ)} (h : U.mem (presentedIntervals L)) :
    presentedIntervals (canonList L) = presentedIntervals L := by
  obtain ⟨-, hne, hsub⟩ := h
  rcases hL : (L.map qpClip).filter (fun p => decide (p.1 < p.2)) with _ | ⟨a, l⟩
  · exfalso
    have hcontra : presentedIntervals L ∩ Set.Ico (0 : ℚ) 1 = ∅ := by
      rw [← presentedIntervals_map_qpClip, ← presentedIntervals_filter_qpPos (L.map qpClip), hL,
        presentedIntervals_nil]
    rw [Set.inter_eq_left.mpr hsub] at hcontra
    exact hne.ne_empty hcontra
  · rw [canonList_eq_of_filter_eq_cons hL, ← hL, presentedIntervals_filter_qpPos,
      presentedIntervals_map_qpClip, Set.inter_eq_left.mpr hsub]

/-! ### Code-level canonicalization: `canonCode` -/

/-- Code-level `qpClip`: `(r,s) ↦ (r⊔0, s⊓1)` on a rational-pair code. -/
def qpClipCode (e : ℕ) : ℕ :=
  Nat.pair (ratMaxCode (Nat.pair e.unpair.1 zeroCode)) (ratMinCode (Nat.pair e.unpair.2 oneCode))

theorem primrec_qpClipCode : Nat.Primrec qpClipCode := by
  have h1 : Nat.Primrec (fun e : ℕ => e.unpair.1) := Nat.Primrec.left
  have h2 : Nat.Primrec (fun e : ℕ => e.unpair.2) := Nat.Primrec.right
  exact ((primrec_ratMaxCode.comp (h1.pair (Nat.Primrec.const zeroCode))).pair
    (primrec_ratMinCode.comp (h2.pair (Nat.Primrec.const oneCode)))).of_eq fun _ => rfl

theorem decodeRatPair_qpClipCode (e : ℕ) :
    decodeRatPair (qpClipCode e) = qpClip (decodeRatPair e) := by
  unfold qpClipCode qpClip decodeRatPair
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [decodeRat_ratMaxCode, decodeRat_ratMinCode, decodeRat_zeroCode, decodeRat_oneCode]

/-- `[qpClipCode e]` if the clipped pair is non-degenerate, else `[]` (the empty list code `0`). -/
def canonFilterStep (e : ℕ) : ℕ :=
  selectFn (qpNonemptyBop (qpClipCode e)) (Nat.pair (qpClipCode e) 0 + 1) 0

theorem primrec_canonFilterStep : Nat.Primrec canonFilterStep := by
  have hc : Nat.Primrec qpClipCode := primrec_qpClipCode
  exact (primrec_selectFn (primrec_qpNonemptyBop.comp hc)
    (Nat.Primrec.succ.comp (hc.pair (Nat.Primrec.const 0))) (Nat.Primrec.const 0)).of_eq
    fun _ => rfl

theorem decodeList_canonFilterStep (e : ℕ) :
    decodeList (canonFilterStep e)
      = if (qpClip (decodeRatPair e)).1 < (qpClip (decodeRatPair e)).2
        then [qpClipCode e] else [] := by
  unfold canonFilterStep
  by_cases h : qpNonemptyBop (qpClipCode e) = 1
  · rw [h, selectFn_one]
    have h' : (decodeRatPair (qpClipCode e)).1 < (decodeRatPair (qpClipCode e)).2 :=
      (qpNonemptyBop_eq_one_iff (qpClipCode e)).mp h
    rw [decodeRatPair_qpClipCode] at h'
    simp [h', decodeList_succ, decodeList_zero]
  · have h0 : qpNonemptyBop (qpClipCode e) = 0 := by
      have := ratLtCode_le_one (Nat.pair (qpClipCode e).unpair.1 (qpClipCode e).unpair.2)
      unfold qpNonemptyBop at h ⊢; omega
    rw [h0, selectFn_zero]
    have hnot : ¬ (decodeRatPair (qpClipCode e)).1 < (decodeRatPair (qpClipCode e)).2 := by
      rw [← qpNonemptyBop_eq_one_iff]; omega
    rw [decodeRatPair_qpClipCode] at hnot
    simp [hnot, decodeList_zero]

/-- The code-level clip-and-filter pass, mirroring the list-level
`(L.map qpClip).filter (fun p => decide (p.1 < p.2))`. -/
def canonListCode (c : ℕ) : ℕ := flatMapCode (fun t => canonFilterStep t.unpair.2) 0 c

theorem primrec_canonListCode : Nat.Primrec canonListCode := by
  have hg : Nat.Primrec (fun t : ℕ => canonFilterStep t.unpair.2) :=
    primrec_canonFilterStep.comp Nat.Primrec.right
  exact ((primrec_flatMapCode hg).comp ((Nat.Primrec.const 0).pair primrec_id)).of_eq
    fun c => by
      unfold canonListCode
      simp only [id, unpair_pair_fst, unpair_pair_snd]

theorem decodeQPairList_canonFilterStep (e : ℕ) :
    decodeQPairList (canonFilterStep e)
      = if (qpClip (decodeRatPair e)).1 < (qpClip (decodeRatPair e)).2
        then [qpClip (decodeRatPair e)] else [] := by
  unfold decodeQPairList
  rw [decodeList_canonFilterStep]
  split <;> simp [decodeRatPair_qpClipCode]

theorem mem_decodeQPairList_canonFilterStep (e : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (canonFilterStep e) ↔
      (qpClip (decodeRatPair e)).1 < (qpClip (decodeRatPair e)).2 ∧ p = qpClip (decodeRatPair e) := by
  rw [decodeQPairList_canonFilterStep]
  by_cases h : (qpClip (decodeRatPair e)).1 < (qpClip (decodeRatPair e)).2
  · simp [h, eq_comm]
  · simp [h]

/-- **`canonListCode` realizes the clip-and-filter pass at the set level.** -/
theorem mem_decodeQPairList_canonListCode (c : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (canonListCode c) ↔
      ∃ p0 ∈ decodeQPairList c, (qpClip p0).1 < (qpClip p0).2 ∧ p = qpClip p0 := by
  unfold canonListCode
  rw [mem_decodeQPairList_flatMapCode]
  constructor
  · rintro ⟨y, hy, hp⟩
    rw [unpair_pair_snd, mem_decodeQPairList_canonFilterStep] at hp
    exact ⟨decodeRatPair y, (mem_decodeQPairList c (decodeRatPair y)).mpr ⟨y, hy, rfl⟩, hp⟩
  · rintro ⟨p0, hp0, hcond, hp⟩
    obtain ⟨y, hy, rfl⟩ := (mem_decodeQPairList c p0).mp hp0
    exact ⟨y, hy, by rw [unpair_pair_snd, mem_decodeQPairList_canonFilterStep]; exact ⟨hcond, hp⟩⟩

/-- **`canonListCode` realizes the clip-and-filter pass at the `presentedIntervals` level.** -/
theorem presentedIntervals_decodeQPairList_canonListCode (c : ℕ) :
    presentedIntervals (decodeQPairList (canonListCode c))
      = presentedIntervals (decodeQPairList c) ∩ Set.Ico (0 : ℚ) 1 := by
  rw [← presentedIntervals_map_qpClip, ← presentedIntervals_filter_qpPos ((decodeQPairList c).map qpClip)]
  apply presentedIntervals_congr
  intro p
  rw [mem_decodeQPairList_canonListCode, List.mem_filter, List.mem_map]
  constructor
  · rintro ⟨p0, hp0, hcond, rfl⟩
    exact ⟨⟨p0, hp0, rfl⟩, decide_eq_true_eq.mpr hcond⟩
  · rintro ⟨⟨p0, hp0, hp⟩, hcond⟩
    rw [decide_eq_true_eq] at hcond
    exact ⟨p0, hp0, hp ▸ hcond, hp.symm⟩

/-- **A list all of whose pairs are already non-degenerate is empty iff it presents `∅`** (unlike
an arbitrary presenting list, where individually-degenerate pairs could make this fail). -/
theorem presentedIntervals_eq_empty_iff_of_forall_lt {L' : List (ℚ × ℚ)}
    (hpos : ∀ p ∈ L', p.1 < p.2) : presentedIntervals L' = ∅ ↔ L' = [] := by
  constructor
  · intro h
    rcases L' with _ | ⟨a, l⟩
    · rfl
    · exact absurd h (Set.Nonempty.ne_empty ⟨a.1, mem_presentedIntervals.mpr
        ⟨a, List.mem_cons.mpr (Or.inl rfl), le_refl _,
          hpos a (List.mem_cons.mpr (Or.inl rfl))⟩⟩)
  · rintro rfl; exact presentedIntervals_nil

/-- Every element of `decodeQPairList (canonListCode c)` is already non-degenerate (this is
`canonFilterStep`'s whole point), so — unlike an arbitrary list — this particular list is empty
iff its `presentedIntervals` is empty. -/
theorem decodeQPairList_canonListCode_eq_nil_iff (c : ℕ) :
    decodeQPairList (canonListCode c) = [] ↔
      presentedIntervals (decodeQPairList (canonListCode c)) = ∅ :=
  (presentedIntervals_eq_empty_iff_of_forall_lt (fun p hp => by
    obtain ⟨p0, hp0, hcond, rfl⟩ := (mem_decodeQPairList_canonListCode c p).mp hp
    exact hcond)).symm

/-- A fixed code for the rational pair `(0,1)`, presenting `U.master`. -/
def masterPairCode : ℕ := Nat.pair zeroCode oneCode

@[simp] theorem decodeRatPair_masterPairCode : decodeRatPair masterPairCode = ((0 : ℚ), (1 : ℚ)) := by
  unfold masterPairCode decodeRatPair
  simp only [unpair_pair_fst, unpair_pair_snd, decodeRat_zeroCode, decodeRat_oneCode]

/-- The singleton list-code `[masterPairCode]` decodes to the singleton presenting list of
`U.master`. -/
theorem decodeQPairList_masterCode :
    decodeQPairList (Nat.pair masterPairCode 0 + 1) = [((0 : ℚ), (1 : ℚ))] := by
  unfold decodeQPairList
  rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero]
  simp [decodeRatPair_masterPairCode]

/-- Every pair in `decodeQPairList (canonListCode c)` is already non-degenerate (this is
`canonFilterStep`'s whole point). -/
theorem forall_lt_decodeQPairList_canonListCode (c : ℕ) :
    ∀ p ∈ decodeQPairList (canonListCode c), p.1 < p.2 := fun p hp => by
  obtain ⟨p0, -, hcond, rfl⟩ := (mem_decodeQPairList_canonListCode c p).mp hp
  exact hcond

/-- **The code-level canonicalization**, mirroring `canonList` exactly: `canonListCode c` if
non-empty, else the fallback singleton `[masterPairCode]` (presenting `U.master`). -/
def canonCode (c : ℕ) : ℕ :=
  selectFn (isZero (canonListCode c)) (Nat.pair masterPairCode 0 + 1) (canonListCode c)

theorem primrec_canonCode : Nat.Primrec canonCode :=
  (primrec_selectFn (primrec_isZero.comp primrec_canonListCode)
    (Nat.Primrec.const (Nat.pair masterPairCode 0 + 1)) primrec_canonListCode).of_eq
    fun _ => rfl

/-- **`canonCode` realizes `canonList` at the `presentedIntervals` level.** -/
theorem presentedIntervals_decodeQPairList_canonCode (c : ℕ) :
    presentedIntervals (decodeQPairList (canonCode c))
      = presentedIntervals (canonList (decodeQPairList c)) := by
  have hfilterPos : ∀ p ∈ ((decodeQPairList c).map qpClip).filter (fun p => decide (p.1 < p.2)),
      p.1 < p.2 := fun p hp => by simpa using (List.mem_filter.mp hp).2
  by_cases hne : (presentedIntervals (decodeQPairList c) ∩ Set.Ico (0 : ℚ) 1).Nonempty
  · have hnc : (presentedIntervals (decodeQPairList (canonListCode c))).Nonempty := by
      rwa [presentedIntervals_decodeQPairList_canonListCode]
    have hcne : canonListCode c ≠ 0 := by
      intro h
      apply hnc.ne_empty
      unfold decodeQPairList
      rw [h, decodeList_zero, List.map_nil]
      exact presentedIntervals_nil
    have hzero : isZero (canonListCode c) = 0 := by
      by_contra hz
      have h1 := isZero_le_one (canonListCode c)
      exact hcne ((isZero_eq_one_iff _).mp (by omega))
    have hcc : canonCode c = canonListCode c := by unfold canonCode; rw [hzero, selectFn_zero]
    have hL'ne : ((decodeQPairList c).map qpClip).filter (fun p => decide (p.1 < p.2)) ≠ [] := by
      rw [Ne, ← presentedIntervals_eq_empty_iff_of_forall_lt hfilterPos,
        presentedIntervals_filter_qpPos, presentedIntervals_map_qpClip]
      exact hne.ne_empty
    rcases hL : ((decodeQPairList c).map qpClip).filter (fun p => decide (p.1 < p.2)) with _ | ⟨a, l⟩
    · exact absurd hL hL'ne
    · rw [hcc, presentedIntervals_decodeQPairList_canonListCode, canonList_eq_of_filter_eq_cons hL,
        ← hL, presentedIntervals_filter_qpPos, presentedIntervals_map_qpClip]
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hLnil : decodeQPairList (canonListCode c) = [] := by
      rw [decodeQPairList_canonListCode_eq_nil_iff, presentedIntervals_decodeQPairList_canonListCode,
        hne]
    have hczero : canonListCode c = 0 := by
      have h' := hLnil
      unfold decodeQPairList at h'
      rwa [List.map_eq_nil_iff, decodeList_eq_nil_iff] at h'
    have hzero : isZero (canonListCode c) = 1 := by rw [hczero]; exact (isZero_eq_one_iff 0).mpr rfl
    have hcc : canonCode c = Nat.pair masterPairCode 0 + 1 := by
      unfold canonCode; rw [hzero, selectFn_one]
    have hLnil' : ((decodeQPairList c).map qpClip).filter (fun p => decide (p.1 < p.2)) = [] := by
      rw [← presentedIntervals_eq_empty_iff_of_forall_lt hfilterPos, presentedIntervals_filter_qpPos,
        presentedIntervals_map_qpClip]
      exact hne
    rw [hcc, decodeQPairList_masterCode, canonList_eq_of_filter_eq_nil hLnil']

/-- **Every pair in `decodeQPairList (canonCode c)` is non-degenerate** — both branches of
`canonCode` (the filtered list, or the `[masterPairCode]` fallback) only ever produce
`p.1 < p.2` pairs. This is what lets `splitU` (Theorem 8.8(b) Part 4) safely pick the *first*
pair of `decodeQPairList (canonCode n)` as its midpoint-split witness, with no search needed. -/
theorem forall_lt_decodeQPairList_canonCode (c : ℕ) :
    ∀ p ∈ decodeQPairList (canonCode c), p.1 < p.2 := by
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
    exact forall_lt_decodeQPairList_canonListCode c

/-- `decodeQPairList (canonCode c)` is never empty (it always contains at least the fallback
pair `(0,1)`, or a genuine clipped pair). -/
theorem decodeQPairList_canonCode_ne_nil (c : ℕ) : decodeQPairList (canonCode c) ≠ [] := by
  unfold canonCode
  by_cases hz : canonListCode c = 0
  · have hzero : isZero (canonListCode c) = 1 := by rw [hz]; exact (isZero_eq_one_iff 0).mpr rfl
    rw [hzero, selectFn_one, decodeQPairList_masterCode]
    simp
  · have hzero : isZero (canonListCode c) = 0 := by
      by_contra hcontra
      have h1 := isZero_le_one (canonListCode c)
      exact hz ((isZero_eq_one_iff _).mp (by omega))
    rw [hzero, selectFn_zero]
    intro hcontra
    apply hz
    have h' := hcontra
    unfold decodeQPairList at h'
    rwa [List.map_eq_nil_iff, decodeList_eq_nil_iff] at h'

/-- `canonCode c` is never the `0` (empty-list) code. -/
theorem canonCode_ne_zero (c : ℕ) : canonCode c ≠ 0 := by
  intro h
  exact decodeQPairList_canonCode_ne_nil c (by rw [h]; unfold decodeQPairList; rw [decodeList_zero]; rfl)

/-! ### Assembling `U.ComputablePresentation` -/

/-- **`𝒰`'s enumeration**: canonicalize the `List (ℚ × ℚ)` coded by `n`. -/
def UX (n : ℕ) : Set ℚ := presentedIntervals (decodeQPairList (canonCode n))

theorem UX_eq (n : ℕ) : UX n = presentedIntervals (canonList (decodeQPairList n)) :=
  presentedIntervals_decodeQPairList_canonCode n

/-- Every `UX n` is a genuine `U`-neighbourhood. -/
theorem U_mem_UX (n : ℕ) : U.mem (UX n) := by
  rw [UX_eq]; exact U_mem_presentedIntervals_canonList _

/-- `UX` is onto `U`'s neighbourhoods: every `U`-neighbourhood already has a Scott-literal
presenting list (`U_mem_iff_scott`), on which `canonList` is a no-op (`canonList_fixed`). -/
theorem U_surj_UX : ∀ {Y : Set ℚ}, U.mem Y → ∃ n, UX n = Y := by
  intro Y hY
  obtain ⟨L, -, hYeq, -⟩ := U_mem_iff_scott.mp hY
  have hUL : U.mem (presentedIntervals L) := by rw [← hYeq]; exact hY
  exact ⟨encodeQPairList L, by
    rw [UX_eq, decodeQPairList_encodeQPairList, canonList_fixed hUL, ← hYeq]⟩

/-- **Scott's consistency condition reduces to non-emptiness**: since `U`'s raw intersection
`combineCode` output is *automatically* a genuine `U`-neighbourhood whenever it is non-empty
(it is always presentable and always `⊆ [0,1)`), "`∃k. Xₖ ⊆ Xₙ∩Xₘ`" holds iff `Xₙ∩Xₘ` is
non-empty (every `Xₖ` being itself non-empty rules out the `⊆ ∅` direction). -/
theorem U_cons_iff_nonempty_inter (n m : ℕ) :
    (∃ k, UX k ⊆ UX n ∩ UX m) ↔ (UX n ∩ UX m).Nonempty := by
  constructor
  · rintro ⟨k, hk⟩
    exact (U_mem_UX k).2.1.mono hk
  · intro hne
    have hUmem : U.mem (UX n ∩ UX m) := by
      obtain ⟨-, -, hsubn⟩ := U_mem_UX n
      exact ⟨⟨decodeQPairList (combineCode (canonCode n) (canonCode m)),
        (presentedIntervals_decodeQPairList_combineCode (canonCode n) (canonCode m)).symm⟩,
        hne, Set.inter_subset_left.trans hsubn⟩
    obtain ⟨k, hk⟩ := U_surj_UX hUmem
    exact ⟨k, by rw [hk]⟩

/-- **7.1(i) for `𝒰`**: `Xₙ ∩ Xₘ = X_k` is recursively decidable. Reduces to
`recDecidable₂_presentedIntervals_eq` on the codes `combineCode (canonCode n) (canonCode m)`
(realizing `Xₙ ∩ Xₘ`) and `canonCode k` (realizing `X_k`). -/
theorem U_interEq_computable : RecDecidable₃ (fun n m k => UX n ∩ UX m = UX k) := by
  unfold RecDecidable₃
  have h1 : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have h2 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have h3 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hcomb : Nat.Primrec (fun t : ℕ =>
      combineCode (canonCode t.unpair.1) (canonCode t.unpair.2.unpair.1)) :=
    (primrec_combineCode.comp ((primrec_canonCode.comp h1).pair (primrec_canonCode.comp h2))).of_eq
      fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hg : Nat.Primrec (fun t : ℕ =>
      Nat.pair (combineCode (canonCode t.unpair.1) (canonCode t.unpair.2.unpair.1))
        (canonCode t.unpair.2.unpair.2)) := hcomb.pair (primrec_canonCode.comp h3)
  refine RecDecidable.of_iff (fun t => ?_) (recDecidable₂_presentedIntervals_eq.comp hg)
  show UX t.unpair.1 ∩ UX t.unpair.2.unpair.1 = UX t.unpair.2.unpair.2 ↔ _
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [UX, UX, UX, presentedIntervals_decodeQPairList_combineCode]

/-- **7.1(ii) for `𝒰`**: consistency `∃k. X_k ⊆ Xₙ ∩ Xₘ` is recursively decidable, via
`U_cons_iff_nonempty_inter` and `recDecidable_presentedIntervals_nonempty`. -/
theorem U_cons_computable : RecDecidable₂ (fun n m => ∃ k, UX k ⊆ UX n ∩ UX m) := by
  unfold RecDecidable₂
  have hcomb : Nat.Primrec (fun t : ℕ => combineCode (canonCode t.unpair.1) (canonCode t.unpair.2)) :=
    (primrec_combineCode.comp ((primrec_canonCode.comp Nat.Primrec.left).pair
      (primrec_canonCode.comp Nat.Primrec.right))).of_eq
      fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  refine RecDecidable.of_iff (fun t => ?_) (recDecidable_presentedIntervals_nonempty.comp hcomb)
  show (∃ k, UX k ⊆ UX t.unpair.1 ∩ UX t.unpair.2) ↔ _
  rw [U_cons_iff_nonempty_inter, UX, UX, presentedIntervals_decodeQPairList_combineCode]

/-- The intersection index: `combineCode` on canonicalized codes (`UX` re-canonicalizes on
lookup, so no further canonicalization is needed here). -/
def Uinter (n m : ℕ) : ℕ := combineCode (canonCode n) (canonCode m)

theorem Uinter_primrec : Nat.Primrec (fun t : ℕ => Uinter t.unpair.1 t.unpair.2) := by
  unfold Uinter
  exact (primrec_combineCode.comp ((primrec_canonCode.comp Nat.Primrec.left).pair
    (primrec_canonCode.comp Nat.Primrec.right))).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]

theorem Uinter_spec {n m : ℕ} (h : ∃ k, UX k ⊆ UX n ∩ UX m) : UX (Uinter n m) = UX n ∩ UX m := by
  have hne : (UX n ∩ UX m).Nonempty := (U_cons_iff_nonempty_inter n m).mp h
  have hUL : U.mem (presentedIntervals (decodeQPairList (combineCode (canonCode n) (canonCode m)))) := by
    rw [presentedIntervals_decodeQPairList_combineCode]
    obtain ⟨-, -, hsubn⟩ := U_mem_UX n
    exact ⟨⟨decodeQPairList (combineCode (canonCode n) (canonCode m)),
      (presentedIntervals_decodeQPairList_combineCode (canonCode n) (canonCode m)).symm⟩,
      hne, Set.inter_subset_left.trans hsubn⟩
  unfold Uinter UX
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL,
    presentedIntervals_decodeQPairList_combineCode]

theorem presentedIntervals_singleton_zero_one :
    presentedIntervals ([((0 : ℚ), (1 : ℚ))]) = U.master := by
  rw [presentedIntervals_cons, presentedIntervals_nil, Set.union_empty]; rfl

/-- A fixed index of `U.master = Ico 0 1`. -/
def UmasterIdx : ℕ := encodeQPairList [((0 : ℚ), (1 : ℚ))]

theorem UX_UmasterIdx : UX UmasterIdx = U.master := by
  unfold UmasterIdx
  rw [UX_eq, decodeQPairList_encodeQPairList]
  have hmem : U.mem (presentedIntervals [((0 : ℚ), (1 : ℚ))]) := by
    rw [presentedIntervals_singleton_zero_one]; exact U.master_mem
  rw [canonList_fixed hmem, presentedIntervals_singleton_zero_one]

/-- **Theorem 8.8(b), Part 3.** `𝒰` (Definition 8.7) has a genuine `ComputablePresentation`. -/
def UComputablePresentation : ComputablePresentation U where
  X := UX
  mem_X := U_mem_UX
  surj := U_surj_UX
  interEq_computable := U_interEq_computable
  cons_computable := U_cons_computable
  inter := Uinter
  inter_primrec := Uinter_primrec
  inter_spec := Uinter_spec
  masterIdx := UmasterIdx
  masterIdx_spec := UX_UmasterIdx

/-- **`𝒰` is effectively given.** -/
theorem U_isEffectivelyGiven : U.IsEffectivelyGiven := ⟨UComputablePresentation⟩

end Scott1980.Neighborhood

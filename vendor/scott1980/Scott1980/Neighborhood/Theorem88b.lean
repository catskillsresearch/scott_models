/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.DAtomDecidable
import Scott1980.Neighborhood.SplitU
import Scott1980.Neighborhood.UComputablePresentation

/-!
# Theorem 8.8(b), Part 6 — the effective back-and-forth construction

`Theorem88.lean`/`Theorem88a.lean` build Scott's back-and-forth construction generically over an
abstract splitting operation `split` satisfying `SplitSpec`; Part 5 (`DAtomDecidable.lean`) shows
`D`-atom emptiness is recursively decidable for any `ComputablePresentation P` of `D`. This file
assembles the **effective** instantiation: a computable splitting operation `splitEff`, built from
`DAtom_recDecidable` (deciding which side of a `D`-side split is non-empty) and `SplitU.lean`'s
`splitULeft`/`splitURight` (deterministically splitting the matching `U`-side neighbourhood).

## Part 6b: re-pointing `P`'s enumeration at index `0`

`Theorem88a.lean`'s apparatus (`Yidx`, `DprimeU`, `domainIso`) is stated for an arbitrary
enumeration `e : ℕ → Set α` with `e 0 = D.master` (Scott's convention `X₀ = Δ`, needed for
`Yseq_zero_eq_master`). An arbitrary `ComputablePresentation P` need not have `P.masterIdx = 0`, so
we re-point it: `eIdx` swaps `0` and `P.masterIdx` (a primitive-recursive involution), and
`P.reindexInvolutive eIdx …` (Definition71.lean) transports the *entire* computable presentation
along this swap in one step — giving a new presentation `P₀` with `P₀.X 0 = D.master` for free,
with no need to redo any of Part 5's `DAtom` apparatus (it applies to `P₀` exactly as it did to
`P`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **Swap `0` and `P.masterIdx`.** A primitive-recursive involution on `ℕ` re-pointing whichever
index `P.masterIdx` names `D`'s master neighbourhood to sit at index `0` instead, leaving every
other index fixed. -/
def eIdx (n : ℕ) : ℕ :=
  if n = 0 then P.masterIdx else if n = P.masterIdx then 0 else n

theorem eIdx_zero : eIdx P 0 = P.masterIdx := if_pos rfl

theorem eIdx_involutive : Function.Involutive (eIdx P) := by
  intro n
  unfold eIdx
  split_ifs with h0 hm hm' hm'' hm''' <;> simp_all

theorem eIdx_primrec : Nat.Primrec (eIdx P) := by
  have hc0 : Nat.Primrec (fun n => isZero n) := primrec_isZero
  have hcm : Nat.Primrec (fun n : ℕ => isZero ((n - P.masterIdx) + (P.masterIdx - n))) :=
    primrec_isZero.comp
      (primrec_add₂ (primrec_sub₂ primrec_id (Nat.Primrec.const P.masterIdx))
        (primrec_sub₂ (Nat.Primrec.const P.masterIdx) primrec_id))
  have hinner : Nat.Primrec (fun n : ℕ =>
      selectFn (isZero ((n - P.masterIdx) + (P.masterIdx - n))) 0 n) :=
    primrec_ite hcm (Nat.Primrec.const 0) primrec_id
  refine (primrec_ite hc0 (Nat.Primrec.const P.masterIdx) hinner).of_eq (fun n => ?_)
  rcases (show isZero n = 0 ∨ isZero n = 1 from by have := isZero_le_one n; omega) with h0 | h0
  · rw [h0, selectFn_zero]
    have hn0 : n ≠ 0 := by intro h; subst h; unfold isZero at h0; omega
    rcases (show isZero ((n - P.masterIdx) + (P.masterIdx - n)) = 0 ∨
        isZero ((n - P.masterIdx) + (P.masterIdx - n)) = 1 from
        by have := isZero_le_one ((n - P.masterIdx) + (P.masterIdx - n)); omega) with h1 | h1
    · rw [h1, selectFn_zero]
      have hnm : n ≠ P.masterIdx := by intro h; subst h; unfold isZero at h1; omega
      unfold eIdx
      rw [if_neg hn0, if_neg hnm]
    · rw [h1, selectFn_one]
      have hnm : n = P.masterIdx := by unfold isZero at h1; omega
      unfold eIdx
      rw [if_neg hn0, if_pos hnm]
  · rw [h0, selectFn_one]
    have hn0 : n = 0 := by unfold isZero at h0; omega
    unfold eIdx
    rw [if_pos hn0]

/-- **The re-pointed presentation `P₀`**: `P`'s enumeration reindexed by `eIdx`, so that
`P₀.X 0 = D.master`. Built via `ComputablePresentation.reindexInvolutive`, so every one of Scott's
structural fields — in particular the two deciders `interEq_computable`/`cons_computable` needed
for `DAtom_recDecidable` — transfers automatically, with no need to redo Part 5's work. -/
noncomputable def P0 : ComputablePresentation D :=
  P.reindexInvolutive (eIdx P) (eIdx_involutive P) (eIdx_primrec P)

@[simp] theorem P0_X (n : ℕ) : (P0 P).X n = P.X (eIdx P n) := rfl

/-- **`e := P₀.X`, Scott's re-enumeration with `e 0 = D.master`.** -/
noncomputable abbrev e : ℕ → Set α := (P0 P).X

theorem he0 : e P 0 = D.master := by
  show P.X (eIdx P 0) = D.master
  rw [eIdx_zero]; exact P.masterIdx_spec

theorem hcover : ∀ S, D.mem S ↔ ∃ n, S = e P n := by
  intro S
  constructor
  · intro hS
    obtain ⟨n, hn⟩ := P.surj hS
    exact ⟨eIdx P n, by show S = P.X (eIdx P (eIdx P n)); rw [eIdx_involutive P n]; exact hn.symm⟩
  · rintro ⟨n, rfl⟩
    exact (P0 P).mem_X n

/-! ## Part 6c: `genAtom (idxSet e)` emptiness is decidable

`Theorem88.lean`'s `genAtom` tracks the depth-`n` atom for a sign sequence `δ` as a *set*, built by
an `if δ i then Z i else M \ Z i` intersection at each step. `DAtomDecidable.lean`'s `DAtom`, by
contrast, tracks the *same kind* of atom (for `Z := idxSet Q.X`, `M := Set.univ`) as two explicit
`List ℕ` accumulators (`pos`/`neg`) — the very data a primitive-recursive realization needs to
carry. `posnegList` extracts these accumulators from `δ` by mirroring `genAtom`'s own recursion
step-for-step, so `genAtom_eq_DAtom` (below) is a one-line induction, not a `List.range`/`filter`
reindexing exercise. -/

/-- **The `(pos, neg)` accumulator pair for a sign sequence `δ`, at depth `n`.** Mirrors
`genAtom`'s own recursion: at step `n`, `n` itself joins `pos` (if `δ n = true`) or `neg`
(otherwise). -/
def posnegList (δ : ℕ → Bool) : ℕ → List ℕ × List ℕ
  | 0 => ([], [])
  | n + 1 =>
      let pn := posnegList δ n
      if δ n then (pn.1 ++ [n], pn.2) else (pn.1, pn.2 ++ [n])

@[simp] theorem posnegList_zero (δ : ℕ → Bool) : posnegList δ 0 = ([], []) := rfl

theorem posnegList_succ_true {δ : ℕ → Bool} {n : ℕ} (h : δ n = true) :
    posnegList δ (n + 1) = ((posnegList δ n).1 ++ [n], (posnegList δ n).2) := by
  show (if δ n then _ else _) = _
  simp [h]

theorem posnegList_succ_false {δ : ℕ → Bool} {n : ℕ} (h : δ n = false) :
    posnegList δ (n + 1) = ((posnegList δ n).1, (posnegList δ n).2 ++ [n]) := by
  show (if δ n then _ else _) = _
  simp [h]

/-- `IPos` splits across list append (order/multiplicity are irrelevant to membership). -/
theorem IPos_append {E : NeighborhoodSystem α} (Q : ComputablePresentation E) (l1 l2 : List ℕ) :
    IPos Q (l1 ++ l2) = IPos Q l1 ∩ IPos Q l2 := by
  induction l1 with
  | nil => simp [IPos_nil]
  | cons a l ih => rw [List.cons_append, IPos_cons, IPos_cons, ih, Set.inter_assoc]

/-- The negative part of `DAtom` splits across list append. -/
theorem negPart_append {E : NeighborhoodSystem α} (Q : ComputablePresentation E)
    (n1 n2 : List ℕ) :
    {m : ℕ | ∀ j ∈ (n1 ++ n2), m ∉ idxSet Q.X j} =
      {m | ∀ j ∈ n1, m ∉ idxSet Q.X j} ∩ {m | ∀ j ∈ n2, m ∉ idxSet Q.X j} := by
  ext m
  simp only [Set.mem_setOf_eq, List.forall_mem_append, Set.mem_inter_iff]

/-- **`genAtom` reindexed via `idxSet e` matches `DAtom (P0 P)` at the `posnegList`
accumulator.** The heart of Part 6c: since `(P0 P).X = e P`, this is exactly the fact that a
`D`-side atom (Boolean-sequence style) and its `(pos, neg)`-list-style description agree. -/
theorem genAtom_eq_DAtom (δ : ℕ → Bool) :
    ∀ n, genAtom (idxSet (e P)) Set.univ δ n =
      DAtom (P0 P) (posnegList δ n).1 (posnegList δ n).2 := by
  intro n
  induction n with
  | zero => simp [genAtom, DAtom, IPos_nil]
  | succ n ih =>
    rcases Bool.eq_false_or_eq_true (δ n) with h | h
    · have hstep : genAtom (idxSet (e P)) Set.univ δ (n + 1) =
          genAtom (idxSet (e P)) Set.univ δ n ∩ idxSet (e P) n := by
        show genAtom (idxSet (e P)) Set.univ δ n ∩
          (if δ n then idxSet (e P) n else Set.univ \ idxSet (e P) n) = _
        simp [h]
      rw [hstep, posnegList_succ_true h, ih]
      unfold DAtom
      rw [IPos_append]
      have hI : IPos (P0 P) [n] = idxSet (e P) n := by
        rw [IPos_cons, IPos_nil, Set.inter_univ]
      rw [hI]
      show IPos (P0 P) (posnegList δ n).1 ∩ {m | ∀ j ∈ (posnegList δ n).2, m ∉ idxSet (e P) j}
          ∩ idxSet (e P) n = _
      ac_rfl
    · have hstep : genAtom (idxSet (e P)) Set.univ δ (n + 1) =
          genAtom (idxSet (e P)) Set.univ δ n ∩ (Set.univ \ idxSet (e P) n) := by
        show genAtom (idxSet (e P)) Set.univ δ n ∩
          (if δ n then idxSet (e P) n else Set.univ \ idxSet (e P) n) = _
        simp [h]
      rw [hstep, posnegList_succ_false h, ih]
      unfold DAtom
      rw [negPart_append]
      have hZ : {m : ℕ | m ∉ idxSet (e P) n} = Set.univ \ idxSet (e P) n := by
        ext m; simp [Set.mem_diff]
      have hn : {m : ℕ | ∀ j ∈ [n], m ∉ idxSet (e P) j} = {m : ℕ | m ∉ idxSet (e P) n} := by
        ext m; simp
      rw [hn, hZ]
      show IPos (P0 P) (posnegList δ n).1 ∩ {m | ∀ j ∈ (posnegList δ n).2, m ∉ idxSet (e P) j}
          ∩ (Set.univ \ idxSet (e P) n) = _
      ac_rfl

/-- **Part 6c's headline result.** `genAtom`-emptiness (for the reindexed enumeration `e P`, at any
sign sequence `δ` and depth `n`) reduces to `DAtom (P0 P)`-emptiness at the `posnegList`
accumulator — which Part 5's `DAtom_recDecidable (P0 P)` already decides, in the codes of *any*
list representing `(posnegList δ n).1`/`.2`. What remains for Part 6e is exactly to realize
`posnegList δ n`'s two components as *codes*, primitively in `n` and a code for `δ`'s first `n`
bits — composing that with `DAtom_recDecidable (P0 P)`'s extracted decider then decides
`genAtom`-emptiness outright, with no need to redo any of Part 5's meet-fold machinery. -/
theorem genAtom_empty_iff (δ : ℕ → Bool) (n : ℕ) :
    genAtom (idxSet (e P)) Set.univ δ n = ∅ ↔
      DAtom (P0 P) (posnegList δ n).1 (posnegList δ n).2 = ∅ := by
  rw [genAtom_eq_DAtom]

end Scott1980.Neighborhood

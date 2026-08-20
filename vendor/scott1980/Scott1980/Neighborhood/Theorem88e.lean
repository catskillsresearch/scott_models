/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Theorem88d
import Scott1980.Neighborhood.Theorem88c

/-!
# Theorem 8.8(b)(vii)(3) — a genuinely code-driven subsystem `D''`

`Theorem88d.lean` (Part 7) builds a fully `Nat.Primrec` back-and-forth recursion — `atomUCode`/
`YseqCode` — tracking `U`-codes natively, and proves the two halves of Scott's matching invariant
at the code level: validity (`atomUCode_mem`, free) and the emptiness-match
(`genAtom_Yc_empty_iff`, where `Yc P n := UX (YseqCode P n)`). This file finishes the job Scott's
own Theorem 8.8(a)/(b) Part 6 (`Theorem88a.lean`/`Theorem88c.lean`) already did for the *classical*
`Yidx (e P)` — but for `Yc P` instead, which is **genuinely code-driven**: unlike `Yidx`, whose
*value* is whatever `Classical.choice` happened to pick, `Yc P n = UX (YseqCode P n)` is *literally*
`UX` applied to a `Nat.Primrec` function of `n` and `P`'s own deciders.

## Plan

* Port the finite-constraint transfer lemmas (`Theorem88.lean`'s `transfer_dir`/`transfer_empty_iff`
 /`transfer_subset_iff`/`transfer_inter_eq_iff`) to the pair `(idxSet (e P), Set.univ)` vs.
 `(Yc P, U.master)`, using `genAtom_Yc_empty_iff` (plus `encodeBits`, realizing any finite prefix of
 an arbitrary `δ : ℕ → Bool` as some `deltaOf k`) as the emptiness-matching core, in place of
 `atomU_invariant`/`atomU_eq_genAtom`.
* Assemble `D'' := DprimeUCode`, `D ≅ᴰ D''`, `D'' ◁ U` — mirroring `Theorem88a.lean`'s
 `DprimeU`/`domainIso`/`DprimeU_subsystem` verbatim, with `Yidx (e P) ↦ Yc P` and the transfer
 lemmas above in place of `Theorem88.lean`'s generic ones.
* Build `ComputablePresentation D''` with `X n := Yc P n`, master index `0` — mirroring
 `Theorem88c.lean`'s `DprimeUPresentation`, reusing `idxSet_inter_eq_iff_DAtom`/
 `DAtom_pair_recDecidable`/`(P0 P).incl_computable`/`(P0 P).cons_computable`/`(P0 P).inter`
 unchanged (the *index relations* were already decidable; only the *carrier family* changes).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-! ## `Yc P`'s basic facts: subset-of-master and the zero-depth base case -/

theorem Yc_subset_master (n : ℕ) : Yc P n ⊆ U.master := (U_mem_UX (YseqCode P n)).2.2

/-- **`Yc P 0 = U.master`** (Scott's convention `Y₀ = U.master`, matching `Yseq_zero_eq_master`):
the unique bit-source realizing depth `1` with bit `0` set is `k = 1`, whose atom is non-junk
(`idxSet (e P) 0 = Set.univ`, so the "positive" constraint at index `0` is vacuous) and whose code
is literally `UmasterIdx`, since the *negative* sibling constraint (`DAtom (P0 P) [] [0]`) is
already empty — freezing `atomUCode` unchanged through the step (mirrors `atomUCode_subset`'s own
"carry unchanged" branch, here made into an equality). -/
theorem Yc_zero_eq_master : Yc P 0 = U.master := by
  have hidx0 : idxSet (e P) 0 = Set.univ := idxSet_zero D (e P) (hcover P) (he0 P)
  have h01 : atomUEmpty P 1 1 = 0 := by
    apply (atomUEmpty_eq_zero_iff_genAtom P 1 1).mpr
    show genAtom (idxSet (e P)) Set.univ (deltaOf 1) 0 ∩
      (if deltaOf 1 0 then idxSet (e P) 0 else Set.univ \ idxSet (e P) 0) ≠ ∅
    have hδ : deltaOf 1 0 = true := by decide
    rw [hδ, if_pos rfl]
    show (Set.univ : Set ℕ) ∩ idxSet (e P) 0 ≠ ∅
    rw [Set.univ_inter, hidx0]
    exact Set.univ_nonempty.ne_empty
  have hmem : Yc P 0 = UX (atomUCode P 1 1) := by
    unfold Yc
    ext z
    rw [mem_UX_YseqCode_iff]
    constructor
    · rintro ⟨i, hilt, hie, hz⟩
      have hi0 : i = 0 := by have := hilt; omega
      rwa [hi0] at hz
    · intro hz
      exact ⟨0, by norm_num, h01, hz⟩
  rw [hmem]
  have hnn : DAtom (P0 P) [] [] = Set.univ := by unfold DAtom; simp [IPos_nil]
  have hcode : atomUCode P 1 1 = UmasterIdx := by
    have hbit : (1 / 2 ^ (0 : ℕ)) % 2 = 1 := by norm_num
    rw [atomUCode_succ, atomUPos_zero, atomUNeg_zero, hbit, selectFn_one]
    have hposEmpty : datomDec P (Nat.pair (Nat.pair 0 0 + 1) 0) = 0 := by
      apply datomDec_eq_zero
      simp only [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero]
      show DAtom (P0 P) [0] [] ≠ ∅
      rw [DAtom_cons_pos, hnn, Set.inter_univ, hidx0]
      exact Set.univ_nonempty.ne_empty
    rw [hposEmpty, selectFn_zero]
    have hnegEmpty : datomDec P (Nat.pair 0 (Nat.pair 0 0 + 1)) = 1 := by
      apply (datomDec_spec P _ _).mpr
      simp only [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero]
      show DAtom (P0 P) [] [0] = ∅
      rw [DAtom_cons_neg, hnn, Set.inter_univ, hidx0, Set.diff_self]
    rw [hnegEmpty, selectFn_one, atomUCode_zero]
  rw [hcode, UX_UmasterIdx]

/-! ## Realizing any finite `δ`-prefix as `deltaOf k` for some `k`

`genAtom_Yc_empty_iff` only relates `genAtom` at sign sequences of the special form `deltaOf k`.
The general finite-constraint transfer lemma (`transfer_dir`, below) needs the emptiness match for
*every* `δ : ℕ → Bool`. Since `genAtom Z M δ n` only inspects `δ 0, …, δ (n - 1)` (`genAtom_congr`),
it suffices to realize any finite prefix of `δ` as `deltaOf k` for a suitable `k < 2 ^ n`. -/

/-- **`δ`'s length-`n` bit-encoding**: the natural number `< 2 ^ n` agreeing with `δ` on every bit
below `n`. -/
def encodeBits (δ : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | (n + 1) => encodeBits δ n + (if δ n then 2 ^ n else 0)

theorem encodeBits_lt (δ : ℕ → Bool) : ∀ n, encodeBits δ n < 2 ^ n
  | 0 => by simp [encodeBits]
  | (n + 1) => by
      have ih := encodeBits_lt δ n
      show encodeBits δ n + (if δ n then 2 ^ n else 0) < 2 ^ (n + 1)
      rw [pow_succ]
      rcases Bool.eq_false_or_eq_true (δ n) with h | h <;> simp [h] <;> omega

theorem deltaOf_encodeBits (δ : ℕ → Bool) : ∀ n i, i < n → deltaOf (encodeBits δ n) i = δ i := by
  intro n
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro i hi
    show deltaOf (encodeBits δ n + (if δ n then 2 ^ n else 0)) i = δ i
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
    · rcases Bool.eq_false_or_eq_true (δ n) with h | h
      · rw [h, if_pos rfl, deltaOf_add_two_pow_of_lt _ hi']
        exact ih i hi'
      · rw [h, if_neg (by simp), Nat.add_zero]
        exact ih i hi'
    · rw [hi']
      rcases Bool.eq_false_or_eq_true (δ n) with h | h
      · rw [h, if_pos rfl]
        exact deltaOf_two_pow_add_self (encodeBits_lt δ n)
      · rw [h, if_neg (by simp), Nat.add_zero, deltaOf_eq_testBit,
          Nat.testBit_lt_two_pow (encodeBits_lt δ n)]

/-- **The `genAtom`-emptiness core, for arbitrary `δ : ℕ → Bool`.** Realizes `δ`'s first `n` bits
as `deltaOf (encodeBits δ n)` (`genAtom_congr`), then invokes `genAtom_Yc_empty_iff`/
`atomUEmpty_eq_one_iff_genAtom` at that specific bit-source. -/
theorem hcoreIdxYc (δ : ℕ → Bool) (n : ℕ) :
    genAtom (idxSet (e P)) Set.univ δ n = ∅ ↔ genAtom (Yc P) U.master δ n = ∅ := by
  set k := encodeBits δ n with hkdef
  have hagree : ∀ i < n, δ i = deltaOf k i := fun i hi => (deltaOf_encodeBits δ n i hi).symm
  rw [genAtom_congr (idxSet (e P)) Set.univ hagree, genAtom_congr (Yc P) U.master hagree,
    ← atomUEmpty_eq_one_iff_genAtom, genAtom_Yc_empty_iff]

/-! ## Porting `Theorem88.lean`'s finite-constraint transfer lemma to `(idxSet (e P), Yc P)`

`transfer_dir` (private in `Theorem88.lean`) is stated fully generically over any two families
related by a `genAtom`-emptiness core — exactly `hcoreIdxYc` above — so it is reproduced verbatim
here (there is nothing to prove beyond what `Theorem88.lean` already established once and for all;
only the *instantiation* differs). -/

private theorem transfer_dir_idxYc {β1 β2 : Type*} (Z1 : ℕ → Set β1) (M1 : Set β1) (Z2 : ℕ → Set β2)
    (M2 : Set β2) (hcore : ∀ δ n, genAtom Z1 M1 δ n = ∅ ↔ genAtom Z2 M2 δ n = ∅)
    {cs : List (ℕ × Bool)} {n : ℕ} (hn : ∀ p ∈ cs, p.1 < n)
    (hne : {x ∈ M1 | ∀ p ∈ cs, (p.2 = true ↔ x ∈ Z1 p.1)}.Nonempty) :
    {y ∈ M2 | ∀ p ∈ cs, (p.2 = true ↔ y ∈ Z2 p.1)}.Nonempty := by
  classical
  obtain ⟨x, hxM, hxcs⟩ := hne
  set δ0 : ℕ → Bool := fun k => decide (x ∈ Z1 k) with hδ0def
  have hX1 : x ∈ genAtom Z1 M1 δ0 n := genAtom_self Z1 M1 hxM n
  have hne1 : (genAtom Z1 M1 δ0 n).Nonempty := ⟨x, hX1⟩
  have hne2 : (genAtom Z2 M2 δ0 n).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h2 => hne1.ne_empty ((hcore δ0 n).mpr h2)
  obtain ⟨y, hy⟩ := hne2
  refine ⟨y, genAtom_subset Z2 M2 δ0 n hy, fun p hp => ?_⟩
  have hforward := genAtom_forward hy p.1 (hn p hp)
  have hbeq : δ0 p.1 = p.2 := by
    show decide (x ∈ Z1 p.1) = p.2
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact (hxcs p hp).symm
  rwa [hbeq] at hforward

theorem transfer_empty_iff_idxYc {cs : List (ℕ × Bool)} {n : ℕ} (hn : ∀ p ∈ cs, p.1 < n) :
    {x ∈ (Set.univ : Set ℕ) | ∀ p ∈ cs, (p.2 = true ↔ x ∈ idxSet (e P) p.1)}.Nonempty ↔
      {y ∈ U.master | ∀ p ∈ cs, (p.2 = true ↔ y ∈ Yc P p.1)}.Nonempty :=
  ⟨transfer_dir_idxYc (idxSet (e P)) Set.univ (Yc P) U.master (hcoreIdxYc P) hn,
    transfer_dir_idxYc (Yc P) U.master (idxSet (e P)) Set.univ (fun δ n => (hcoreIdxYc P δ n).symm)
      hn⟩

theorem transfer_subset_iff_idxYc (i j : ℕ) :
    (Set.univ : Set ℕ) ∩ idxSet (e P) i ⊆ idxSet (e P) j ↔
      U.master ∩ Yc P i ⊆ Yc P j := by
  have key := transfer_empty_iff_idxYc P (cs := [(i, true), (j, false)]) (n := max i j + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) <;> simp)
  have hLHS : {x ∈ (Set.univ : Set ℕ) | ∀ p ∈ [(i, true), (j, false)],
      (p.2 = true ↔ x ∈ idxSet (e P) p.1)} = ((Set.univ : Set ℕ) ∩ idxSet (e P) i) \ idxSet (e P) j := by
    ext x
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_diff, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ U.master | ∀ p ∈ [(i, true), (j, false)], (p.2 = true ↔ y ∈ Yc P p.1)}
      = (U.master ∩ Yc P i) \ Yc P j := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_inter_iff]
    constructor
    · rintro ⟨hyM, hcs⟩
      have h1 : y ∈ Yc P i := (hcs (i, true) (by simp)).mp rfl
      have h2 : y ∉ Yc P j := fun hmem =>
        absurd ((hcs (j, false) (by simp)).mpr hmem) Bool.false_ne_true
      exact ⟨⟨hyM, h1⟩, h2⟩
    · rintro ⟨⟨hyM, h1⟩, h2⟩
      refine ⟨hyM, fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨fun _ => h1, fun _ => rfl⟩
      · exact ⟨fun hc => absurd hc Bool.false_ne_true, fun hmem => absurd hmem h2⟩
  rw [hLHS, hRHS] at key
  rw [← Set.diff_eq_empty, ← Set.diff_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

theorem transfer_inter_empty_iff_idxYc (i j : ℕ) :
    (Set.univ : Set ℕ) ∩ idxSet (e P) i ∩ idxSet (e P) j = ∅ ↔
      U.master ∩ Yc P i ∩ Yc P j = ∅ := by
  have key := transfer_empty_iff_idxYc P (cs := [(i, true), (j, true)]) (n := max i j + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) <;> simp)
  have hLHS : {x ∈ (Set.univ : Set ℕ) | ∀ p ∈ [(i, true), (j, true)],
      (p.2 = true ↔ x ∈ idxSet (e P) p.1)} = (Set.univ : Set ℕ) ∩ idxSet (e P) i ∩ idxSet (e P) j := by
    ext x
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ U.master | ∀ p ∈ [(i, true), (j, true)], (p.2 = true ↔ y ∈ Yc P p.1)}
      = U.master ∩ Yc P i ∩ Yc P j := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hyM, hcs⟩
      exact ⟨⟨hyM, (hcs (i, true) (by simp)).mp rfl⟩, (hcs (j, true) (by simp)).mp rfl⟩
    · rintro ⟨⟨hyM, h1⟩, h2⟩
      refine ⟨hyM, fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨fun _ => h1, fun _ => rfl⟩
      · exact ⟨fun _ => h2, fun _ => rfl⟩
  rw [hLHS, hRHS] at key
  rw [← Set.not_nonempty_iff_eq_empty, ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

theorem transfer_double_subset_iff_idxYc (i j k : ℕ) :
    (Set.univ : Set ℕ) ∩ idxSet (e P) i ∩ idxSet (e P) j ⊆ idxSet (e P) k ↔
      U.master ∩ Yc P i ∩ Yc P j ⊆ Yc P k := by
  have key := transfer_empty_iff_idxYc P (cs := [(i, true), (j, true), (k, false)])
    (n := max i (max j k) + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl) <;>
          simp [(Nat.le_max_left j k).trans (Nat.le_max_right i (max j k)),
            (Nat.le_max_right j k).trans (Nat.le_max_right i (max j k))])
  have hLHS : {x ∈ (Set.univ : Set ℕ) | ∀ p ∈ [(i, true), (j, true), (k, false)],
      (p.2 = true ↔ x ∈ idxSet (e P) p.1)}
      = ((Set.univ : Set ℕ) ∩ idxSet (e P) i ∩ idxSet (e P) j) \ idxSet (e P) k := by
    ext x
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_diff, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ U.master |
      ∀ p ∈ [(i, true), (j, true), (k, false)], (p.2 = true ↔ y ∈ Yc P p.1)}
      = (U.master ∩ Yc P i ∩ Yc P j) \ Yc P k := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_inter_iff]
    constructor
    · rintro ⟨hyM, hcs⟩
      have h1 : y ∈ Yc P i := (hcs (i, true) (by simp)).mp rfl
      have h2 : y ∈ Yc P j := (hcs (j, true) (by simp)).mp rfl
      have h3 : y ∉ Yc P k := fun hmem =>
        absurd ((hcs (k, false) (by simp)).mpr hmem) Bool.false_ne_true
      exact ⟨⟨⟨hyM, h1⟩, h2⟩, h3⟩
    · rintro ⟨⟨⟨hyM, h1⟩, h2⟩, h3⟩
      refine ⟨hyM, fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨fun _ => h1, fun _ => rfl⟩
      · exact ⟨fun _ => h2, fun _ => rfl⟩
      · exact ⟨fun hc => absurd hc Bool.false_ne_true, fun hmem => absurd hmem h3⟩
  rw [hLHS, hRHS] at key
  rw [← Set.diff_eq_empty, ← Set.diff_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

/-- **`idxSet e i ⊆ idxSet e j ↔ Yc P i ⊆ Yc P j`.** The `Δ = Set.univ`/`Yc P i ⊆ U.master`
simplification of `transfer_subset_iff_idxYc`, matching `Theorem88a.lean`'s `embed_subset_iff`. -/
theorem embed_subset_iff_code (i j : ℕ) : idxSet (e P) i ⊆ idxSet (e P) j ↔ Yc P i ⊆ Yc P j := by
  have := transfer_subset_iff_idxYc P i j
  rwa [Set.univ_inter, Set.inter_eq_self_of_subset_right (Yc_subset_master P i)] at this

theorem embed_eq_iff_code (i j : ℕ) : idxSet (e P) i = idxSet (e P) j ↔ Yc P i = Yc P j :=
  ⟨fun h => Set.Subset.antisymm ((embed_subset_iff_code P i j).mp h.subset)
      ((embed_subset_iff_code P j i).mp h.symm.subset),
    fun h => Set.Subset.antisymm ((embed_subset_iff_code P i j).mpr h.subset)
      ((embed_subset_iff_code P j i).mpr h.symm.subset)⟩

/-- **`e P i ⊆ e P j ↔ Yc P i ⊆ Yc P j`**, the raw-level analogue of `Theorem88a.lean`'s
`embed_subset_iff`, built from the idxSet-level `embed_subset_iff_code` via `idxSet_subset_iff`. -/
theorem embed_subset_iff_raw_code (i j : ℕ) : e P i ⊆ e P j ↔ Yc P i ⊆ Yc P j := by
  rw [← idxSet_subset_iff (e P) i j]
  exact embed_subset_iff_code P i j

/-- **`e P i = e P j ↔ Yc P i = Yc P j`**, the raw-level analogue of `Theorem88a.lean`'s
`embed_eq_iff`. -/
theorem embed_eq_iff_raw_code (i j : ℕ) : e P i = e P j ↔ Yc P i = Yc P j := by
  rw [← idxSet_eq_iff (e P) i j]
  exact embed_eq_iff_code P i j

theorem transfer_inter_eq_iff_idxYc (i j k : ℕ) :
    idxSet (e P) i ∩ idxSet (e P) j = idxSet (e P) k ↔ Yc P i ∩ Yc P j = Yc P k := by
  have h1 : idxSet (e P) k ⊆ idxSet (e P) i ↔ Yc P k ⊆ Yc P i := embed_subset_iff_code P k i
  have h2 : idxSet (e P) k ⊆ idxSet (e P) j ↔ Yc P k ⊆ Yc P j := embed_subset_iff_code P k j
  have h3 : idxSet (e P) i ∩ idxSet (e P) j ⊆ idxSet (e P) k ↔
      Yc P i ∩ Yc P j ⊆ Yc P k := by
    have := transfer_double_subset_iff_idxYc P i j k
    rwa [Set.univ_inter, Set.inter_eq_self_of_subset_right (Yc_subset_master P i)] at this
  constructor
  · intro heq
    have hki : idxSet (e P) k ⊆ idxSet (e P) i := heq ▸ Set.inter_subset_left
    have hkj : idxSet (e P) k ⊆ idxSet (e P) j := heq ▸ Set.inter_subset_right
    have hijk : idxSet (e P) i ∩ idxSet (e P) j ⊆ idxSet (e P) k := heq ▸ subset_rfl
    exact Set.Subset.antisymm (h3.mp hijk) (Set.subset_inter (h1.mp hki) (h2.mp hkj))
  · intro heq
    have hki : Yc P k ⊆ Yc P i := by rw [← heq]; exact Set.inter_subset_left
    have hkj : Yc P k ⊆ Yc P j := by rw [← heq]; exact Set.inter_subset_right
    have hijk : Yc P i ∩ Yc P j ⊆ Yc P k := by rw [heq]
    exact Set.Subset.antisymm (h3.mpr hijk) (Set.subset_inter (h1.mpr hki) (h2.mpr hkj))

/-! ## Assembling `D'' := DprimeUCode`, `D ≅ᴰ D''`, and `D'' ◁ U`

Mirrors `Theorem88a.lean`'s `DprimeU`/`domainIso`/`DprimeU_subsystem`/`isomorphic_DprimeU` verbatim,
with `Yidx (e P) ↦ Yc P` and `exists_inter_index_of_dmem`/`exists_inter_index_of_nonempty`'s calls
to `transfer_inter_eq_iff`/`transfer_inter_empty_iff` (generic, `Yseq`-flavoured) replaced by the
`Yc`-flavoured `transfer_inter_eq_iff_idxYc`/`transfer_inter_empty_iff_idxYc` above. -/

private theorem exists_inter_index_of_dmem_code {i j : ℕ} (hDij : D.mem (e P i ∩ e P j)) :
    ∃ m, e P i ∩ e P j = e P m ∧ Yc P i ∩ Yc P j = Yc P m := by
  obtain ⟨m, hm⟩ := (hcover P (e P i ∩ e P j)).mp hDij
  exact ⟨m, hm, (transfer_inter_eq_iff_idxYc P i j m).mp (idxSet_inter_of_inter_eq (e P) hm)⟩

private theorem exists_inter_index_of_nonempty_code {i j : ℕ} (hne : (Yc P i ∩ Yc P j).Nonempty) :
    ∃ m, e P i ∩ e P j = e P m ∧ Yc P i ∩ Yc P j = Yc P m := by
  have hne' : (idxSet (e P) i ∩ idxSet (e P) j).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hkey := transfer_inter_empty_iff_idxYc P i j
    rw [Set.univ_inter, Set.inter_eq_self_of_subset_right (Yc_subset_master P i)] at hkey
    exact hne.ne_empty (hkey.mp hcon)
  obtain ⟨k, hki, hkj⟩ := hne'
  exact exists_inter_index_of_dmem_code P
    (D.inter_mem (D_mem_e D (e P) (hcover P) i) (D_mem_e D (e P) (hcover P) j)
      (D_mem_e D (e P) (hcover P) k) (Set.subset_inter hki hkj))

/-- **`D'' := DprimeUCode`**: the neighbourhood system generated by `{Yc P n ∣ n ∈ ℕ}`, genuinely
code-driven (`Yc P n = UX (YseqCode P n)`), mirroring `Theorem88a.lean`'s `DprimeU` construction. -/
noncomputable def DprimeUCode : NeighborhoodSystem ℚ where
  mem Y := ∃ n, Y = Yc P n
  master := U.master
  master_mem := ⟨0, (Yc_zero_eq_master P).symm⟩
  sub_master := by rintro Y ⟨n, rfl⟩; exact Yc_subset_master P n
  inter_mem := by
    rintro X Y Z ⟨i, rfl⟩ ⟨j, rfl⟩ ⟨k, rfl⟩ hZsub
    have h1 : e P k ⊆ e P i := (embed_subset_iff_raw_code P k i).mpr (hZsub.trans Set.inter_subset_left)
    have h2 : e P k ⊆ e P j := (embed_subset_iff_raw_code P k j).mpr (hZsub.trans Set.inter_subset_right)
    obtain ⟨m, -, hYeq⟩ := exists_inter_index_of_dmem_code P
      (D.inter_mem (D_mem_e D (e P) (hcover P) i) (D_mem_e D (e P) (hcover P) j)
        (D_mem_e D (e P) (hcover P) k) (Set.subset_inter h1 h2))
    exact ⟨m, hYeq⟩

/-- **`D'' ◁ U`.** -/
theorem DprimeUCode_subsystem : DprimeUCode P ◁ U where
  master_eq := rfl
  sub := by rintro Y ⟨n, rfl⟩; exact (U_mem_UX (YseqCode P n))
  inter_closed := by
    rintro X Y ⟨i, rfl⟩ ⟨j, rfl⟩ hUmem
    obtain ⟨m, -, hYeq⟩ := exists_inter_index_of_nonempty_code P hUmem.2.1
    exact ⟨m, hYeq⟩

/-! ## The element-level isomorphism `D ≅ᴰ D''` -/

/-- **Pushforward**: the `D''`-filter induced by a `D`-filter `x`. -/
def toDprimeUCode (x : D.Element) : (DprimeUCode P).Element where
  mem Y := ∃ n, Y = Yc P n ∧ x.mem (e P n)
  sub := fun ⟨n, hn, _⟩ => ⟨n, hn⟩
  master_mem := ⟨0, (Yc_zero_eq_master P).symm, by rw [he0 P]; exact x.master_mem⟩
  inter_mem := by
    rintro X Y ⟨i, rfl, hxi⟩ ⟨j, rfl, hxj⟩
    obtain ⟨m, hem, hYeq⟩ :=
      exists_inter_index_of_dmem_code P (x.sub (x.inter_mem hxi hxj))
    exact ⟨m, hYeq, hem ▸ x.inter_mem hxi hxj⟩
  up_mem := by
    rintro X Y ⟨i, rfl, hxi⟩ ⟨j, rfl⟩ hXY
    have heij : e P i ⊆ e P j := (embed_subset_iff_raw_code P i j).mpr hXY
    exact ⟨j, rfl, x.up_mem hxi (D_mem_e D (e P) (hcover P) j) heij⟩

/-- **Pullback**: the `D`-filter induced by a `D''`-filter `y`. -/
def toDCode (y : (DprimeUCode P).Element) : D.Element where
  mem S := ∃ n, S = e P n ∧ y.mem (Yc P n)
  sub := fun ⟨n, hn, _⟩ => hn ▸ D_mem_e D (e P) (hcover P) n
  master_mem := ⟨0, (he0 P).symm, by rw [Yc_zero_eq_master P]; exact y.master_mem⟩
  inter_mem := by
    rintro S T ⟨i, rfl, hyi⟩ ⟨j, rfl, hyj⟩
    have hD'mem : (DprimeUCode P).mem (Yc P i ∩ Yc P j) := y.sub (y.inter_mem hyi hyj)
    obtain ⟨m, hem, hYeq⟩ := exists_inter_index_of_nonempty_code P
      ((DprimeUCode_subsystem P).sub hD'mem).2.1
    exact ⟨m, hem, hYeq ▸ y.inter_mem hyi hyj⟩
  up_mem := by
    rintro S T ⟨i, rfl, hyi⟩ hDT hST
    obtain ⟨j, rfl⟩ := (hcover P T).mp hDT
    have hYij : Yc P i ⊆ Yc P j := (embed_subset_iff_raw_code P i j).mp hST
    exact ⟨j, rfl, y.up_mem hyi ⟨j, rfl⟩ hYij⟩

/-- **The order isomorphism `D.Element ≃o D''.Element`.** -/
noncomputable def domainIsoCode : DomainIso D (DprimeUCode P) where
  toFun := toDprimeUCode P
  invFun := toDCode P
  left_inv x := by
    apply Element.ext
    intro S
    constructor
    · rintro ⟨n, hn, k, hk, hxk⟩
      rw [hn, (embed_eq_iff_raw_code P n k).mpr hk]
      exact hxk
    · intro hS
      obtain ⟨n, hn⟩ := (hcover P S).mp (x.sub hS)
      refine ⟨n, hn, n, rfl, ?_⟩
      rwa [← hn]
  right_inv y := by
    apply Element.ext
    intro Y
    constructor
    · rintro ⟨n, hn, k, hk, hyk⟩
      rw [hn, (embed_eq_iff_raw_code P n k).mp hk]
      exact hyk
    · intro hY
      obtain ⟨n, hn⟩ := y.sub hY
      refine ⟨n, hn, n, rfl, ?_⟩
      rwa [← hn]
  map_rel_iff' := by
    intro x x2
    constructor
    · intro hle S hxS
      obtain ⟨n, hn⟩ := (hcover P S).mp (x.sub hxS)
      have hxn : x.mem (e P n) := hn ▸ hxS
      obtain ⟨k, hk, hx2k⟩ := hle _ (⟨n, rfl, hxn⟩ : (toDprimeUCode P x).mem (Yc P n))
      rw [hn, (embed_eq_iff_raw_code P n k).mpr hk]
      exact hx2k
    · intro hle Y hY
      obtain ⟨n, hn, hxn⟩ := hY
      exact ⟨n, hn, hle _ hxn⟩

/-- **Theorem 8.8(b)(vii)(3), isomorphism half.** `D ≅ᴰ D''`. -/
theorem isomorphic_DprimeUCode : D ≅ᴰ DprimeUCode P := ⟨domainIsoCode P⟩

/-! ## Building `ComputablePresentation D''`

Mirrors `Theorem88c.lean`'s `DprimeUPresentation` verbatim, with `Yidx (e P) ↦ Yc P` and the
generic `transfer_inter_eq_iff`/`embed_subset_iff` replaced by the `Yc`-flavoured
`transfer_inter_eq_iff_idxYc`/`embed_subset_iff_raw_code` above. The two index relations
(`interEq_computable`, `cons_computable`) and the intersection index (`inter`) are **reused
unchanged** from `(P0 P)` — only the carrier family (`Yidx` ↦ `Yc P`, now genuinely code-driven)
changes; `idxSet_inter_eq_iff_DAtom`/`DAtom_pair_recDecidable` (Theorem88c.lean, stated generically
for any `ComputablePresentation Q`) apply verbatim to `Q := P0 P`. -/

private theorem inclK_i_recDecidable_code :
    RecDecidable₃ (fun i _ k => (P0 P).X k ⊆ (P0 P).X i) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.2.unpair.2 t.unpair.1) :=
    Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right) Nat.Primrec.left
  have hp := (P0 P).incl_computable.comp hg
  refine RecDecidable.of_iff (fun t => ?_) hp
  simp only [unpair_pair_fst, unpair_pair_snd]

private theorem inclK_j_recDecidable_code :
    RecDecidable₃ (fun _ j k => (P0 P).X k ⊆ (P0 P).X j) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.2.unpair.2 t.unpair.2.unpair.1) :=
    Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right)
      (Nat.Primrec.left.comp Nat.Primrec.right)
  have hp := (P0 P).incl_computable.comp hg
  refine RecDecidable.of_iff (fun t => ?_) hp
  simp only [unpair_pair_fst, unpair_pair_snd]

/-- **`Yc P i ∩ Yc P j = Yc P k` is recursively decidable in `(i, j, k)`.** Transfers
(`transfer_inter_eq_iff_idxYc`) to the `idxSet`-level equation, which `idxSet_inter_eq_iff_DAtom`
reduces to two `incl_computable` queries and one `DAtom_recDecidable` query. -/
theorem DprimeUCode_interEq_computable :
    RecDecidable₃ (fun i j k => Yc P i ∩ Yc P j = Yc P k) := by
  have hcomb : RecDecidable₃ (fun i j k =>
      ((P0 P).X k ⊆ (P0 P).X i ∧ (P0 P).X k ⊆ (P0 P).X j) ∧ DAtom (P0 P) [i, j] [k] = ∅) :=
    (inclK_i_recDecidable_code P |>.and (inclK_j_recDecidable_code P)).and (DAtom_pair_recDecidable P)
  refine RecDecidable.of_iff (fun t => ?_) hcomb
  dsimp only
  rw [← transfer_inter_eq_iff_idxYc P t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2,
    idxSet_inter_eq_iff_DAtom (P0 P) t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2]
  tauto

/-- **`∃ k, Yc P k ⊆ Yc P i ∩ Yc P j` is recursively decidable in `(i, j)`.** Transfers
(`embed_subset_iff_raw_code`, twice) to `∃ k, e P k ⊆ e P i ∧ e P k ⊆ e P j`, which is literally
`(P0 P).cons_computable`'s own predicate. -/
theorem DprimeUCode_cons_computable :
    RecDecidable₂ (fun i j => ∃ k, Yc P k ⊆ Yc P i ∩ Yc P j) := by
  refine RecDecidable.of_iff (fun t => ?_) (P0 P).cons_computable
  simp only [Set.subset_inter_iff]
  exact exists_congr (fun k => by
    rw [← embed_subset_iff_raw_code P k t.unpair.1, ← embed_subset_iff_raw_code P k t.unpair.2])

/-- **The intersection index transfers.** `(P0 P).inter n m` (Scott's own primitive-recursive
intersection index for `D`, reused verbatim) also indexes `Yc P n ∩ Yc P m` whenever that
intersection is consistent. -/
theorem DprimeUCode_inter_spec {n m : ℕ} (h : ∃ k, Yc P k ⊆ Yc P n ∩ Yc P m) :
    Yc P ((P0 P).inter n m) = Yc P n ∩ Yc P m := by
  have h' : ∃ k, (P0 P).X k ⊆ (P0 P).X n ∩ (P0 P).X m := by
    obtain ⟨k, hk⟩ := h
    rw [Set.subset_inter_iff] at hk
    exact ⟨k, Set.subset_inter ((embed_subset_iff_raw_code P k n).mpr hk.1)
      ((embed_subset_iff_raw_code P k m).mpr hk.2)⟩
  have heP : (P0 P).X ((P0 P).inter n m) = (P0 P).X n ∩ (P0 P).X m := (P0 P).inter_spec h'
  have hidx : idxSet (e P) n ∩ idxSet (e P) m = idxSet (e P) ((P0 P).inter n m) :=
    idxSet_inter_of_inter_eq (e P) heP.symm
  exact ((transfer_inter_eq_iff_idxYc P n m ((P0 P).inter n m)).mp hidx).symm

/-- **Theorem 8.8(b)(vii)(3), presentation half.** `D''` (`DprimeUCode P`, genuinely code-driven:
`X n := Yc P n = UX (YseqCode P n)`) is effectively given, with master index `0`. Its two index
relations and intersection index are reused **unchanged** from `P0 P`; only the carrier family
changed from `Yidx (e P)` (Part 6's classical choice-built sets) to `Yc P` (this file's
`Nat.Primrec`-tracked codes). -/
noncomputable def DprimeUCodePresentation : ComputablePresentation (DprimeUCode P) where
  X n := Yc P n
  mem_X n := ⟨n, rfl⟩
  surj := fun hY => hY.imp (fun _ h => h.symm)
  interEq_computable := DprimeUCode_interEq_computable P
  cons_computable := DprimeUCode_cons_computable P
  inter n m := (P0 P).inter n m
  inter_primrec := (P0 P).inter_primrec
  inter_spec h := DprimeUCode_inter_spec P h
  masterIdx := 0
  masterIdx_spec := Yc_zero_eq_master P

/-- **Theorem 8.8(b)(vii)(3), full statement.** `D''` is effectively given, `D ≅ᴰ D''`, and
`D'' ◁ U`. -/
theorem DprimeUCode_isEffectivelyGiven : (DprimeUCode P).IsEffectivelyGiven :=
  ⟨DprimeUCodePresentation P⟩

end Scott1980.Neighborhood

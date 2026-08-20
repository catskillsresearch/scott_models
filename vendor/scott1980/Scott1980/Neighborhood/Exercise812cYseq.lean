/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Exercise812c
import Scott1980.Neighborhood.Theorem88

/-!
# Exercise 8.12(c)(vi)(1) (Scott 1981, PRG-19, Lecture VIII) — the abstract `Yseq` closed form

Generalizes `Theorem88.lean`'s core `Yseq` closed-form apparatus (`atomU`, `Yseq`,
`split_fst_eq_inter_Yseq`, `atomU_subset_master`, `atomU_succ_eq`, `atomU_eq_genAtom`) from the
hardcoded target `U : NeighborhoodSystem ℚ` to an **abstract atomless `E : NeighborhoodSystem γ`**,
exactly mirroring how `Exercise812c.lean`'s `exists_split'`/`SplitSpec'`/`splitChoice'` generalized
`exists_split`/`SplitSpec`/`splitChoice`. Once done twice (once with `E := D₀`, once with
`E := D₁`, in 8.12(c)(vi)(5)/(vi)(6)), this is the machinery that recovers a *closed-form*
description of `atomPair`'s two interleaved sub-steps — the two-sided analogue of Scott's `Yₙ`.

## What is reused unchanged from `Theorem88.lean`

`extendTrue`/`restrictFin` (and their agreement lemmas `extendTrue_agree`/
`extendTrue_restrictFin_agree`) and the generic `genAtom` family (`genAtom`, `genAtom_subset`,
`genAtom_congr`, `genAtom_forward`, `genAtom_self`) are **already fully type-generic** in
`Theorem88.lean` — none of them mention `U` at all. They are imported and used *verbatim* below,
with no re-statement needed.

## What is new here

Everything downstream of `atomU` in `Theorem88.lean` (`atomU` itself onward) is hardcoded to
`U.master`/`U.mem`. This file re-proves that whole layer — `atomE` (the `atomU`-analogue),
`atomE_invariant`, `YseqE` (the `Yseq`-analogue), `split_fst_eq_inter_YseqE`, `atomE_subset_master`,
`atomE_succ_eq`, `atomE_eq_genAtom` — against an abstract `E : NeighborhoodSystem γ` and an abstract
`split` satisfying `SplitSpec' E split` (`Exercise812c.lean`), taking `E.master.Nonempty` as an
extra explicit hypothesis (`U.master`'s nonemptiness was previously a hardcoded fact about `[0,1)`;
for the eventual instantiations `E := D₀`/`E := D₁` this is exactly the `hD₀mne`/`hD₁mne` hypothesis
already in scope in `Exercise812c.lean`'s `section AtomPair`). The finite-constraint transfer lemma
(`transfer_empty_iff` and its corollaries) and the nonemptiness facts (`Yseq_empty_or_mem`/
`Yseq_nonempty_of_mem`) are deliberately **not** included here — tracked separately as
8.12(c)(vi)(2)/(vi)(3).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem

variable {α γ : Type*}

/-! ### The abstract `E`-side atom, generalizing `atomU` -/

variable (E : NeighborhoodSystem γ) (split : Set α → Set γ → Set α → Set γ × Set γ)

/-- The `E`-side atom matching `genAtom X Δ δ n`, built recursively via an abstract splitting
operation `split` satisfying `SplitSpec' E split`. Generalizes `Theorem88.lean`'s `atomU` from the
hardcoded target `U` to an abstract `E`. -/
noncomputable def atomE (E : NeighborhoodSystem γ) (split : Set α → Set γ → Set α → Set γ × Set γ)
    (X : ℕ → Set α) (Δ : Set α) (δ : ℕ → Bool) : ℕ → Set γ
  | 0 => E.master
  | (n + 1) =>
      if δ n then (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).1
      else (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).2

variable (X : ℕ → Set α) (Δ : Set α)

@[simp] theorem atomE_zero (δ : ℕ → Bool) : atomE E split X Δ δ 0 = E.master := rfl

theorem atomE_succ (δ : ℕ → Bool) (n : ℕ) :
    atomE E split X Δ δ (n + 1) =
      if δ n then (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).1
      else (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).2 := rfl

/-- Extending/changing `δ` at or beyond position `n` does not change `atomE E split X Δ δ n`
(mirrors `atomU_congr`). -/
theorem atomE_congr {δ δ' : ℕ → Bool} {n : ℕ} (h : ∀ i < n, δ i = δ' i) :
    atomE E split X Δ δ n = atomE E split X Δ δ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev : atomE E split X Δ δ n = atomE E split X Δ δ' n :=
      ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hA : genAtom X Δ δ n = genAtom X Δ δ' n :=
      genAtom_congr X Δ (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hn := h n (Nat.lt_succ_self n)
    rw [atomE_succ, atomE_succ, hA, hprev, hn]

/-! ### The core invariant: emptiness-matching, `E.mem`-or-empty, and pairwise disjointness -/

variable (hΔ : Δ.Nonempty) (hEmne : E.master.Nonempty) (hsplit : SplitSpec' E split)
include hΔ hEmne hsplit

/-- **The core invariant, generalizing `atomU_invariant`.** At every depth `n` and for every sign
sequence `δ`: (a) the atom-matching invariant (`genAtom X Δ δ n = ∅ ↔ atomE E split X Δ δ n = ∅`),
(b) `atomE E split X Δ δ n` is either empty or a genuine `E`-neighbourhood, and (c) pairwise
disjointness for sign sequences disagreeing somewhere below `n`. -/
theorem atomE_invariant :
    ∀ n, (∀ δ, genAtom X Δ δ n = ∅ ↔ atomE E split X Δ δ n = ∅) ∧
      (∀ δ, atomE E split X Δ δ n = ∅ ∨ E.mem (atomE E split X Δ δ n)) ∧
      (∀ δ δ', (∃ i < n, δ i ≠ δ' i) →
        atomE E split X Δ δ n ∩ atomE E split X Δ δ' n = ∅) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun δ => ?_, fun δ => Or.inr E.master_mem,
      fun δ δ' ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)⟩
    show Δ = ∅ ↔ (E.master : Set γ) = ∅
    exact ⟨fun h => absurd h hΔ.ne_empty, fun h => absurd h hEmne.ne_empty⟩
  | succ n ih =>
    obtain ⟨ihmatch, ihmem, ihdisj⟩ := ih
    refine ⟨fun δ => ?_, fun δ => ?_, fun δ δ' ⟨i, hi, hne⟩ => ?_⟩
    · have hspec := hsplit (ihmatch δ) (ihmem δ) (X n)
      rw [atomE_succ]
      by_cases hδ : δ n = true
      · rw [show genAtom X Δ δ (n + 1) = genAtom X Δ δ n ∩ X n from by simp [genAtom, hδ]]
        simp only [hδ, if_true]
        exact hspec.2.2.1
      · rw [Bool.not_eq_true] at hδ
        have hsub := genAtom_subset X Δ δ n
        rw [show genAtom X Δ δ (n + 1) = genAtom X Δ δ n \ X n from by
          have heq : genAtom X Δ δ (n + 1) = genAtom X Δ δ n ∩ (Δ \ X n) := by simp [genAtom, hδ]
          rw [heq]
          ext x; constructor
          · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩
          · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hsub hx1, hx2⟩]
        simp only [hδ]
        exact hspec.2.2.2.1
    · have hspec := hsplit (ihmatch δ) (ihmem δ) (X n)
      rw [atomE_succ]
      by_cases hδ : δ n = true
      · simp only [hδ, if_true]; exact hspec.1
      · simp only [hδ]; exact hspec.2.1
    · by_cases hagree : ∀ j < n, δ j = δ' j
      · have hδn : δ n ≠ δ' n := by
          intro heq
          exact hne (by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
            · exact hagree i hi'
            · exact heq)
        have hA : genAtom X Δ δ n = genAtom X Δ δ' n := genAtom_congr X Δ hagree
        have hB : atomE E split X Δ δ n = atomE E split X Δ δ' n := atomE_congr E split X Δ hagree
        have hspec := hsplit (ihmatch δ) (ihmem δ) (X n)
        rw [atomE_succ, atomE_succ, hA, hB]
        have hIJ := hspec.2.2.2.2.2
        rcases Bool.eq_false_or_eq_true (δ n) with h1 | h1 <;>
          rcases Bool.eq_false_or_eq_true (δ' n) with h2 | h2 <;>
          simp_all [Set.inter_comm]
      · push Not at hagree
        obtain ⟨j, hj, hjne⟩ := hagree
        have hd : atomE E split X Δ δ n ∩ atomE E split X Δ δ' n = ∅ := ihdisj δ δ' ⟨j, hj, hjne⟩
        have h1 : atomE E split X Δ δ (n + 1) ⊆ atomE E split X Δ δ n := by
          rw [atomE_succ]
          by_cases hδ : δ n = true
          · simp only [hδ, if_true]; exact split_fst_subset' hsplit (ihmatch δ) (ihmem δ) (X n)
          · simp only [hδ]; exact split_snd_subset' hsplit (ihmatch δ) (ihmem δ) (X n)
        have h2 : atomE E split X Δ δ' (n + 1) ⊆ atomE E split X Δ δ' n := by
          rw [atomE_succ]
          by_cases hδ' : δ' n = true
          · simp only [hδ', if_true]; exact split_fst_subset' hsplit (ihmatch δ') (ihmem δ') (X n)
          · simp only [hδ']; exact split_snd_subset' hsplit (ihmatch δ') (ihmem δ') (X n)
        exact Set.subset_eq_empty (Set.inter_subset_inter h1 h2) hd

/-- Corollary of `atomE_invariant`, extracted for reuse: `atomE` only shrinks as `n` grows
(mirrors `atomU_succ_subset`). -/
theorem atomE_succ_subset (δ : ℕ → Bool) (n : ℕ) :
    atomE E split X Δ δ (n + 1) ⊆ atomE E split X Δ δ n := by
  obtain ⟨hmatch, hmem, -⟩ := atomE_invariant E split X Δ hΔ hEmne hsplit n
  rw [atomE_succ]
  by_cases hδ : δ n = true
  · simp only [hδ, if_true]; exact split_fst_subset' hsplit (hmatch δ) (hmem δ) (X n)
  · simp only [hδ]; exact split_snd_subset' hsplit (hmatch δ) (hmem δ) (X n)

/-! ### `YseqE`: the abstract analogue of Scott's `Yₙ`

Reuses `Theorem88.lean`'s `extendTrue`/`restrictFin` verbatim (already fully generic, no `U`- or
`E`-specific content). -/

omit hΔ hEmne hsplit in
/-- **The abstract analogue of Scott's `Yₙ`**: the union, over all `2ⁿ` depth-`n` atoms, of the
"+"-piece chosen when splitting against `X n`. Generalizes `Theorem88.lean`'s `Yseq`. -/
noncomputable def YseqE (n : ℕ) : Set γ :=
  ⋃ δ' : Fin n → Bool, atomE E split X Δ (extendTrue δ') (n + 1)

omit hΔ hEmne hsplit in
theorem subset_YseqE {n : ℕ} (δ' : Fin n → Bool) :
    atomE E split X Δ (extendTrue δ') (n + 1) ⊆ YseqE E split X Δ n :=
  Set.subset_iUnion (fun δ' => atomE E split X Δ (extendTrue δ') (n + 1)) δ'

/-- **The "I-formula", generalizing `split_fst_eq_inter_Yseq`**: the "+"-piece chosen when
splitting the depth-`n` atom for `δ` against `X n` is *exactly* the intersection of that atom with
`YseqE E split X Δ n`. -/
theorem split_fst_eq_inter_YseqE (δ : ℕ → Bool) (n : ℕ) :
    (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).1 =
      atomE E split X Δ δ n ∩ YseqE E split X Δ n := by
  obtain ⟨hmatch, hmem, hdisj⟩ := atomE_invariant E split X Δ hΔ hEmne hsplit n
  set A := genAtom X Δ δ n with hAdef
  set B := atomE E split X Δ δ n with hBdef
  set I := (split A B (X n)).1 with hIdef
  set δ2 := Function.update δ n true with hδ2def
  set δ3 := extendTrue (restrictFin δ2 n) with hδ3def
  have hagreefull : ∀ i < n + 1, δ3 i = δ2 i := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · exact extendTrue_restrictFin_agree δ2 n i hi'
    · simp [hδ3def, extendTrue, hδ2def]
  have hI_eq : atomE E split X Δ δ2 (n + 1) = I := by
    rw [atomE_succ]
    have hd2n : δ2 n = true := by simp [hδ2def]
    have hA2 : genAtom X Δ δ2 n = A := by
      apply genAtom_congr; intro i hi; simp [hδ2def, Function.update_of_ne (ne_of_lt hi)]
    have hB2 : atomE E split X Δ δ2 n = B := by
      apply atomE_congr; intro i hi; simp [hδ2def, Function.update_of_ne (ne_of_lt hi)]
    rw [hd2n, if_pos rfl, hA2, hB2]
  have hδ3_eq : atomE E split X Δ δ3 (n + 1) = I := (atomE_congr E split X Δ hagreefull).trans hI_eq
  apply Set.Subset.antisymm
  · have hIsubB : I ⊆ B := split_fst_subset' hsplit (hmatch δ) (hmem δ) (X n)
    have hIsubY : I ⊆ YseqE E split X Δ n := hδ3_eq ▸ subset_YseqE E split X Δ (restrictFin δ2 n)
    exact Set.subset_inter hIsubB hIsubY
  · rintro z ⟨hzB, hzY⟩
    obtain ⟨δ', hz'⟩ := Set.mem_iUnion.mp hzY
    by_cases hagree : ∀ i < n, extendTrue δ' i = δ i
    · have hAeq : genAtom X Δ (extendTrue δ') n = A := genAtom_congr X Δ hagree
      have hBeq : atomE E split X Δ (extendTrue δ') n = B := atomE_congr E split X Δ hagree
      have hlast : extendTrue δ' n = true := by simp [extendTrue]
      have heq : atomE E split X Δ (extendTrue δ') (n + 1) = I := by
        rw [atomE_succ, hAeq, hBeq, hlast, if_pos rfl]
      rwa [heq] at hz'
    · push Not at hagree
      obtain ⟨j, hj, hjne⟩ := hagree
      have hzB' : z ∈ atomE E split X Δ (extendTrue δ') n :=
        atomE_succ_subset E split X Δ hΔ hEmne hsplit (extendTrue δ') n hz'
      have hempty := hdisj δ (extendTrue δ') ⟨j, hj, fun h => hjne (h.symm)⟩
      exact absurd (Set.mem_inter hzB hzB') (by rw [hempty]; simp)

/-- `atomE E split X Δ δ n` is always a subset of `E.master` (mirrors `atomU_subset_master`). -/
theorem atomE_subset_master (δ : ℕ → Bool) (n : ℕ) : atomE E split X Δ δ n ⊆ E.master := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact (atomE_succ_subset E split X Δ hΔ hEmne hsplit δ n).trans ih

/-- **Closed form for `atomE`, generalizing `atomU_succ_eq`**: with `YseqE` in hand, `atomE`
satisfies exactly the same recursive description as `genAtom (YseqE E split X Δ) E.master`. -/
theorem atomE_succ_eq (δ : ℕ → Bool) (n : ℕ) :
    atomE E split X Δ δ (n + 1) =
      atomE E split X Δ δ n ∩
        (if δ n then YseqE E split X Δ n else E.master \ YseqE E split X Δ n) := by
  obtain ⟨hmatch, hmem, -⟩ := atomE_invariant E split X Δ hΔ hEmne hsplit n
  have hspec := hsplit (hmatch δ) (hmem δ) (X n)
  have hIeq := split_fst_eq_inter_YseqE E split X Δ hΔ hEmne hsplit δ n
  by_cases hδ : δ n = true
  · rw [atomE_succ, if_pos hδ, if_pos hδ]; exact hIeq
  · rw [atomE_succ, if_neg hδ, if_neg hδ]
    have hJeq : (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).2 =
        atomE E split X Δ δ n \ YseqE E split X Δ n := by
      have hunion := hspec.2.2.2.2.1
      have hinter := hspec.2.2.2.2.2
      ext x
      constructor
      · intro hxJ
        have hxB : x ∈ atomE E split X Δ δ n := hunion ▸ Or.inr hxJ
        refine ⟨hxB, fun hxY => ?_⟩
        have hxI : x ∈ (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).1 :=
          hIeq ▸ Set.mem_inter hxB hxY
        exact absurd (Set.mem_inter hxI hxJ) (by rw [hinter]; simp)
      · rintro ⟨hxB, hxnY⟩
        rw [← hunion] at hxB
        rcases hxB with hxI | hxJ
        · exact absurd (hIeq ▸ hxI : x ∈ atomE E split X Δ δ n ∩ YseqE E split X Δ n).2 hxnY
        · exact hxJ
    rw [hJeq]
    have hsub := atomE_subset_master E split X Δ hΔ hEmne hsplit δ n
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hsub hx1, hx2⟩
    · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩

/-- **`atomE` coincides with the generic atom construction on `YseqE`/`E.master`**, generalizing
`atomU_eq_genAtom`. Lets every later argument treat `atomE` and `genAtom` uniformly (in particular,
`genAtom_forward`/`genAtom_self` — proved once, generically, in `Theorem88.lean` — apply verbatim
to the `E`-side atoms too). -/
theorem atomE_eq_genAtom (δ : ℕ → Bool) :
    ∀ n, atomE E split X Δ δ n = genAtom (YseqE E split X Δ) E.master δ n
  | 0 => rfl
  | (n + 1) => by
      rw [atomE_succ_eq E split X Δ hΔ hEmne hsplit, atomE_eq_genAtom δ n]; rfl

/-! ### The general finite-constraint transfer lemma, generalized to an abstract `E`

Mirrors `Theorem88.lean`'s `transfer_empty_iff`/`transfer_subset_iff`/`transfer_inter_empty_iff`/
`transfer_double_subset_iff`/`transfer_inter_eq_iff`, replacing the hardcoded `U`/`Yseq` by an
abstract `E`/`YseqE`. `transfer_dir` itself needs **no** re-proof: it is already stated fully
generically over two independent carrier types, connected only by a shared `genAtom`-emptiness
correspondence — reused verbatim from `Theorem88.lean`. -/

/-- **The transfer lemma, generalized to `E`.** A finite Boolean combination of the `X i` is
non-empty in `D`'s carrier `Δ` iff the *same* Boolean combination of `YseqE E split X Δ i` is
non-empty in `E.master`. Mirrors `transfer_empty_iff`. -/
theorem transfer_empty_iffE {cs : List (ℕ × Bool)} {n : ℕ} (hn : ∀ p ∈ cs, p.1 < n) :
    {x ∈ Δ | ∀ p ∈ cs, (p.2 = true ↔ x ∈ X p.1)}.Nonempty ↔
      {y ∈ E.master | ∀ p ∈ cs, (p.2 = true ↔ y ∈ YseqE E split X Δ p.1)}.Nonempty := by
  have hcore : ∀ δ n, genAtom X Δ δ n = ∅ ↔ genAtom (YseqE E split X Δ) E.master δ n = ∅ :=
    fun δ n => (atomE_invariant E split X Δ hΔ hEmne hsplit n).1 δ
      |>.trans (by rw [atomE_eq_genAtom E split X Δ hΔ hEmne hsplit])
  have hcore' : ∀ δ n, genAtom (YseqE E split X Δ) E.master δ n = ∅ ↔ genAtom X Δ δ n = ∅ :=
    fun δ n => (hcore δ n).symm
  exact ⟨transfer_dir X Δ (YseqE E split X Δ) E.master hcore hn,
    transfer_dir (YseqE E split X Δ) E.master X Δ hcore' hn⟩

/-- Subset transfer, generalized to `E`: `X i ⊆ X j` (restricted to `Δ`) iff `YseqE i ⊆ YseqE j`
(restricted to `E.master`). Mirrors `transfer_subset_iff`. -/
theorem transfer_subset_iffE (i j : ℕ) :
    Δ ∩ X i ⊆ X j ↔ E.master ∩ YseqE E split X Δ i ⊆ YseqE E split X Δ j := by
  have key := transfer_empty_iffE E split X Δ hΔ hEmne hsplit (cs := [(i, true), (j, false)])
    (n := max i j + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) <;> simp [Nat.lt_succ_iff])
  have hLHS : {x ∈ Δ | ∀ p ∈ [(i, true), (j, false)], (p.2 = true ↔ x ∈ X p.1)}
      = (Δ ∩ X i) \ X j := by
    ext x
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_diff, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ E.master |
      ∀ p ∈ [(i, true), (j, false)], (p.2 = true ↔ y ∈ YseqE E split X Δ p.1)}
      = (E.master ∩ YseqE E split X Δ i) \ YseqE E split X Δ j := by
    ext y
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_diff, Set.mem_inter_iff]
    tauto
  rw [hLHS, hRHS] at key
  rw [← Set.diff_eq_empty, ← Set.diff_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

/-- Intersection transfer, generalized to `E`: `X i ∩ X j` is empty on `Δ` iff `YseqE i ∩ YseqE j`
is empty on `E.master`. Mirrors `transfer_inter_empty_iff`. -/
theorem transfer_inter_empty_iffE (i j : ℕ) :
    Δ ∩ X i ∩ X j = ∅ ↔ E.master ∩ YseqE E split X Δ i ∩ YseqE E split X Δ j = ∅ := by
  have key := transfer_empty_iffE E split X Δ hΔ hEmne hsplit (cs := [(i, true), (j, true)])
    (n := max i j + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) <;> simp [Nat.lt_succ_iff])
  have hLHS : {x ∈ Δ | ∀ p ∈ [(i, true), (j, true)], (p.2 = true ↔ x ∈ X p.1)}
      = Δ ∩ X i ∩ X j := by
    ext x
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ E.master |
      ∀ p ∈ [(i, true), (j, true)], (p.2 = true ↔ y ∈ YseqE E split X Δ p.1)}
      = E.master ∩ YseqE E split X Δ i ∩ YseqE E split X Δ j := by
    ext y
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_inter_iff]
    tauto
  rw [hLHS, hRHS] at key
  rw [← Set.not_nonempty_iff_eq_empty, ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

/-- Three-term subset transfer, generalized to `E`: `X i ∩ X j ⊆ X k` (restricted to `Δ`) iff
`YseqE i ∩ YseqE j ⊆ YseqE k` (restricted to `E.master`). Mirrors `transfer_double_subset_iff`. -/
theorem transfer_double_subset_iffE (i j k : ℕ) :
    Δ ∩ X i ∩ X j ⊆ X k ↔
      E.master ∩ YseqE E split X Δ i ∩ YseqE E split X Δ j ⊆ YseqE E split X Δ k := by
  have key := transfer_empty_iffE E split X Δ hΔ hEmne hsplit
    (cs := [(i, true), (j, true), (k, false)]) (n := max i (max j k) + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl) <;>
          simp [Nat.lt_succ_iff,
            (Nat.le_max_left j k).trans (Nat.le_max_right i (max j k)),
            (Nat.le_max_right j k).trans (Nat.le_max_right i (max j k))])
  have hLHS : {x ∈ Δ | ∀ p ∈ [(i, true), (j, true), (k, false)], (p.2 = true ↔ x ∈ X p.1)}
      = (Δ ∩ X i ∩ X j) \ X k := by
    ext x
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_diff, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ E.master |
      ∀ p ∈ [(i, true), (j, true), (k, false)], (p.2 = true ↔ y ∈ YseqE E split X Δ p.1)}
      = (E.master ∩ YseqE E split X Δ i ∩ YseqE E split X Δ j) \ YseqE E split X Δ k := by
    ext y
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_diff, Set.mem_inter_iff]
    tauto
  rw [hLHS, hRHS] at key
  rw [← Set.diff_eq_empty, ← Set.diff_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

/-- `YseqE E split X Δ n` is always a subset of `E.master`. Needed by `transfer_inter_eq_iffE`
below; mirrors `Yseq_subset_master` (`Theorem88.lean`), pulled forward from 8.12(c)(vi)(3)'s
planned scope since `transfer_inter_eq_iff`'s proof genuinely depends on it. -/
theorem YseqE_subset_master (n : ℕ) : YseqE E split X Δ n ⊆ E.master :=
  Set.iUnion_subset fun δ' =>
    atomE_subset_master E split X Δ hΔ hEmne hsplit (extendTrue δ') (n + 1)

/-- **Equation transfer, generalized to `E`.** If `X k = X i ∩ X j` on `D`'s side (with all three
sets `⊆ Δ`), then `YseqE k = YseqE i ∩ YseqE j` on `E`'s side, and conversely. Mirrors
`transfer_inter_eq_iff`. -/
theorem transfer_inter_eq_iffE (i j k : ℕ) (hi : X i ⊆ Δ) (_hj : X j ⊆ Δ) (hk : X k ⊆ Δ) :
    X i ∩ X j = X k ↔ YseqE E split X Δ i ∩ YseqE E split X Δ j = YseqE E split X Δ k := by
  have h1 : X k ⊆ X i ↔ YseqE E split X Δ k ⊆ YseqE E split X Δ i := by
    have := transfer_subset_iffE E split X Δ hΔ hEmne hsplit k i
    rwa [Set.inter_eq_self_of_subset_right hk,
      Set.inter_eq_self_of_subset_right (YseqE_subset_master E split X Δ hΔ hEmne hsplit k)] at this
  have h2 : X k ⊆ X j ↔ YseqE E split X Δ k ⊆ YseqE E split X Δ j := by
    have := transfer_subset_iffE E split X Δ hΔ hEmne hsplit k j
    rwa [Set.inter_eq_self_of_subset_right hk,
      Set.inter_eq_self_of_subset_right (YseqE_subset_master E split X Δ hΔ hEmne hsplit k)] at this
  have h3 : X i ∩ X j ⊆ X k ↔
      YseqE E split X Δ i ∩ YseqE E split X Δ j ⊆ YseqE E split X Δ k := by
    have := transfer_double_subset_iffE E split X Δ hΔ hEmne hsplit i j k
    rwa [Set.inter_eq_self_of_subset_right hi,
      Set.inter_eq_self_of_subset_right (YseqE_subset_master E split X Δ hΔ hEmne hsplit i)] at this
  constructor
  · intro heq
    have hki : X k ⊆ X i := heq ▸ Set.inter_subset_left
    have hkj : X k ⊆ X j := heq ▸ Set.inter_subset_right
    have hijk : X i ∩ X j ⊆ X k := heq ▸ subset_rfl
    exact Set.Subset.antisymm (h3.mp hijk) (Set.subset_inter (h1.mp hki) (h2.mp hkj))
  · intro heq
    have hki : YseqE E split X Δ k ⊆ YseqE E split X Δ i := heq ▸ Set.inter_subset_left
    have hkj : YseqE E split X Δ k ⊆ YseqE E split X Δ j := heq ▸ Set.inter_subset_right
    have hijk : YseqE E split X Δ i ∩ YseqE E split X Δ j ⊆ YseqE E split X Δ k :=
      heq ▸ subset_rfl
    exact Set.Subset.antisymm (h3.mpr hijk) (Set.subset_inter (h1.mpr hki) (h2.mpr hkj))

/-! ### `YseqE` is non-empty (and a genuine `E`-neighbourhood) whenever `X n` is non-empty

Mirrors `Theorem88.lean`'s `Yseq_zero_eq_master`/`Yseq_empty_or_mem`/`Yseq_nonempty_of_mem`.
`YseqE_empty_or_mem` is the one place this file needs more than `hΔ`/`hEmne`/`hsplit`: `Yseq`'s own
proof leans on `U_iUnion_mem`, which is proved directly from `U`'s presented-interval structure —
an abstract `E` has no such structure, so `Exercise812c.lean`'s new, genuinely generic
`iUnion_mem_or_empty` (derived from `IsPositive` + `DiffClosed` alone) is used in its place, taking
`hEpos`/`hEdiff` as two extra explicit hypotheses. -/

/-- **`YseqE E split X Δ 0 = E.master` whenever `X 0 = Δ`** (Scott's convention `X₀ = Δ`). Mirrors
`Yseq_zero_eq_master`. -/
theorem YseqE_zero_eq_master (h0 : X 0 = Δ) : YseqE E split X Δ 0 = E.master := by
  set δ : ℕ → Bool := extendTrue (fun i : Fin 0 => i.elim0) with hδdef
  have hδ0 : δ 0 = true := by simp [hδdef, extendTrue]
  have hAB : genAtom X Δ δ 0 = ∅ ↔ atomE E split X Δ δ 0 = ∅ :=
    ⟨fun h => absurd h hΔ.ne_empty, fun h => absurd h hEmne.ne_empty⟩
  have hBE : atomE E split X Δ δ 0 = ∅ ∨ E.mem (atomE E split X Δ δ 0) := Or.inr E.master_mem
  have hspec := hsplit hAB hBE (X 0)
  have hJ : (split (genAtom X Δ δ 0) (atomE E split X Δ δ 0) (X 0)).2 = ∅ := by
    rw [← hspec.2.2.2.1]
    show genAtom X Δ δ 0 \ X 0 = ∅
    rw [show genAtom X Δ δ 0 = Δ from rfl, h0]
    exact Set.diff_self
  have hI : (split (genAtom X Δ δ 0) (atomE E split X Δ δ 0) (X 0)).1 = E.master := by
    have hunion := hspec.2.2.2.2.1
    rw [hJ, Set.union_empty] at hunion
    exact hunion
  have hkey : atomE E split X Δ δ 1 = E.master := by rw [atomE_succ, hδ0, if_pos rfl]; exact hI
  apply Set.Subset.antisymm (YseqE_subset_master E split X Δ hΔ hEmne hsplit 0)
  calc E.master = atomE E split X Δ δ 1 := hkey.symm
    _ ⊆ YseqE E split X Δ 0 := subset_YseqE E split X Δ (fun i : Fin 0 => i.elim0)

/-- `YseqE E split X Δ n` is always either empty or a genuine `E`-neighbourhood: it is a finite
union (`Fin n → Bool`) of `atomE` pieces, each of which is `∅` or `E.mem` by `atomE_invariant`, and
`E` is closed under such finite unions by `Exercise812c.lean`'s generic `iUnion_mem_or_empty`
(needing the extra hypotheses `hEpos`/`hEdiff`, absent from `Theorem88.lean`'s hardcoded
`U_iUnion_mem`). Mirrors `Yseq_empty_or_mem`. -/
theorem YseqE_empty_or_mem (hEpos : E.IsPositive) (hEdiff : E.DiffClosed) (n : ℕ) :
    YseqE E split X Δ n = ∅ ∨ E.mem (YseqE E split X Δ n) := by
  by_cases hne : (YseqE E split X Δ n).Nonempty
  · exact Or.inr ((iUnion_mem_or_empty hEpos hEdiff
      (fun δ' => (atomE_invariant E split X Δ hΔ hEmne hsplit (n + 1)).2.1 (extendTrue δ'))
      ).resolve_left hne.ne_empty)
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hne)

/-- If `x ∈ X n` (and `x ∈ Δ`), then `YseqE E split X Δ n` is non-empty. Mirrors
`Yseq_nonempty_of_mem`. -/
theorem YseqE_nonempty_of_mem {n : ℕ} {x : α} (hxΔ : x ∈ Δ) (hxn : x ∈ X n) :
    (YseqE E split X Δ n).Nonempty := by
  classical
  set δ0 : ℕ → Bool := fun k => decide (x ∈ X k) with hδ0def
  have hδ0n : δ0 n = true := by show decide (x ∈ X n) = true; rw [decide_eq_true_iff]; exact hxn
  have hxA : x ∈ genAtom X Δ δ0 n := genAtom_self X Δ hxΔ n
  have hAX : x ∈ genAtom X Δ δ0 n ∩ X n := ⟨hxA, hxn⟩
  have hAne : (genAtom X Δ δ0 n ∩ X n).Nonempty := ⟨x, hAX⟩
  obtain ⟨hmatch, hmem, -⟩ := atomE_invariant E split X Δ hΔ hEmne hsplit n
  have hspec := hsplit (hmatch δ0) (hmem δ0) (X n)
  have hIne : (split (genAtom X Δ δ0 n) (atomE E split X Δ δ0 n) (X n)).1 ≠ ∅ :=
    fun h => hAne.ne_empty (hspec.2.2.1.mpr h)
  have hI_eq_atomE : (split (genAtom X Δ δ0 n) (atomE E split X Δ δ0 n) (X n)).1 =
      atomE E split X Δ δ0 (n + 1) := by rw [atomE_succ, hδ0n, if_pos rfl]
  set δ2 : ℕ → Bool := extendTrue (restrictFin δ0 n) with hδ2def
  have hagree : ∀ i < n + 1, δ2 i = δ0 i := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · exact extendTrue_restrictFin_agree δ0 n i hi'
    · simp [hδ2def, extendTrue, hδ0n]
  have hδ2_eq : atomE E split X Δ δ2 (n + 1) = atomE E split X Δ δ0 (n + 1) :=
    atomE_congr E split X Δ hagree
  have hne2 : (atomE E split X Δ δ2 (n + 1)).Nonempty := by
    rw [hδ2_eq, ← hI_eq_atomE]
    exact Set.nonempty_iff_ne_empty.mpr hIne
  exact hne2.mono (subset_YseqE E split X Δ (restrictFin δ0 n))

end Scott1980.Neighborhood

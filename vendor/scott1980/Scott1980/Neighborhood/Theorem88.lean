/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Definition87
import Mathlib.Data.Fintype.Pi

/-!
# Theorem 8.8 (Scott 1981, PRG-19, Lecture VIII) — `U` is universal

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Theorem 8.8:

> The system `U` is universal in the sense that, for every countable neighbourhood system `D`, we
> have `D ⊴ U`. Moreover, if `D` is effectively given, then the projection pair making the
> embedding can be taken as computable. Indeed there is a correspondence between effectively
> presented domains and the computable, finitary projections of `U`.

This file works towards **Theorem 8.8(a)**, the general (non-effective) half of the theorem: every
*countable* `D` embeds as a subsystem of `U`, up to isomorphism.

## Scott's construction

Enumerate `D = {Xₙ ∣ n ∈ ℕ}` (with `X₀ = Δ = D.master`). Scott builds `Yₙ ∈ U` recursively so
that, for every `n` and every `δ ∈ {+,-}ⁿ`, writing `δX := X` if `δ = +` and `Δ \ X` if `δ = -`,
the **atom** `⋂_{i<n} δᵢXᵢ` is empty iff the corresponding atom `⋂_{i<n} δᵢYᵢ` is empty — call this
invariant `(■)`. Once built, matching `Xᵢ ↦ Yᵢ` realizes the embedding.

## This file's encoding

Rather than track the atoms via dependent `Fin n → Bool` tuples, we track them as a `List (Set α ×
Set ℚ)` of matching *pairs* `(A, B)` (the `D`-side atom and its paired `U`-side atom), which
doubles in length at each step — this is exactly `(■)` unpacked into `List` bookkeeping (matching
this codebase's usual idiom for finite combinatorial data, e.g. `presentedIntervals`'s own `List`
representation), avoiding `Fin`-indexed dependent recursion entirely.

**The key local step (`exists_split`)**: given one matching pair `(A, B)` and a new target `Xₙ`,
produce the two refined pairs for `A ∩ Xₙ` and `A \ Xₙ`. Remarkably, all three of Scott's cases are
handled *without* ever needing a general "`U`-neighbourhoods are closed under set difference"
lemma:

* `A ∩ Xₙ = ∅`: the new pairs are `(∅, ∅)` and `(A, B)` (unchanged) — no computation needed.
* `A \ Xₙ = ∅` (i.e. `A ⊆ Xₙ`): the new pairs are `(A, B)` (unchanged) and `(∅, ∅)`.
* otherwise (`A` is genuinely split by `Xₙ`): both `A ∩ Xₙ` and `A \ Xₙ` are non-empty, so (by the
  matching invariant on the old pair) `B` is a genuine, non-empty `U`-neighbourhood — split it via
  **Definition 8.7's `U_no_minimal`** into disjoint proper non-empty pieces `Y, Z` with `Y ∪ Z = B`;
  take `I := Y`, and `B \ I = Z` comes *for free* from `U_no_minimal`'s own conclusion, again with
  no separate set-difference-closure lemma required.

**Remaining work** (tracked in `arxiv.md`, not yet in this file): package `exists_split` into the
`List`-of-pairs recursive construction of the full sequence `Y : ℕ → Set ℚ`, derive the inclusion
correspondence `Xᵢ ⊆ Xⱼ ↔ Yᵢ ⊆ Yⱼ` from the atom invariant, and assemble the final `∃ D' : Neighbo
rhoodSystem ℚ, D ≅ᴰ D' ∧ D' ◁ U` statement. `Classical.choice` is expected and acceptable throughout
this file's `Theorem 8.8(a)` development: it is a genuinely non-constructive `Prop`-level existence
statement for an *arbitrary* countable `D` (Scott's own remark that the effective case needs the
*additional* `𝒟 ≅ 𝒟†` preparation, absent here, to make the case-splits decidable rather than merely
classical, is the substance of the follow-up Theorem 8.8(b)).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem

variable {α : Type*}

/-- **The key local splitting step behind Theorem 8.8(a)'s back-and-forth construction.** Given a
`D`-side atom `A` matched with a `U`-side atom `B` (`A = ∅ ↔ B = ∅`, and `B` is either empty or a
genuine `U`-neighbourhood), and a new target set `Xₙ` (morally the next `D`-neighbourhood `Xₙ`),
produce matching refinements `I` (for `A ∩ Xₙ`) and `J` (for `A \ Xₙ`). -/
theorem exists_split {A : Set α} {B : Set ℚ} (hAB : A = ∅ ↔ B = ∅)
    (hBU : B = ∅ ∨ U.mem B) (Xn : Set α) :
    ∃ I J : Set ℚ, (I = ∅ ∨ U.mem I) ∧ (J = ∅ ∨ U.mem J) ∧
      (A ∩ Xn = ∅ ↔ I = ∅) ∧ (A \ Xn = ∅ ↔ J = ∅) ∧ I ∪ J = B ∧ I ∩ J = ∅ := by
  by_cases h1 : A ∩ Xn = ∅
  · refine ⟨∅, B, Or.inl rfl, hBU, by simp [h1], ?_, by simp, by simp⟩
    have hAeq : A \ Xn = A := by
      ext x
      simp only [Set.mem_diff]
      refine ⟨fun hx => hx.1, fun hx => ⟨hx, fun hxn => ?_⟩⟩
      exact Set.eq_empty_iff_forall_notMem.mp h1 x ⟨hx, hxn⟩
    rw [hAeq, hAB]
  · by_cases h2 : A \ Xn = ∅
    · refine ⟨B, ∅, hBU, Or.inl rfl, ?_, iff_of_true h2 rfl, by simp, by simp⟩
      have hAeq : A ∩ Xn = A := by
        ext x
        simp only [Set.mem_inter_iff]
        refine ⟨fun hx => hx.1, fun hx => ⟨hx, ?_⟩⟩
        by_contra hxn
        exact Set.eq_empty_iff_forall_notMem.mp h2 x ⟨hx, hxn⟩
      rw [hAeq, hAB]
    · have hAne : A ≠ ∅ := by
        intro hA
        apply h1
        rw [hA]
        exact Set.empty_inter Xn
      have hBne : B ≠ ∅ := fun hB => hAne (hAB.mpr hB)
      have hBU' : U.mem B := hBU.resolve_left hBne
      obtain ⟨Y, Z, hY, hZ, hYZinter, hYZunion, -, -⟩ := U_no_minimal hBU'
      have hYne : Y ≠ ∅ := hY.2.1.ne_empty
      have hZne : Z ≠ ∅ := hZ.2.1.ne_empty
      exact ⟨Y, Z, Or.inr hY, Or.inr hZ, iff_of_false h1 hYne, iff_of_false h2 hZne,
        hYZunion, hYZinter⟩

/-! ### Boolean atoms, indexed by `δ : ℕ → Bool`

The recursion below tracks the atom `⋂_{i<n} δᵢZᵢ` for a *sign sequence* `δ : ℕ → Bool` and a
family `Z : ℕ → Set β` relative to a master set `M` (Scott's `Δ` on the `D`-side, `U.master` on
the `U`-side). We deliberately index by *all* of `ℕ → Bool` rather than `Fin n → Bool`: since
`genAtom Z M δ n` only ever inspects `δ 0, …, δ (n-1)` (`genAtom_congr` below), this sidesteps
`Fin`-indexed dependent bookkeeping entirely for every *characterization* lemma, at the cost of
harmless redundancy (many `δ` present the same atom). A genuine finite index type (`Fin n → Bool`)
only reappears once, locally, when a *finite union* is actually needed (`Yseq`, below). -/

def genAtom {β : Type*} (Z : ℕ → Set β) (M : Set β) (δ : ℕ → Bool) : ℕ → Set β
  | 0 => M
  | (n + 1) => genAtom Z M δ n ∩ (if δ n then Z n else M \ Z n)

theorem genAtom_subset {β : Type*} (Z : ℕ → Set β) (M : Set β) (δ : ℕ → Bool) (n : ℕ) :
    genAtom Z M δ n ⊆ M := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact (Set.inter_subset_left).trans ih

/-- Extending/changing `δ` at or beyond position `n` does not change `genAtom Z M δ n`. -/
theorem genAtom_congr {β : Type*} (Z : ℕ → Set β) (M : Set β) {δ δ' : ℕ → Bool} {n : ℕ}
    (h : ∀ i < n, δ i = δ' i) : genAtom Z M δ n = genAtom Z M δ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := h n (Nat.lt_succ_self n)
    have hprev : genAtom Z M δ n = genAtom Z M δ' n := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    show genAtom Z M δ n ∩ _ = genAtom Z M δ' n ∩ _
    rw [hprev, hn]

/-- **Forward direction of atom membership**: if `x` lies in the depth-`n` atom for `δ`, then `δ`
records `x`'s membership pattern against `Z 0, …, Z (n-1)` exactly. (The converse, "self-atom
membership" for the canonical `δ` built from `x` itself, is `genAtom_self` below; together they
are all that is needed — no general "iff" characterization with explicit list/`Fin` indexing is
required anywhere in this file.) -/
theorem genAtom_forward {β : Type*} {Z : ℕ → Set β} {M : Set β} {δ : ℕ → Bool} {n : ℕ}
    {x : β} (hx : x ∈ genAtom Z M δ n) : ∀ i < n, (δ i = true ↔ x ∈ Z i) := by
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro i hi
    obtain ⟨hxprev, hxlast⟩ := hx
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · exact ih hxprev i hi'
    · by_cases hδ : δ i = true
      · simp only [hδ, if_true] at hxlast
        exact ⟨fun _ => hxlast, fun _ => hδ⟩
      · rw [Bool.not_eq_true] at hδ
        simp only [hδ] at hxlast
        exact ⟨fun h => absurd h (by simp [hδ]), fun hmem => absurd hmem hxlast.2⟩

open Classical in
/-- **Self-atom membership**: any `x ∈ M` lies in its own canonical atom (built from the
sign sequence `δ := fun k => decide (x ∈ Z k)`), at every depth `n`. -/
theorem genAtom_self {β : Type*} (Z : ℕ → Set β) (M : Set β) {x : β} (hx : x ∈ M) :
    ∀ n, x ∈ genAtom Z M (fun k => decide (x ∈ Z k)) n := by
  intro n
  induction n with
  | zero => exact hx
  | succ n ih =>
    refine ⟨ih, ?_⟩
    by_cases h : x ∈ Z n
    · simp [h]
    · simp [h, hx]

/-! ### Packaging `exists_split` as a total choice function

**Generalization for Theorem 8.8(b).** Everything from `atomU` onward in this file is stated
relative to an *abstract* splitting operation `split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ`
satisfying `SplitSpec` — exactly `exists_split`'s conclusion, packaged as a total function rather
than a dependent existential. Theorem 8.8(a) (`Theorem88a.lean`) instantiates this with the
classical `splitChoice` below (via `Classical.choice` on `exists_split`'s existential — the *only*
place non-constructivity enters this file). Theorem 8.8(b)'s effective refinement
(`DAtomDecidable.lean` onward) instantiates the *same* generic theorems with a **computable**
`splitEff`, built from `SplitU.lean`'s deterministic `splitU` and `DAtomDecidable.lean`'s decidable
atom-emptiness test — getting the entire invariant/transfer apparatus below "for free", with no
need to reprove any of it. -/

/-- **The abstract specification a splitting operation must satisfy** — exactly `exists_split`'s
conclusion, as a `Prop` about a *total* function `split`. Both the classical `splitChoice` (via
`Classical.choice`) and the effective, computable `splitEff` (Theorem 8.8(b)) satisfy this. -/
def SplitSpec (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ) : Prop :=
  ∀ {A : Set α} {B : Set ℚ}, (A = ∅ ↔ B = ∅) → (B = ∅ ∨ U.mem B) → ∀ Xn : Set α,
    ((split A B Xn).1 = ∅ ∨ U.mem (split A B Xn).1) ∧
      ((split A B Xn).2 = ∅ ∨ U.mem (split A B Xn).2) ∧
      (A ∩ Xn = ∅ ↔ (split A B Xn).1 = ∅) ∧
      (A \ Xn = ∅ ↔ (split A B Xn).2 = ∅) ∧
      (split A B Xn).1 ∪ (split A B Xn).2 = B ∧
      (split A B Xn).1 ∩ (split A B Xn).2 = ∅

open Classical in
/-- **Total packaging of `exists_split`.** Given any `A : Set α`, `B : Set ℚ`, `Xn : Set α`,
`splitChoice A B Xn` is the pair `(I, J)` produced by `exists_split` whenever the hypotheses hold
(`A = ∅ ↔ B = ∅` and `B = ∅ ∨ U.mem B`), and the junk value `(∅, ∅)` otherwise. Making this total
(rather than threading proof obligations through a dependent recursive definition) is what lets
`atomU` below be defined by plain structural recursion on `ℕ`; `splitChoice_isSplitSpec` recovers
`exists_split`'s conclusions whenever the hypotheses genuinely hold, which is all that is ever
used (the junk branch is never reached along the real construction). -/
noncomputable def splitChoice (A : Set α) (B : Set ℚ) (Xn : Set α) : Set ℚ × Set ℚ :=
  if h : (A = ∅ ↔ B = ∅) ∧ (B = ∅ ∨ U.mem B) then
    ⟨(exists_split h.1 h.2 Xn).choose, (exists_split h.1 h.2 Xn).choose_spec.choose⟩
  else (∅, ∅)

theorem splitChoice_isSplitSpec : SplitSpec (α := α) splitChoice := by
  intro A B hAB hBU Xn
  classical
  unfold splitChoice
  rw [dif_pos ⟨hAB, hBU⟩]
  exact (exists_split hAB hBU Xn).choose_spec.choose_spec

/-- **A splitting operation's first output is a subset of `B`** (`I ⊆ B`, from `I ∪ J = B`) —
a corollary of `SplitSpec` alone, needing no facts about the specific `split`. -/
theorem split_fst_subset {split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ} (hsplit : SplitSpec split)
    {A : Set α} {B : Set ℚ} (hAB : A = ∅ ↔ B = ∅)
    (hBU : B = ∅ ∨ U.mem B) (Xn : Set α) : (split A B Xn).1 ⊆ B :=
  Set.subset_union_left.trans_eq (hsplit hAB hBU Xn).2.2.2.2.1

/-- **A splitting operation's second output is a subset of `B`** (`J ⊆ B`, from `I ∪ J = B`). -/
theorem split_snd_subset {split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ} (hsplit : SplitSpec split)
    {A : Set α} {B : Set ℚ} (hAB : A = ∅ ↔ B = ∅)
    (hBU : B = ∅ ∨ U.mem B) (Xn : Set α) : (split A B Xn).2 ⊆ B :=
  Set.subset_union_right.trans_eq (hsplit hAB hBU Xn).2.2.2.2.1

/-! ### The `U`-side atoms, built via an abstract splitting operation

Fix the enumeration `X : ℕ → Set α` of `D` and its master `Δ := D.master`, and a splitting
operation `split` satisfying `SplitSpec`. The `D`-side atom at depth `n` for sign sequence `δ` is
simply `genAtom X Δ δ n` (no new definition needed). The `U`-side atom `atomU split X Δ δ n` is
built by recursion, splitting the *previous* atom via `split` against the *next* target `X n`,
taking the `δ n`-side of the split. -/

variable (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)

/-- The `U`-side atom matching `genAtom X Δ δ n`, built recursively via an abstract splitting
operation `split` (instantiated with `splitChoice` for Theorem 8.8(a), `splitEff` for 8.8(b)). -/
noncomputable def atomU (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)
    (X : ℕ → Set α) (Δ : Set α) (δ : ℕ → Bool) : ℕ → Set ℚ
  | 0 => U.master
  | (n + 1) =>
      if δ n then (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).1
      else (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).2

variable (X : ℕ → Set α) (Δ : Set α)

@[simp] theorem atomU_zero (δ : ℕ → Bool) : atomU split X Δ δ 0 = U.master := rfl

theorem atomU_succ (δ : ℕ → Bool) (n : ℕ) :
    atomU split X Δ δ (n + 1) =
      if δ n then (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).1
      else (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).2 := rfl

/-- Extending/changing `δ` at or beyond position `n` does not change `atomU split X Δ δ n` (mirrors
`genAtom_congr`; needs no invariant, since `split` is an ordinary function of its inputs). -/
theorem atomU_congr {δ δ' : ℕ → Bool} {n : ℕ} (h : ∀ i < n, δ i = δ' i) :
    atomU split X Δ δ n = atomU split X Δ δ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev : atomU split X Δ δ n = atomU split X Δ δ' n :=
      ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hA : genAtom X Δ δ n = genAtom X Δ δ' n :=
      genAtom_congr X Δ (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hn := h n (Nat.lt_succ_self n)
    rw [atomU_succ, atomU_succ, hA, hprev, hn]

/-! ### The core invariant: emptiness-matching, `U.mem`-or-empty, and pairwise disjointness -/

variable (hΔ : Δ.Nonempty) (hsplit : SplitSpec split)
include hΔ hsplit

/-- **The core invariant of Scott's back-and-forth construction**, proved by a single induction on
`n` alongside `split`'s spec: at every depth `n` and for every sign sequence `δ`,
(a) the atom-matching invariant `(■)` (`genAtom X Δ δ n = ∅ ↔ atomU split X Δ δ n = ∅`),
(b) `atomU split X Δ δ n` is either empty or a genuine `U`-neighbourhood, and
(c) **pairwise disjointness**: atoms for sign sequences disagreeing somewhere below `n` are
disjoint on the `U`-side. (c) is what lets `Yseq` (below) recover a *closed-form* recursive
description of `atomU`, exactly mirroring `genAtom`'s. -/
theorem atomU_invariant :
    ∀ n, (∀ δ, genAtom X Δ δ n = ∅ ↔ atomU split X Δ δ n = ∅) ∧
      (∀ δ, atomU split X Δ δ n = ∅ ∨ U.mem (atomU split X Δ δ n)) ∧
      (∀ δ δ', (∃ i < n, δ i ≠ δ' i) →
        atomU split X Δ δ n ∩ atomU split X Δ δ' n = ∅) := by
  have hUmasterNe : (U.master : Set ℚ) ≠ ∅ := Set.Nonempty.ne_empty ⟨0, by norm_num [U]⟩
  intro n
  induction n with
  | zero =>
    refine ⟨fun δ => ?_, fun δ => Or.inr U.master_mem, fun δ δ' ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)⟩
    show Δ = ∅ ↔ (U.master : Set ℚ) = ∅
    exact ⟨fun h => absurd h hΔ.ne_empty, fun h => absurd h hUmasterNe⟩
  | succ n ih =>
    obtain ⟨ihmatch, ihmem, ihdisj⟩ := ih
    refine ⟨fun δ => ?_, fun δ => ?_, fun δ δ' ⟨i, hi, hne⟩ => ?_⟩
    · have hspec := hsplit (ihmatch δ) (ihmem δ) (X n)
      rw [atomU_succ]
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
      rw [atomU_succ]
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
        have hB : atomU split X Δ δ n = atomU split X Δ δ' n := atomU_congr split X Δ hagree
        have hspec := hsplit (ihmatch δ) (ihmem δ) (X n)
        rw [atomU_succ, atomU_succ, hA, hB]
        have hIJ := hspec.2.2.2.2.2
        rcases Bool.eq_false_or_eq_true (δ n) with h1 | h1 <;>
          rcases Bool.eq_false_or_eq_true (δ' n) with h2 | h2 <;>
          simp_all [Set.inter_comm]
      · push Not at hagree
        obtain ⟨j, hj, hjne⟩ := hagree
        have hd : atomU split X Δ δ n ∩ atomU split X Δ δ' n = ∅ := ihdisj δ δ' ⟨j, hj, hjne⟩
        have h1 : atomU split X Δ δ (n + 1) ⊆ atomU split X Δ δ n := by
          rw [atomU_succ]
          by_cases hδ : δ n = true
          · simp only [hδ, if_true]; exact split_fst_subset hsplit (ihmatch δ) (ihmem δ) (X n)
          · simp only [hδ]; exact split_snd_subset hsplit (ihmatch δ) (ihmem δ) (X n)
        have h2 : atomU split X Δ δ' (n + 1) ⊆ atomU split X Δ δ' n := by
          rw [atomU_succ]
          by_cases hδ' : δ' n = true
          · simp only [hδ', if_true]; exact split_fst_subset hsplit (ihmatch δ') (ihmem δ') (X n)
          · simp only [hδ']; exact split_snd_subset hsplit (ihmatch δ') (ihmem δ') (X n)
        exact Set.subset_eq_empty (Set.inter_subset_inter h1 h2) hd

/-- Corollary of `atomU_invariant`, extracted for reuse: `atomU` only shrinks as `n` grows. -/
theorem atomU_succ_subset (δ : ℕ → Bool) (n : ℕ) :
    atomU split X Δ δ (n + 1) ⊆ atomU split X Δ δ n := by
  obtain ⟨hmatch, hmem, -⟩ := atomU_invariant split X Δ hΔ hsplit n
  rw [atomU_succ]
  by_cases hδ : δ n = true
  · simp only [hδ, if_true]; exact split_fst_subset hsplit (hmatch δ) (hmem δ) (X n)
  · simp only [hδ]; exact split_snd_subset hsplit (hmatch δ) (hmem δ) (X n)

/-! ### `Yseq`: Scott's `Yₙ`, the union of the "+"-pieces of all depth-`n` atoms

A genuine `Fintype` index (`Fin n → Bool`) is used *only* here, to state a bona fide finite union;
`extendTrue` promotes a length-`n` sign sequence to a full `δ : ℕ → Bool` by padding with `true`
(the padding value is irrelevant beyond position `n`, and *must* be `true` at position `n` itself,
to select the "+"-branch of the split there). -/

/-- Pad `δ' : Fin n → Bool` to a total `ℕ → Bool`, filling positions `≥ n` with `true`. -/
def extendTrue {n : ℕ} (δ' : Fin n → Bool) : ℕ → Bool :=
  fun i => if h : i < n then δ' ⟨i, h⟩ else true

/-- Restrict `δ : ℕ → Bool` to `Fin n → Bool`. -/
def restrictFin (δ : ℕ → Bool) (n : ℕ) : Fin n → Bool := fun i => δ i.val

omit hΔ hsplit in
theorem extendTrue_agree {n : ℕ} (δ' : Fin n → Bool) (i : ℕ) (hi : i < n) :
    extendTrue δ' i = δ' ⟨i, hi⟩ := by simp [extendTrue, hi]

omit hΔ hsplit in
theorem extendTrue_restrictFin_agree (δ : ℕ → Bool) (n i : ℕ) (hi : i < n) :
    extendTrue (restrictFin δ n) i = δ i := by simp [extendTrue, restrictFin, hi]

/-- **Scott's `Yₙ`**: the union, over all `2ⁿ` depth-`n` atoms, of the "+"-piece chosen when
splitting against `X n`. -/
noncomputable def Yseq (n : ℕ) : Set ℚ :=
  ⋃ δ' : Fin n → Bool, atomU split X Δ (extendTrue δ') (n + 1)

omit hΔ hsplit in
theorem subset_Yseq {n : ℕ} (δ' : Fin n → Bool) :
    atomU split X Δ (extendTrue δ') (n + 1) ⊆ Yseq split X Δ n :=
  Set.subset_iUnion (fun δ' => atomU split X Δ (extendTrue δ') (n + 1)) δ'

/-- **The "I-formula"**: the "+"-piece chosen when splitting the depth-`n` atom for `δ` against
`X n` is *exactly* the intersection of that atom with `Yseq n` — recovering, after the fact, a
closed-form description of the choice made by `split`. This is where pairwise disjointness
(`atomU_invariant`'s third clause) is essential: it rules out any *other* depth-`n` atom (from a
different, non-agreeing `δ`) contributing a point to `Yseq n` that isn't already forced into this
one. -/
theorem split_fst_eq_inter_Yseq (δ : ℕ → Bool) (n : ℕ) :
    (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).1 =
      atomU split X Δ δ n ∩ Yseq split X Δ n := by
  obtain ⟨hmatch, hmem, hdisj⟩ := atomU_invariant split X Δ hΔ hsplit n
  set A := genAtom X Δ δ n with hAdef
  set B := atomU split X Δ δ n with hBdef
  set I := (split A B (X n)).1 with hIdef
  set δ2 := Function.update δ n true with hδ2def
  set δ3 := extendTrue (restrictFin δ2 n) with hδ3def
  have hagreefull : ∀ i < n + 1, δ3 i = δ2 i := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · exact extendTrue_restrictFin_agree δ2 n i hi'
    · simp [hδ3def, extendTrue, hδ2def]
  have hI_eq : atomU split X Δ δ2 (n + 1) = I := by
    rw [atomU_succ]
    have hd2n : δ2 n = true := by simp [hδ2def]
    have hA2 : genAtom X Δ δ2 n = A := by
      apply genAtom_congr; intro i hi; simp [hδ2def, Function.update_of_ne (ne_of_lt hi)]
    have hB2 : atomU split X Δ δ2 n = B := by
      apply atomU_congr; intro i hi; simp [hδ2def, Function.update_of_ne (ne_of_lt hi)]
    rw [hd2n, if_pos rfl, hA2, hB2]
  have hδ3_eq : atomU split X Δ δ3 (n + 1) = I := (atomU_congr split X Δ hagreefull).trans hI_eq
  apply Set.Subset.antisymm
  · have hIsubB : I ⊆ B := split_fst_subset hsplit (hmatch δ) (hmem δ) (X n)
    have hIsubY : I ⊆ Yseq split X Δ n := hδ3_eq ▸ subset_Yseq split X Δ (restrictFin δ2 n)
    exact Set.subset_inter hIsubB hIsubY
  · rintro z ⟨hzB, hzY⟩
    obtain ⟨δ', hz'⟩ := Set.mem_iUnion.mp hzY
    by_cases hagree : ∀ i < n, extendTrue δ' i = δ i
    · have hAeq : genAtom X Δ (extendTrue δ') n = A := genAtom_congr X Δ hagree
      have hBeq : atomU split X Δ (extendTrue δ') n = B := atomU_congr split X Δ hagree
      have hlast : extendTrue δ' n = true := by simp [extendTrue]
      have heq : atomU split X Δ (extendTrue δ') (n + 1) = I := by
        rw [atomU_succ, hAeq, hBeq, hlast, if_pos rfl]
      rwa [heq] at hz'
    · push Not at hagree
      obtain ⟨j, hj, hjne⟩ := hagree
      have hzB' : z ∈ atomU split X Δ (extendTrue δ') n :=
        atomU_succ_subset split X Δ hΔ hsplit (extendTrue δ') n hz'
      have hempty := hdisj δ (extendTrue δ') ⟨j, hj, fun h => hjne (h.symm)⟩
      exact absurd (Set.mem_inter hzB hzB') (by rw [hempty]; simp)

theorem atomU_subset_master (δ : ℕ → Bool) (n : ℕ) : atomU split X Δ δ n ⊆ U.master := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact (atomU_succ_subset split X Δ hΔ hsplit δ n).trans ih

/-- **Closed form for `atomU`**: with `Yseq` in hand, `atomU` satisfies exactly the same
recursive description as `genAtom Yseq U.master` — the choices made by `split` are, after
the fact, forced (`split_fst_eq_inter_Yseq` handles the `true` branch; the `false` branch
follows algebraically from `I ∪ J = B`, `I ∩ J = ∅`). -/
theorem atomU_succ_eq (δ : ℕ → Bool) (n : ℕ) :
    atomU split X Δ δ (n + 1) =
      atomU split X Δ δ n ∩ (if δ n then Yseq split X Δ n else U.master \ Yseq split X Δ n) := by
  obtain ⟨hmatch, hmem, -⟩ := atomU_invariant split X Δ hΔ hsplit n
  have hspec := hsplit (hmatch δ) (hmem δ) (X n)
  have hIeq := split_fst_eq_inter_Yseq split X Δ hΔ hsplit δ n
  by_cases hδ : δ n = true
  · rw [atomU_succ, if_pos hδ, if_pos hδ]; exact hIeq
  · rw [atomU_succ, if_neg hδ, if_neg hδ]
    have hJeq : (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).2 =
        atomU split X Δ δ n \ Yseq split X Δ n := by
      have hunion := hspec.2.2.2.2.1
      have hinter := hspec.2.2.2.2.2
      ext x
      constructor
      · intro hxJ
        have hxB : x ∈ atomU split X Δ δ n := hunion ▸ Or.inr hxJ
        refine ⟨hxB, fun hxY => ?_⟩
        have hxI : x ∈ (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).1 :=
          hIeq ▸ Set.mem_inter hxB hxY
        exact absurd (Set.mem_inter hxI hxJ) (by rw [hinter]; simp)
      · rintro ⟨hxB, hxnY⟩
        rw [← hunion] at hxB
        rcases hxB with hxI | hxJ
        · exact absurd (hIeq ▸ hxI : x ∈ atomU split X Δ δ n ∩ Yseq split X Δ n).2 hxnY
        · exact hxJ
    rw [hJeq]
    have hsub := atomU_subset_master split X Δ hΔ hsplit δ n
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hsub hx1, hx2⟩
    · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩

/-- **`atomU` coincides with the generic atom construction on `Yseq`/`U.master`.** This is the
payoff of the whole `split`/disjointness apparatus: it lets every later argument treat
`atomU` and `genAtom` uniformly (in particular, `genAtom_forward` and `genAtom_self` — proved once,
generically — now apply verbatim to the `U`-side atoms too). -/
theorem atomU_eq_genAtom (δ : ℕ → Bool) :
    ∀ n, atomU split X Δ δ n = genAtom (Yseq split X Δ) U.master δ n
  | 0 => rfl
  | (n + 1) => by
      rw [atomU_succ_eq split X Δ hΔ hsplit, atomU_eq_genAtom δ n]; rfl

/-! ### The general finite-constraint transfer lemma

This is the payoff of the whole apparatus above: *any* finite conjunction of membership/
non-membership constraints against `X 0, X 1, …` is non-empty iff the corresponding constraint
against `Y 0 := Yseq 0, Y 1 := Yseq 1, …` is non-empty. Subset- and intersection-transfer facts
(needed for `D'`'s `NeighborhoodSystem` axioms and the element-level isomorphism) both drop out as
one-line corollaries by unfolding the constraint set. -/

-- One-directional half of the transfer lemma, stated fully generically (over two independent
-- carrier types related only by a shared `genAtom`-emptiness correspondence `hcore`) so that it
-- can be reused, symmetrically, for both directions of the two-sided statement
-- `transfer_empty_iff`. Not `private`: also reused verbatim by `Exercise812cYseq.lean`'s
-- `transfer_empty_iffE` (8.12(c)(vi)(2)), since it is already fully generic over two independent
-- carrier types.
omit hΔ hsplit in
theorem transfer_dir {β1 β2 : Type*} (Z1 : ℕ → Set β1) (M1 : Set β1) (Z2 : ℕ → Set β2)
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

/-- **The transfer lemma.** A finite Boolean combination of the `X i` (`i` ranging over the
finite constraint list `cs`, `true` meaning "in", `false` meaning "out") is non-empty in `D`'s
carrier `Δ` iff the *same* Boolean combination of the `Y i := Yseq X Δ i` is non-empty in `U`'s
master neighborhood. This is the single fact from which the order-isomorphism `D ≅ᴰ D'` and the
subsystem relation `D' ◁ U` are both assembled. -/
theorem transfer_empty_iff {cs : List (ℕ × Bool)} {n : ℕ} (hn : ∀ p ∈ cs, p.1 < n) :
    {x ∈ Δ | ∀ p ∈ cs, (p.2 = true ↔ x ∈ X p.1)}.Nonempty ↔
      {y ∈ U.master | ∀ p ∈ cs, (p.2 = true ↔ y ∈ Yseq split X Δ p.1)}.Nonempty := by
  have hcore : ∀ δ n, genAtom X Δ δ n = ∅ ↔ genAtom (Yseq split X Δ) U.master δ n = ∅ :=
    fun δ n => (atomU_invariant split X Δ hΔ hsplit n).1 δ
      |>.trans (by rw [atomU_eq_genAtom split X Δ hΔ hsplit])
  have hcore' : ∀ δ n, genAtom (Yseq split X Δ) U.master δ n = ∅ ↔ genAtom X Δ δ n = ∅ :=
    fun δ n => (hcore δ n).symm
  exact ⟨transfer_dir X Δ (Yseq split X Δ) U.master hcore hn,
    transfer_dir (Yseq split X Δ) U.master X Δ hcore' hn⟩

/-- Subset transfer: `X i ⊆ X j` (restricted to the carrier `Δ`) iff `Y i ⊆ Y j` (restricted to
`U.master`). Obtained from `transfer_empty_iff` applied to the two-point constraint list
witnessing `x ∈ X i \ X j`. -/
theorem transfer_subset_iff (i j : ℕ) :
    Δ ∩ X i ⊆ X j ↔ U.master ∩ Yseq split X Δ i ⊆ Yseq split X Δ j := by
  have key := transfer_empty_iff split X Δ hΔ hsplit (cs := [(i, true), (j, false)])
    (n := max i j + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) <;> simp [Nat.lt_succ_iff])
  have hLHS : {x ∈ Δ | ∀ p ∈ [(i, true), (j, false)], (p.2 = true ↔ x ∈ X p.1)}
      = (Δ ∩ X i) \ X j := by
    ext x
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_diff, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ U.master |
      ∀ p ∈ [(i, true), (j, false)], (p.2 = true ↔ y ∈ Yseq split X Δ p.1)}
      = (U.master ∩ Yseq split X Δ i) \ Yseq split X Δ j := by
    ext y
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_diff, Set.mem_inter_iff]
    tauto
  rw [hLHS, hRHS] at key
  rw [← Set.diff_eq_empty, ← Set.diff_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

/-- Intersection transfer: `X i ∩ X j` is empty on `Δ` iff `Y i ∩ Y j` is empty on `U.master`. This
is the key fact ensuring the map `Xᵢ ↦ Yᵢ` respects both inclusions *and* incompatibility, i.e.
that it extends to an order isomorphism between the atomic Boolean combinations, hence to an
order isomorphism of the generated `NeighborhoodSystem`s. -/
theorem transfer_inter_empty_iff (i j : ℕ) :
    Δ ∩ X i ∩ X j = ∅ ↔ U.master ∩ Yseq split X Δ i ∩ Yseq split X Δ j = ∅ := by
  have key := transfer_empty_iff split X Δ hΔ hsplit (cs := [(i, true), (j, true)])
    (n := max i j + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) <;> simp [Nat.lt_succ_iff])
  have hLHS : {x ∈ Δ | ∀ p ∈ [(i, true), (j, true)], (p.2 = true ↔ x ∈ X p.1)}
      = Δ ∩ X i ∩ X j := by
    ext x
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ U.master | ∀ p ∈ [(i, true), (j, true)], (p.2 = true ↔ y ∈ Yseq split X Δ p.1)}
      = U.master ∩ Yseq split X Δ i ∩ Yseq split X Δ j := by
    ext y
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_inter_iff]
    tauto
  rw [hLHS, hRHS] at key
  rw [← Set.not_nonempty_iff_eq_empty, ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

/-- Three-term subset transfer: `X i ∩ X j ⊆ X k` (restricted to `Δ`) iff `Y i ∩ Y j ⊆ Y k`
(restricted to `U.master`). Combined with two applications of `transfer_subset_iff` (in the
`m ⊆ i`/`m ⊆ j` direction), this lets an *equation* `X i ∩ X j = X k` on the `D`-side transfer to
the equation `Y i ∩ Y j = Y k` on the `U`-side, and conversely — exactly the fact needed to move
`D`'s own `inter_mem` witnessed-consistency structure across the `Xᵢ ↦ Yᵢ` correspondence. -/
theorem transfer_double_subset_iff (i j k : ℕ) :
    Δ ∩ X i ∩ X j ⊆ X k ↔ U.master ∩ Yseq split X Δ i ∩ Yseq split X Δ j ⊆ Yseq split X Δ k := by
  have key := transfer_empty_iff split X Δ hΔ hsplit (cs := [(i, true), (j, true), (k, false)])
    (n := max i (max j k) + 1)
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
  have hRHS : {y ∈ U.master |
      ∀ p ∈ [(i, true), (j, true), (k, false)], (p.2 = true ↔ y ∈ Yseq split X Δ p.1)}
      = (U.master ∩ Yseq split X Δ i ∩ Yseq split X Δ j) \ Yseq split X Δ k := by
    ext y
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_diff, Set.mem_inter_iff]
    tauto
  rw [hLHS, hRHS] at key
  rw [← Set.diff_eq_empty, ← Set.diff_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

/-- `Yseq split X Δ n` is always a subset of `U.master`: it is a union of `atomU`-pieces at depth
`n+1`, each of which is `⊆ U.master` by `atomU_subset_master`. -/
theorem Yseq_subset_master (n : ℕ) : Yseq split X Δ n ⊆ U.master :=
  Set.iUnion_subset fun δ' => atomU_subset_master split X Δ hΔ hsplit (extendTrue δ') (n + 1)

/-- **`Yseq split X Δ 0 = U.master` whenever `X 0 = Δ`** (Scott's convention `X₀ = Δ`). Unfolding
one step of the recursion at `n = 0`, both `genAtom X Δ δ 0` and `atomU split X Δ δ 0` are `Δ` and
`U.master` *definitionally*, so splitting against `X 0 = Δ` puts everything into the `"+"`-branch
(the `"-"`-branch `Δ \ Δ = ∅` is forced empty by `split`'s spec), and `I ∪ J = U.master` with
`J = ∅` forces `I = U.master`. -/
theorem Yseq_zero_eq_master (h0 : X 0 = Δ) : Yseq split X Δ 0 = U.master := by
  set δ : ℕ → Bool := extendTrue (fun i : Fin 0 => i.elim0) with hδdef
  have hδ0 : δ 0 = true := by simp [hδdef, extendTrue]
  have hAB : genAtom X Δ δ 0 = ∅ ↔ atomU split X Δ δ 0 = ∅ :=
    ⟨fun h => absurd h hΔ.ne_empty, fun h => absurd h U.master_mem.2.1.ne_empty⟩
  have hBU : atomU split X Δ δ 0 = ∅ ∨ U.mem (atomU split X Δ δ 0) := Or.inr U.master_mem
  have hspec := hsplit hAB hBU (X 0)
  have hJ : (split (genAtom X Δ δ 0) (atomU split X Δ δ 0) (X 0)).2 = ∅ := by
    rw [← hspec.2.2.2.1]
    show genAtom X Δ δ 0 \ X 0 = ∅
    rw [show genAtom X Δ δ 0 = Δ from rfl, h0]
    exact Set.diff_self
  have hI : (split (genAtom X Δ δ 0) (atomU split X Δ δ 0) (X 0)).1 = U.master := by
    have hunion := hspec.2.2.2.2.1
    rw [hJ, Set.union_empty] at hunion
    exact hunion
  have hkey : atomU split X Δ δ 1 = U.master := by rw [atomU_succ, hδ0, if_pos rfl]; exact hI
  apply Set.Subset.antisymm (Yseq_subset_master split X Δ hΔ hsplit 0)
  calc U.master = atomU split X Δ δ 1 := hkey.symm
    _ ⊆ Yseq split X Δ 0 := subset_Yseq split X Δ (fun i : Fin 0 => i.elim0)

/-- **Equation transfer.** If `X k = X i ∩ X j` on `D`'s side (with all three sets `⊆ Δ`, as holds
automatically whenever they are genuine `D`-neighbourhoods), then `Y k = Y i ∩ Y j` on `U`'s side,
and conversely. This is assembled from `transfer_subset_iff` (twice, for `Xk ⊆ Xi`/`Xk ⊆ Xj`) and
`transfer_double_subset_iff` (once, for `Xi ∩ Xj ⊆ Xk`). -/
theorem transfer_inter_eq_iff (i j k : ℕ) (hi : X i ⊆ Δ) (_hj : X j ⊆ Δ) (hk : X k ⊆ Δ) :
    X i ∩ X j = X k ↔ Yseq split X Δ i ∩ Yseq split X Δ j = Yseq split X Δ k := by
  have h1 : X k ⊆ X i ↔ Yseq split X Δ k ⊆ Yseq split X Δ i := by
    have := transfer_subset_iff split X Δ hΔ hsplit k i
    rwa [Set.inter_eq_self_of_subset_right hk,
      Set.inter_eq_self_of_subset_right (Yseq_subset_master split X Δ hΔ hsplit k)] at this
  have h2 : X k ⊆ X j ↔ Yseq split X Δ k ⊆ Yseq split X Δ j := by
    have := transfer_subset_iff split X Δ hΔ hsplit k j
    rwa [Set.inter_eq_self_of_subset_right hk,
      Set.inter_eq_self_of_subset_right (Yseq_subset_master split X Δ hΔ hsplit k)] at this
  have h3 : X i ∩ X j ⊆ X k ↔ Yseq split X Δ i ∩ Yseq split X Δ j ⊆ Yseq split X Δ k := by
    have := transfer_double_subset_iff split X Δ hΔ hsplit i j k
    rwa [Set.inter_eq_self_of_subset_right hi,
      Set.inter_eq_self_of_subset_right (Yseq_subset_master split X Δ hΔ hsplit i)] at this
  constructor
  · intro heq
    have hki : X k ⊆ X i := heq ▸ Set.inter_subset_left
    have hkj : X k ⊆ X j := heq ▸ Set.inter_subset_right
    have hijk : X i ∩ X j ⊆ X k := heq ▸ subset_rfl
    exact Set.Subset.antisymm (h3.mp hijk) (Set.subset_inter (h1.mp hki) (h2.mp hkj))
  · intro heq
    have hki : Yseq split X Δ k ⊆ Yseq split X Δ i := heq ▸ Set.inter_subset_left
    have hkj : Yseq split X Δ k ⊆ Yseq split X Δ j := heq ▸ Set.inter_subset_right
    have hijk : Yseq split X Δ i ∩ Yseq split X Δ j ⊆ Yseq split X Δ k := heq ▸ subset_rfl
    exact Set.Subset.antisymm (h3.mpr hijk) (Set.subset_inter (h1.mpr hki) (h2.mpr hkj))

/-! ### `Yseq` is non-empty (and a genuine `U`-neighbourhood) whenever `X n` is non-empty -/

/-- `Yseq split X Δ n` is always either empty or a genuine `U`-neighbourhood: it is a finite union
(`Fin n → Bool`) of `atomU` pieces, each of which is `∅` or `U.mem` by `atomU_invariant`. -/
theorem Yseq_empty_or_mem (n : ℕ) : Yseq split X Δ n = ∅ ∨ U.mem (Yseq split X Δ n) := by
  by_cases hne : (Yseq split X Δ n).Nonempty
  · exact Or.inr (U_iUnion_mem
      (fun δ' => (atomU_invariant split X Δ hΔ hsplit (n + 1)).2.1 (extendTrue δ')) hne)
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hne)

/-- If `x ∈ X n` (and `x ∈ Δ`, automatic whenever `X n ⊆ Δ`), then `Yseq split X Δ n` is
non-empty: the canonical sign sequence `δ₀ k := decide (x ∈ X k)` produces a depth-`n` atom
containing `x` (hence non-empty), which `X n` (since `x ∈ X n`) splits into a non-empty
`"+"`-piece that is, by `split_fst_eq_inter_Yseq`, a subset of `Yseq split X Δ n`. -/
theorem Yseq_nonempty_of_mem {n : ℕ} {x : α} (hxΔ : x ∈ Δ) (hxn : x ∈ X n) :
    (Yseq split X Δ n).Nonempty := by
  classical
  set δ0 : ℕ → Bool := fun k => decide (x ∈ X k) with hδ0def
  have hδ0n : δ0 n = true := by show decide (x ∈ X n) = true; rw [decide_eq_true_iff]; exact hxn
  have hxA : x ∈ genAtom X Δ δ0 n := genAtom_self X Δ hxΔ n
  have hAX : x ∈ genAtom X Δ δ0 n ∩ X n := ⟨hxA, hxn⟩
  have hAne : (genAtom X Δ δ0 n ∩ X n).Nonempty := ⟨x, hAX⟩
  obtain ⟨hmatch, hmem, -⟩ := atomU_invariant split X Δ hΔ hsplit n
  have hspec := hsplit (hmatch δ0) (hmem δ0) (X n)
  have hIne : (split (genAtom X Δ δ0 n) (atomU split X Δ δ0 n) (X n)).1 ≠ ∅ :=
    fun h => hAne.ne_empty (hspec.2.2.1.mpr h)
  have hI_eq_atomU : (split (genAtom X Δ δ0 n) (atomU split X Δ δ0 n) (X n)).1 =
      atomU split X Δ δ0 (n + 1) := by rw [atomU_succ, hδ0n, if_pos rfl]
  set δ2 : ℕ → Bool := extendTrue (restrictFin δ0 n) with hδ2def
  have hagree : ∀ i < n + 1, δ2 i = δ0 i := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · exact extendTrue_restrictFin_agree δ0 n i hi'
    · simp [hδ2def, extendTrue, hδ0n]
  have hδ2_eq : atomU split X Δ δ2 (n + 1) = atomU split X Δ δ0 (n + 1) :=
    atomU_congr split X Δ hagree
  have hne2 : (atomU split X Δ δ2 (n + 1)).Nonempty := by
    rw [hδ2_eq, ← hI_eq_atomU]
    exact Set.nonempty_iff_ne_empty.mpr hIne
  exact hne2.mono (subset_Yseq split X Δ (restrictFin δ0 n))

end Scott1980.Neighborhood

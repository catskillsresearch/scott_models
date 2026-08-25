/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Exercise812c
import Scott1980.Neighborhood.Definition71
import Scott1980.Neighborhood.Definition72
import Scott1980.Neighborhood.Exercise718

/-!
# Exercise 8.12(d) (Scott 1981, PRG-19, Lecture VIII) — effective refinement of 8.12(c)

## 8.12(d)(1): generalizing the core recursion over an abstract split

`Exercise812c.lean`'s `xStep`/`yStep`/`atomPair` are all built directly on top of the
**classical** `splitChoice' D₁ hD₁nomin`/`splitChoice' D₀ hD₀nomin` (defined via `Classical.choice`
over `exists_split'`). To eventually get an *effective* isomorphism we need to re-run the exact same
construction with a **computable** split instead — so the first step is to generalize `xStep`/
`yStep`/`atomPair` (and its core invariant/disjointness/subset facts) over an *abstract* split
satisfying `SplitSpec'`, rather than one hardcoded to come from `NoMinimal` via choice.

This turns out to be a comparatively light abstraction, because `Exercise812c.lean`'s own generic
layer (`xyStep`, `xyStep_disjoint_of_ne`, `SplitSpec'`, `split_fst_subset'`, `split_snd_subset'`) is
**already** split-agnostic — the hardcoding to `splitChoice'` only happens at `xStep`/`yStep`
themselves (`Exercise812c.lean` lines 390/398). So this file's job is: redo *just* `xStep`/`yStep`
through `atomPair`'s subset/disjointness/master-subset facts (`Exercise812c.lean` lines 390–757)
with the `NoMinimal`-witnessed `splitChoice' Dᵢ hDᵢnomin` replaced by an arbitrary
`(splitX, hxSplit : SplitSpec' D₁ splitX)`/`(splitY, hySplit : SplitSpec' D₀ splitY)` pair — every
proof step transcribes essentially verbatim, replacing `splitChoice'_isSplitSpec Dᵢ hDᵢnomin`
(a *term*) with the hypothesis `hxSplit`/`hySplit` directly.

**Scope note (adjustment from the original `arxiv.md` scoping, discovered during execution):** the
original scoping listed `XPseq`/`YPseq`/`combinedX`/`combinedY`/`toD1`/`toD0`/`domainIso812c` as
also needing a parallel classical-abstract-split generalization in this sub-part. On closer
inspection this is unnecessary extra work: those are all downstream consequences of `atomPair`'s
invariant/disjointness/subset facts alone (never touching `splitX`/`splitY`/`hxSplit`/`hySplit`
directly), so `(d)(3)`–`(d)(6)` can build the *code-level* analogues (`atomPairCode`,
`XPseqCode`/`YPseqCode`, computability of `toD1`/`toD0`, final `EffectiveIso` assembly) directly on
top of `atomPairG` below, without first needing a redundant *classical* abstract-split replica of
the whole downstream chain. This keeps `(d)(1)` focused on the genuinely load-bearing recursive
core that every later sub-part depends on.

We also verify, as a sanity check that the abstraction is not vacuous and genuinely subsumes
`Exercise812c.lean`'s construction, that instantiating `splitX := splitChoice' D₁ hD₁nomin`/
`splitY := splitChoice' D₀ hD₀nomin` recovers `atomPair` exactly (`atomPairG_splitChoice_eq`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

/-! ### The two named sub-steps of `atomPair`, generalized over an abstract split

Direct analogues of `Exercise812c.lean`'s `xStep`/`yStep`, taking the split function itself as an
explicit argument instead of deriving it from a `NoMinimal` witness via `splitChoice'`. -/

section StepGen

variable {α β : Type*}

/-- **Generalized `xStep`**: split `D₁`'s side (via the abstract `splitX`) while directly refining
`D₀`'s side. Literally `xyStep splitX`; `xStep D₁ hD₁nomin = xStepG (splitChoice' D₁ hD₁nomin)`. -/
noncomputable def xStepG (splitX : Set α → Set β → Set α → Set β × Set β)
    (A : Set α) (B : Set β) (Xn : Set α) (b : Bool) : Set α × Set β :=
  xyStep splitX A B Xn b

/-- **Generalized `yStep`**: split `D₀`'s side (via the abstract `splitY`) while directly refining
`D₁`'s side. Literally `(xyStep splitY _ _ _ _).swap`; `yStep D₀ hD₀nomin = yStepG (splitChoice' D₀
hD₀nomin)`. -/
noncomputable def yStepG (splitY : Set β → Set α → Set β → Set α × Set α)
    (A1 : Set α) (B1 : Set β) (Yn : Set β) (b : Bool) : Set α × Set β :=
  (xyStep splitY B1 A1 Yn b).swap

theorem xStepG_fst_subset (splitX : Set α → Set β → Set α → Set β × Set β)
    (A : Set α) (B : Set β) (Xn : Set α) (b : Bool) : (xStepG splitX A B Xn b).1 ⊆ A := by
  by_cases hb : b = true
  · simp only [xStepG, xyStep, hb, if_true]; exact Set.inter_subset_left
  · simp only [xStepG, xyStep, hb]; exact Set.sdiff_subset

theorem xStepG_snd_subset {D₁ : NeighborhoodSystem β}
    {splitX : Set α → Set β → Set α → Set β × Set β} (hxSplit : SplitSpec' D₁ splitX)
    {A : Set α} {B : Set β} (hAB : A = ∅ ↔ B = ∅) (hBmem : B = ∅ ∨ D₁.mem B) (Xn : Set α)
    (b : Bool) : (xStepG splitX A B Xn b).2 ⊆ B := by
  have hspec := hxSplit hAB hBmem Xn
  by_cases hb : b = true
  · simp only [xStepG, xyStep, hb, if_true]; exact Set.subset_union_left.trans_eq hspec.2.2.2.2.1
  · simp only [xStepG, xyStep, hb]; exact Set.subset_union_right.trans_eq hspec.2.2.2.2.1

theorem yStepG_fst_subset {D₀ : NeighborhoodSystem α}
    {splitY : Set β → Set α → Set β → Set α × Set α} (hySplit : SplitSpec' D₀ splitY)
    {A1 : Set α} {B1 : Set β} (hBA : B1 = ∅ ↔ A1 = ∅) (hAmem : A1 = ∅ ∨ D₀.mem A1) (Yn : Set β)
    (b : Bool) : (yStepG splitY A1 B1 Yn b).1 ⊆ A1 := by
  have hspec := hySplit hBA hAmem Yn
  by_cases hb : b = true
  · simp only [yStepG, xyStep, Prod.swap, hb, if_true]
    exact Set.subset_union_left.trans_eq hspec.2.2.2.2.1
  · simp only [yStepG, xyStep, Prod.swap, hb]
    exact Set.subset_union_right.trans_eq hspec.2.2.2.2.1

theorem yStepG_snd_subset (splitY : Set β → Set α → Set β → Set α × Set α)
    (A1 : Set α) (B1 : Set β) (Yn : Set β) (b : Bool) : (yStepG splitY A1 B1 Yn b).2 ⊆ B1 := by
  by_cases hb : b = true
  · simp only [yStepG, xyStep, Prod.swap, hb, if_true]; exact Set.inter_subset_left
  · simp only [yStepG, xyStep, Prod.swap, hb]; exact Set.sdiff_subset

/-- **`xStepG`'s two direct-refine outputs reunion to exactly the parent**: the trivial two-set
identity `(A ∩ Xn) ∪ (A \ Xn) = A`, restated through `xStepG`'s `.1`. Needed for
**8.12(d)(4)(c)(i)**'s one-step 4-way reunion (the `b1`-level half of the argument); no `SplitSpec'`
hypotheses needed at all, unlike every other fact about `xStepG`/`yStepG` in this section. -/
theorem xStepG_fst_union (splitX : Set α → Set β → Set α → Set β × Set β)
    (A : Set α) (B : Set β) (Xn : Set α) :
    (xStepG splitX A B Xn true).1 ∪ (xStepG splitX A B Xn false).1 = A := by
  simp only [xStepG, xyStep]
  exact Set.inter_union_sdiff A Xn

/-- **`yStepG`'s two split-side outputs reunion to exactly the split's own input `A1`**: from
`SplitSpec'`'s unconditional `(split A B Xn).1 ∪ (split A B Xn).2 = B` field (here with `B := A1`,
`A := B1`, matching `yStepG`'s `.swap`-ed argument order). Needed for **8.12(d)(4)(c)(i)**'s
one-step 4-way reunion (the `b2`-level half). -/
theorem yStepG_fst_union {D₀ : NeighborhoodSystem α}
    {splitY : Set β → Set α → Set β → Set α × Set α} (hySplit : SplitSpec' D₀ splitY)
    {A1 : Set α} {B1 : Set β} (hBA : B1 = ∅ ↔ A1 = ∅) (hAmem : A1 = ∅ ∨ D₀.mem A1) (Yn : Set β) :
    (yStepG splitY A1 B1 Yn true).1 ∪ (yStepG splitY A1 B1 Yn false).1 = A1 := by
  have hspec := hySplit hBA hAmem Yn
  simp only [yStepG, xyStep, Prod.swap]
  exact hspec.2.2.2.2.1

/-- **`yStepG`'s two direct-refine outputs reunion to exactly its own input `B1`**: the trivial
two-set identity `(B1 ∩ Yn) ∪ (B1 \ Yn) = B1`, restated through `yStepG`'s `.2` (the `.swap`-ed
direct-refine side, on `D₁`'s side). Needed for **8.12(d)(4)(d)(i)**'s one-step 4-way reunion (the
`D₁`-side mirror of `xStepG_fst_union`'s `b1`-level half); no `SplitSpec'` hypotheses needed, exactly
like `xStepG_fst_union`. -/
theorem yStepG_snd_union (splitY : Set β → Set α → Set β → Set α × Set α)
    (A1 : Set α) (B1 : Set β) (Yn : Set β) :
    (yStepG splitY A1 B1 Yn true).2 ∪ (yStepG splitY A1 B1 Yn false).2 = B1 := by
  simp only [yStepG, xyStep, Prod.swap]
  exact Set.inter_union_sdiff B1 Yn

/-- **`xStepG`'s two split-side outputs reunion to exactly its own input `B`**: from `SplitSpec'`'s
unconditional `(split A B Xn).1 ∪ (split A B Xn).2 = B` field, applied directly (no `.swap`, unlike
`yStepG_fst_union`'s use of the same field). Needed for **8.12(d)(4)(d)(i)**'s one-step 4-way
reunion (the `D₁`-side mirror of `yStepG_fst_union`'s `b2`-level half). -/
theorem xStepG_snd_union {D₁ : NeighborhoodSystem β}
    {splitX : Set α → Set β → Set α → Set β × Set β} (hxSplit : SplitSpec' D₁ splitX)
    {A : Set α} {B : Set β} (hAB : A = ∅ ↔ B = ∅) (hBmem : B = ∅ ∨ D₁.mem B) (Xn : Set α) :
    (xStepG splitX A B Xn true).2 ∪ (xStepG splitX A B Xn false).2 = B := by
  have hspec := hxSplit hAB hBmem Xn
  simp only [xStepG, xyStep]
  exact hspec.2.2.2.2.1

theorem xStepG_disjoint_of_ne {D₁ : NeighborhoodSystem β}
    {splitX : Set α → Set β → Set α → Set β × Set β} (hxSplit : SplitSpec' D₁ splitX)
    {A : Set α} {B : Set β} (hAB : A = ∅ ↔ B = ∅) (hBmem : B = ∅ ∨ D₁.mem B) (Xn : Set α)
    {b b' : Bool} (hbb' : b ≠ b') :
    (xStepG splitX A B Xn b).1 ∩ (xStepG splitX A B Xn b').1 = ∅ ∧
      (xStepG splitX A B Xn b).2 ∩ (xStepG splitX A B Xn b').2 = ∅ :=
  xyStep_disjoint_of_ne hxSplit hAB hBmem Xn hbb'

theorem yStepG_disjoint_of_ne {D₀ : NeighborhoodSystem α}
    {splitY : Set β → Set α → Set β → Set α × Set α} (hySplit : SplitSpec' D₀ splitY)
    {A1 : Set α} {B1 : Set β} (hBA : B1 = ∅ ↔ A1 = ∅) (hAmem : A1 = ∅ ∨ D₀.mem A1) (Yn : Set β)
    {b b' : Bool} (hbb' : b ≠ b') :
    (yStepG splitY A1 B1 Yn b).1 ∩ (yStepG splitY A1 B1 Yn b').1 = ∅ ∧
      (yStepG splitY A1 B1 Yn b).2 ∩ (yStepG splitY A1 B1 Yn b').2 = ∅ := by
  have h := xyStep_disjoint_of_ne hySplit hBA hAmem Yn hbb'
  exact ⟨h.2, h.1⟩

end StepGen

/-! ### `atomPair`, generalized over an abstract split pair

Direct analogue of `Exercise812c.lean`'s `section AtomPair` (lines 552–757: the recursive
definition through `atomPair_fst_subset_master`/`atomPair_snd_subset_master`), with `hD₀nomin`/
`hD₁nomin` replaced throughout by `(splitY, hySplit)`/`(splitX, hxSplit)`. `NoMinimal` itself is no
longer needed anywhere in this generalized layer — only `SplitSpec'` is ever used. -/

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

/-- **Generalized `atomPair`**, taking the split functions directly instead of deriving them from
`NoMinimal` witnesses. -/
noncomputable def atomPairG (δ : ℕ → Bool × Bool) : ℕ → Set α × Set β
  | 0 => (D₀.master, D₁.master)
  | (n + 1) =>
      let A := (atomPairG δ n).1
      let B := (atomPairG δ n).2
      let IJ1 := splitX A B (X n)
      let A1 := if (δ n).1 then A ∩ X n else A \ X n
      let B1 := if (δ n).1 then IJ1.1 else IJ1.2
      let IJ2 := splitY B1 A1 (Y n)
      let B2 := if (δ n).2 then B1 ∩ Y n else B1 \ Y n
      let A2 := if (δ n).2 then IJ2.1 else IJ2.2
      (A2, B2)

theorem atomPairG_succ_eq (δ : ℕ → Bool × Bool) (n : ℕ) :
    atomPairG D₀ D₁ splitY splitX X Y δ (n + 1) =
      yStepG splitY
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).2
        (Y n) (δ n).2 := rfl

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

/-- **The core invariant, generalized.** Direct transcription of `atomPair_invariant`. -/
theorem atomPairG_invariant (δ : ℕ → Bool × Bool) :
    ∀ n, ((atomPairG D₀ D₁ splitY splitX X Y δ n).1 = ∅ ↔
        (atomPairG D₀ D₁ splitY splitX X Y δ n).2 = ∅) ∧
      ((atomPairG D₀ D₁ splitY splitX X Y δ n).1 = ∅ ∨
        D₀.mem (atomPairG D₀ D₁ splitY splitX X Y δ n).1) ∧
      ((atomPairG D₀ D₁ splitY splitX X Y δ n).2 = ∅ ∨
        D₁.mem (atomPairG D₀ D₁ splitY splitX X Y δ n).2) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, Or.inr D₀.master_mem, Or.inr D₁.master_mem⟩
    show (D₀.master = ∅ ↔ D₁.master = ∅)
    exact ⟨fun h => absurd h hD₀mne.ne_empty, fun h => absurd h hD₁mne.ne_empty⟩
  | succ n ih =>
    obtain ⟨ihAB, ihA, ihB⟩ := ih
    set A := (atomPairG D₀ D₁ splitY splitX X Y δ n).1 with hAdef
    set B := (atomPairG D₀ D₁ splitY splitX X Y δ n).2 with hBdef
    have hspec1 := hxSplit ihAB ihB (X n)
    set I1 := (splitX A B (X n)).1 with hI1def
    set J1 := (splitX A B (X n)).2 with hJ1def
    set A1 := (if (δ n).1 then A ∩ X n else A \ X n) with hA1def
    set B1 := (if (δ n).1 then I1 else J1) with hB1def
    have hA1B1 : A1 = ∅ ↔ B1 = ∅ := by
      by_cases hδ1 : (δ n).1 = true
      · simp only [hA1def, hB1def, hδ1, if_true]; exact hspec1.2.2.1
      · simp only [hA1def, hB1def, hδ1]; exact hspec1.2.2.2.1
    have hA1mem : A1 = ∅ ∨ D₀.mem A1 := by
      by_cases hδ1 : (δ n).1 = true
      · simp only [hA1def, hδ1, if_true]; exact inter_mem_or_empty hD₀pos ihA (hXmem n)
      · simp only [hA1def, hδ1]; exact diff_mem_or_empty hD₀diff ihA (hXmem n)
    have hB1mem : B1 = ∅ ∨ D₁.mem B1 := by
      by_cases hδ1 : (δ n).1 = true
      · simp only [hB1def, hδ1, if_true]; exact hspec1.1
      · simp only [hB1def, hδ1]; exact hspec1.2.1
    have hspec2 := hySplit hA1B1.symm hA1mem (Y n)
    set I2 := (splitY B1 A1 (Y n)).1 with hI2def
    set J2 := (splitY B1 A1 (Y n)).2 with hJ2def
    set B2 := (if (δ n).2 then B1 ∩ Y n else B1 \ Y n) with hB2def
    set A2 := (if (δ n).2 then I2 else J2) with hA2def
    have hB2A2 : B2 = ∅ ↔ A2 = ∅ := by
      by_cases hδ2 : (δ n).2 = true
      · simp only [hB2def, hA2def, hδ2, if_true]; exact hspec2.2.2.1
      · simp only [hB2def, hA2def, hδ2]; exact hspec2.2.2.2.1
    have hB2mem : B2 = ∅ ∨ D₁.mem B2 := by
      by_cases hδ2 : (δ n).2 = true
      · simp only [hB2def, hδ2, if_true]; exact inter_mem_or_empty hD₁pos hB1mem (hYmem n)
      · simp only [hB2def, hδ2]; exact diff_mem_or_empty hD₁diff hB1mem (hYmem n)
    have hA2mem : A2 = ∅ ∨ D₀.mem A2 := by
      by_cases hδ2 : (δ n).2 = true
      · simp only [hA2def, hδ2, if_true]; exact hspec2.1
      · simp only [hA2def, hδ2]; exact hspec2.2.1
    show (A2 = ∅ ↔ B2 = ∅) ∧ (A2 = ∅ ∨ D₀.mem A2) ∧ (B2 = ∅ ∨ D₁.mem B2)
    exact ⟨hB2A2.symm, hA2mem, hB2mem⟩

omit hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne in
/-- Extending/changing `δ` at or beyond position `n` does not change `atomPairG δ n`. -/
theorem atomPairG_congr {δ δ' : ℕ → Bool × Bool} {n : ℕ} (h : ∀ i < n, δ i = δ' i) :
    atomPairG D₀ D₁ splitY splitX X Y δ n = atomPairG D₀ D₁ splitY splitX X Y δ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev : atomPairG D₀ D₁ splitY splitX X Y δ n =
        atomPairG D₀ D₁ splitY splitX X Y δ' n := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hn : δ n = δ' n := h n (Nat.lt_succ_self n)
    show
      (let A := (atomPairG D₀ D₁ splitY splitX X Y δ n).1
       let B := (atomPairG D₀ D₁ splitY splitX X Y δ n).2
       let IJ1 := splitX A B (X n)
       let A1 := if (δ n).1 then A ∩ X n else A \ X n
       let B1 := if (δ n).1 then IJ1.1 else IJ1.2
       let IJ2 := splitY B1 A1 (Y n)
       let B2 := if (δ n).2 then B1 ∩ Y n else B1 \ Y n
       let A2 := if (δ n).2 then IJ2.1 else IJ2.2
       (A2, B2)) =
        (let A := (atomPairG D₀ D₁ splitY splitX X Y δ' n).1
         let B := (atomPairG D₀ D₁ splitY splitX X Y δ' n).2
         let IJ1 := splitX A B (X n)
         let A1 := if (δ' n).1 then A ∩ X n else A \ X n
         let B1 := if (δ' n).1 then IJ1.1 else IJ1.2
         let IJ2 := splitY B1 A1 (Y n)
         let B2 := if (δ' n).2 then B1 ∩ Y n else B1 \ Y n
         let A2 := if (δ' n).2 then IJ2.1 else IJ2.2
         (A2, B2))
    rw [hprev, hn]

/-- **`xStepG`'s output satisfies the preconditions `yStepG` needs**, generalizing `xStep_spec`. -/
theorem xStepG_spec (δ : ℕ → Bool × Bool) (n : ℕ) :
    ((xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
        (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).2 = ∅ ↔
      (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
        (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).1 = ∅) ∧
      ((xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).1 = ∅ ∨
        D₀.mem (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).1) := by
  obtain ⟨ihAB, ihA, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
  set A := (atomPairG D₀ D₁ splitY splitX X Y δ n).1 with hAdef
  set B := (atomPairG D₀ D₁ splitY splitX X Y δ n).2 with hBdef
  have hspec1 := hxSplit ihAB ihB (X n)
  refine ⟨?_, ?_⟩
  · by_cases hδ1 : (δ n).1 = true
    · simp only [xStepG, xyStep, hδ1, if_true]; exact hspec1.2.2.1.symm
    · simp only [xStepG, xyStep, hδ1]; exact hspec1.2.2.2.1.symm
  · by_cases hδ1 : (δ n).1 = true
    · simp only [xStepG, xyStep, hδ1, if_true]; exact inter_mem_or_empty hD₀pos ihA (hXmem n)
    · simp only [xStepG, xyStep, hδ1]; exact diff_mem_or_empty hD₀diff ihA (hXmem n)

/-- **`atomPairG`'s `α`-side only shrinks from depth `n` to `n + 1`.** -/
theorem atomPairG_fst_subset (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPairG D₀ D₁ splitY splitX X Y δ (n + 1)).1 ⊆
      (atomPairG D₀ D₁ splitY splitX X Y δ n).1 := by
  rw [atomPairG_succ_eq]
  obtain ⟨hspecAB, hspecAmem⟩ := xStepG_spec D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
  exact (yStepG_fst_subset hySplit hspecAB hspecAmem (Y n) (δ n).2).trans
    (xStepG_fst_subset splitX _ _ (X n) (δ n).1)

/-- **`atomPairG`'s `β`-side only shrinks from depth `n` to `n + 1`.** -/
theorem atomPairG_snd_subset (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPairG D₀ D₁ splitY splitX X Y δ (n + 1)).2 ⊆
      (atomPairG D₀ D₁ splitY splitX X Y δ n).2 := by
  rw [atomPairG_succ_eq]
  obtain ⟨ihAB, -, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
  exact (yStepG_snd_subset splitY _ _ (Y n) (δ n).2).trans
    (xStepG_snd_subset hxSplit ihAB ihB (X n) (δ n).1)

/-- **`atomPairG`'s `α`-side is always `⊆ D₀.master`.** -/
theorem atomPairG_fst_subset_master (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPairG D₀ D₁ splitY splitX X Y δ n).1 ⊆ D₀.master := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact (atomPairG_fst_subset D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
      splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n).trans ih

/-- **`atomPairG`'s `β`-side is always `⊆ D₁.master`**. -/
theorem atomPairG_snd_subset_master (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPairG D₀ D₁ splitY splitX X Y δ n).2 ⊆ D₁.master := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact (atomPairG_snd_subset D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
      splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n).trans ih

/-- **8.12(d)(4)(c)(i): the one-step 4-way classical reunion.** Ranging over all four
`(b1, b2) : Bool × Bool` sign choices at depth `n`, the resulting depth-`(n+1)` `D₀`-pieces
reunion to *exactly* the depth-`n` parent's `D₀`-piece — the algebraic core of the covering
argument closing `XPseqCode`'s deferred unconditional-"found" gap (`(d)(4)(c)`'s nested sub-goals).
Two facts chained: `xStepG_fst_union` at the `b1`-level (no hypotheses needed) and `yStepG_fst_union`
at the `b2`-level (needs `xStepG`'s output to satisfy `SplitSpec'`'s preconditions, supplied by the
same case analysis `xStepG_spec` already does, inlined here since `xStepG_spec` itself is hardcoded
to `(δ n).1` rather than a free `b1`). -/
theorem atomPairG_fst_union_step (δ : ℕ → Bool × Bool) (n : ℕ) :
    ((yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).2 (Y n) true).1 ∪
      (yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).2 (Y n) false).1) ∪
    ((yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).2 (Y n) true).1 ∪
      (yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).2 (Y n) false).1) =
      (atomPairG D₀ D₁ splitY splitX X Y δ n).1 := by
  obtain ⟨ihAB, ihA, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
  set A := (atomPairG D₀ D₁ splitY splitX X Y δ n).1 with hAdef
  set B := (atomPairG D₀ D₁ splitY splitX X Y δ n).2 with hBdef
  have hspec1 := hxSplit ihAB ihB (X n)
  have hBAtrue : (xStepG splitX A B (X n) true).2 = ∅ ↔ (xStepG splitX A B (X n) true).1 = ∅ := by
    simp only [xStepG, xyStep, if_true]; exact hspec1.2.2.1.symm
  have hAmemtrue : (xStepG splitX A B (X n) true).1 = ∅ ∨ D₀.mem (xStepG splitX A B (X n) true).1 := by
    simp only [xStepG, xyStep, if_true]; exact inter_mem_or_empty hD₀pos ihA (hXmem n)
  have hBAfalse : (xStepG splitX A B (X n) false).2 = ∅ ↔ (xStepG splitX A B (X n) false).1 = ∅ := by
    simp only [xStepG, xyStep]; exact hspec1.2.2.2.1.symm
  have hAmemfalse : (xStepG splitX A B (X n) false).1 = ∅ ∨ D₀.mem (xStepG splitX A B (X n) false).1 := by
    simp only [xStepG, xyStep]; exact diff_mem_or_empty hD₀diff ihA (hXmem n)
  rw [yStepG_fst_union hySplit hBAtrue hAmemtrue (Y n),
    yStepG_fst_union hySplit hBAfalse hAmemfalse (Y n)]
  exact xStepG_fst_union splitX A B (X n)

/-- **8.12(d)(4)(d)(i): the one-step 4-way classical reunion, `D₁`-side.** The `D₁`-side mirror of
`atomPairG_fst_union_step`: ranging over all four `(b1, b2) : Bool × Bool` sign choices at depth
`n`, the resulting depth-`(n+1)` `D₁`-pieces reunion to *exactly* the depth-`n` parent's `D₁`-piece.
Genuinely *simpler* to prove than the `D₀`-side version: here the *inner* (`b2`-level) collapse is
the hypothesis-free one (`yStepG_snd_union`, `D₁`'s side is `yStep`'s own direct-refine side) and
the *outer* (`b1`-level) collapse is the one needing `hxSplit` (`xStepG_snd_union`, `D₁`'s side is
`xStep`'s split side) — exactly the reverse pairing from the `D₀`-side proof, so no per-branch
`have`s (`hBAtrue`/`hAmemtrue`/etc.) are needed at all: `yStepG_snd_union` takes no `SplitSpec'`
hypotheses, so both inner collapses are immediate rewrites, leaving only the outer `xStepG_snd_union`
call. -/
theorem atomPairG_snd_union_step (δ : ℕ → Bool × Bool) (n : ℕ) :
    ((yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).2 (Y n) true).2 ∪
      (yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).2 (Y n) false).2) ∪
    ((yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).2 (Y n) true).2 ∪
      (yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).2 (Y n) false).2) =
      (atomPairG D₀ D₁ splitY splitX X Y δ n).2 := by
  obtain ⟨ihAB, ihA, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
  set A := (atomPairG D₀ D₁ splitY splitX X Y δ n).1 with hAdef
  set B := (atomPairG D₀ D₁ splitY splitX X Y δ n).2 with hBdef
  rw [yStepG_snd_union splitY (xStepG splitX A B (X n) true).1 (xStepG splitX A B (X n) true).2
      (Y n),
    yStepG_snd_union splitY (xStepG splitX A B (X n) false).1 (xStepG splitX A B (X n) false).2
      (Y n)]
  exact xStepG_snd_union hxSplit ihAB ihB (X n)

/-- **8.12(d)(4)(c)(ii): classical covering induction.** The classical `atomPairG` pieces at depth
`n`, ranged over all sign-histories `δ' : Fin n → Bool × Bool` (padded to `ℕ → Bool × Bool` via
`extendTruePair`), cover `D₀.master`. Induction on `n` chaining `atomPairG_fst_union_step` at every
step; base case `n = 0` is trivial (`atomPairG _ 0 = (D₀.master, D₁.master)`, one piece covering
itself). The successor step extends a covering history `δ'₀ : Fin n → Bool × Bool` for `z` by one
more `(b1, b2) : Bool × Bool` bit via the usual `Function.update`-based device (`extendTruePair
δ'₀` updated at `n`, then `restrictFinPair`'d back down to `Fin (n + 1) → Bool × Bool`; mirrors
`Exercise812c.lean`'s `xStep_spec_bit`/`yStep_fst_eq_inter_YPseq` proofs), picking whichever of the
four `atomPairG_fst_union_step` branches `z` actually landed in. -/
theorem atomPairG_master_covered (n : ℕ) :
    ∀ z ∈ D₀.master, ∃ δ' : Fin n → Bool × Bool,
      z ∈ (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ') n).1 := by
  induction n with
  | zero => exact fun z hz => ⟨Fin.elim0, hz⟩
  | succ n ih =>
    intro z hz
    obtain ⟨δ'₀, hδ'₀⟩ := ih z hz
    have hcover := atomPairG_fst_union_step D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
      splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne (extendTruePair δ'₀) n
    set A := (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ'₀) n).1 with hAdef
    set B := (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ'₀) n).2 with hBdef
    have step : ∀ b1 b2 : Bool,
        z ∈ (yStepG splitY (xStepG splitX A B (X n) b1).1 (xStepG splitX A B (X n) b1).2
          (Y n) b2).1 →
        ∃ δ' : Fin (n + 1) → Bool × Bool,
          z ∈ (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ') (n + 1)).1 := by
      intro b1 b2 hz'
      set δ'' := Function.update (extendTruePair δ'₀) n (b1, b2) with hδ''def
      refine ⟨restrictFinPair δ'' (n + 1), ?_⟩
      have hagree : ∀ i < n + 1, extendTruePair (restrictFinPair δ'' (n + 1)) i = δ'' i :=
        fun i hi => extendTruePair_restrictFinPair_agree δ'' (n + 1) i hi
      rw [atomPairG_congr D₀ D₁ splitY splitX X Y hagree, atomPairG_succ_eq]
      have hagreeN : ∀ i < n, δ'' i = extendTruePair δ'₀ i := by
        intro i hi
        simp [hδ''def, Function.update_of_ne (ne_of_lt hi)]
      have hbit : δ'' n = (b1, b2) := by simp [hδ''def]
      rw [atomPairG_congr D₀ D₁ splitY splitX X Y hagreeN, hbit]
      exact hz'
    rw [← hcover] at hδ'₀
    simp only [Set.mem_union] at hδ'₀
    rcases hδ'₀ with (h1 | h2) | (h3 | h4)
    · exact step true true h1
    · exact step true false h2
    · exact step false true h3
    · exact step false false h4

/-- **8.12(d)(4)(d)(ii): classical covering induction, `D₁`-side.** The `D₁`-side mirror of
`atomPairG_master_covered`: the classical `atomPairG` pieces at depth `n`, ranged over all
sign-histories `δ' : Fin n → Bool × Bool` (padded via `extendTruePair`), cover `D₁.master`. Verbatim
transcription of `atomPairG_master_covered`'s proof with `.1`→`.2`, `D₀.master`→`D₁.master`, and
`atomPairG_fst_union_step`→`atomPairG_snd_union_step`: induction on `n`, base case trivial
(`atomPairG _ 0 = (D₀.master, D₁.master)`), successor step extending a covering history by one more
`(b1, b2)` bit via the same `Function.update`/`restrictFinPair` device, picking whichever of the
four `atomPairG_snd_union_step` branches `z` landed in. -/
theorem atomPairG_master_covered_snd (n : ℕ) :
    ∀ z ∈ D₁.master, ∃ δ' : Fin n → Bool × Bool,
      z ∈ (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ') n).2 := by
  induction n with
  | zero => exact fun z hz => ⟨Fin.elim0, hz⟩
  | succ n ih =>
    intro z hz
    obtain ⟨δ'₀, hδ'₀⟩ := ih z hz
    have hcover := atomPairG_snd_union_step D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
      splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne (extendTruePair δ'₀) n
    set A := (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ'₀) n).1 with hAdef
    set B := (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ'₀) n).2 with hBdef
    have step : ∀ b1 b2 : Bool,
        z ∈ (yStepG splitY (xStepG splitX A B (X n) b1).1 (xStepG splitX A B (X n) b1).2
          (Y n) b2).2 →
        ∃ δ' : Fin (n + 1) → Bool × Bool,
          z ∈ (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ') (n + 1)).2 := by
      intro b1 b2 hz'
      set δ'' := Function.update (extendTruePair δ'₀) n (b1, b2) with hδ''def
      refine ⟨restrictFinPair δ'' (n + 1), ?_⟩
      have hagree : ∀ i < n + 1, extendTruePair (restrictFinPair δ'' (n + 1)) i = δ'' i :=
        fun i hi => extendTruePair_restrictFinPair_agree δ'' (n + 1) i hi
      rw [atomPairG_congr D₀ D₁ splitY splitX X Y hagree, atomPairG_succ_eq]
      have hagreeN : ∀ i < n, δ'' i = extendTruePair δ'₀ i := by
        intro i hi
        simp [hδ''def, Function.update_of_ne (ne_of_lt hi)]
      have hbit : δ'' n = (b1, b2) := by simp [hδ''def]
      rw [atomPairG_congr D₀ D₁ splitY splitX X Y hagreeN, hbit]
      exact hz'
    rw [← hcover] at hδ'₀
    simp only [Set.mem_union] at hδ'₀
    rcases hδ'₀ with (h1 | h2) | (h3 | h4)
    · exact step true true h1
    · exact step true false h2
    · exact step false true h3
    · exact step false false h4

/-- **Pairwise disjointness of `atomPairG` on both sides at once**, generalizing
`atomPair_disjoint`. -/
theorem atomPairG_disjoint (δ δ' : ℕ → Bool × Bool) :
    ∀ n, (∃ i < n, δ i ≠ δ' i) →
      (atomPairG D₀ D₁ splitY splitX X Y δ n).1 ∩
          (atomPairG D₀ D₁ splitY splitX X Y δ' n).1 = ∅ ∧
        (atomPairG D₀ D₁ splitY splitX X Y δ n).2 ∩
          (atomPairG D₀ D₁ splitY splitX X Y δ' n).2 = ∅ := by
  intro n
  induction n with
  | zero => rintro ⟨i, hi, -⟩; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    rintro ⟨i, hi, hine⟩
    by_cases hagree : ∀ j < n, δ j = δ' j
    · have hδn : δ n ≠ δ' n := by
        intro heq
        exact hine (by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact hagree i hi'
          · exact heq)
      have hpairEq : atomPairG D₀ D₁ splitY splitX X Y δ n =
          atomPairG D₀ D₁ splitY splitX X Y δ' n :=
        atomPairG_congr D₀ D₁ splitY splitX X Y hagree
      have hAB' : (atomPairG D₀ D₁ splitY splitX X Y δ' n).1 =
          (atomPairG D₀ D₁ splitY splitX X Y δ n).1 ∧
          (atomPairG D₀ D₁ splitY splitX X Y δ' n).2 =
            (atomPairG D₀ D₁ splitY splitX X Y δ n).2 :=
        ⟨(congrArg Prod.fst hpairEq).symm, (congrArg Prod.snd hpairEq).symm⟩
      by_cases h1 : (δ n).1 = (δ' n).1
      · have h2 : (δ n).2 ≠ (δ' n).2 := fun h2eq => hδn (Prod.ext_iff.mpr ⟨h1, h2eq⟩)
        rw [atomPairG_succ_eq, atomPairG_succ_eq, hAB'.1, hAB'.2, h1]
        obtain ⟨hspecAB, hspecAmem⟩ := xStepG_spec D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
          hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
        rw [h1] at hspecAB hspecAmem
        exact yStepG_disjoint_of_ne hySplit hspecAB hspecAmem (Y n) h2
      · obtain ⟨ihAB, ihA, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
          hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
        have hxdisj := xStepG_disjoint_of_ne hxSplit ihAB ihB (X n) h1
        obtain ⟨hspecAB, hspecAmem⟩ := xStepG_spec D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
          hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
        obtain ⟨hspecAB', hspecAmem'⟩ := xStepG_spec D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
          hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ' n
        have h1sub : (atomPairG D₀ D₁ splitY splitX X Y δ (n + 1)).1 ⊆
            (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
              (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).1 := by
          rw [atomPairG_succ_eq]; exact yStepG_fst_subset hySplit hspecAB hspecAmem (Y n) (δ n).2
        have h2sub : (atomPairG D₀ D₁ splitY splitX X Y δ (n + 1)).2 ⊆
            (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
              (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).2 := by
          rw [atomPairG_succ_eq]; exact yStepG_snd_subset splitY _ _ (Y n) (δ n).2
        have h1sub' : (atomPairG D₀ D₁ splitY splitX X Y δ' (n + 1)).1 ⊆
            (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ' n).1
              (atomPairG D₀ D₁ splitY splitX X Y δ' n).2 (X n) (δ' n).1).1 := by
          rw [atomPairG_succ_eq]; exact yStepG_fst_subset hySplit hspecAB' hspecAmem' (Y n) (δ' n).2
        have h2sub' : (atomPairG D₀ D₁ splitY splitX X Y δ' (n + 1)).2 ⊆
            (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ' n).1
              (atomPairG D₀ D₁ splitY splitX X Y δ' n).2 (X n) (δ' n).1).2 := by
          rw [atomPairG_succ_eq]; exact yStepG_snd_subset splitY _ _ (Y n) (δ' n).2
        rw [hAB'.1, hAB'.2] at h1sub' h2sub'
        exact ⟨Set.subset_eq_empty (Set.inter_subset_inter h1sub h1sub') hxdisj.1,
          Set.subset_eq_empty (Set.inter_subset_inter h2sub h2sub') hxdisj.2⟩
    · push Not at hagree
      obtain ⟨j, hj, hjne⟩ := hagree
      obtain ⟨hd1, hd2⟩ := ih ⟨j, hj, hjne⟩
      have h1 : (atomPairG D₀ D₁ splitY splitX X Y δ (n + 1)).1 ⊆
          (atomPairG D₀ D₁ splitY splitX X Y δ n).1 := atomPairG_fst_subset D₀ D₁ hD₀pos hD₀diff
        splitY hySplit hD₁pos hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
      have h1' : (atomPairG D₀ D₁ splitY splitX X Y δ' (n + 1)).1 ⊆
          (atomPairG D₀ D₁ splitY splitX X Y δ' n).1 := atomPairG_fst_subset D₀ D₁ hD₀pos hD₀diff
        splitY hySplit hD₁pos hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ' n
      have h2 : (atomPairG D₀ D₁ splitY splitX X Y δ (n + 1)).2 ⊆
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 := atomPairG_snd_subset D₀ D₁ hD₀pos hD₀diff
        splitY hySplit hD₁pos hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
      have h2' : (atomPairG D₀ D₁ splitY splitX X Y δ' (n + 1)).2 ⊆
          (atomPairG D₀ D₁ splitY splitX X Y δ' n).2 := atomPairG_snd_subset D₀ D₁ hD₀pos hD₀diff
        splitY hySplit hD₁pos hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ' n
      exact ⟨Set.subset_eq_empty (Set.inter_subset_inter h1 h1') hd1,
        Set.subset_eq_empty (Set.inter_subset_inter h2 h2') hd2⟩

end AtomPairGen

/-! ### Sanity check: instantiating with the classical split recovers `Exercise812c.lean`'s `atomPair`

Confirms the generalization is not vacuous: `atomPair` (from 8.12(c)) is exactly `atomPairG`
instantiated at `splitX := splitChoice' D₁ hD₁nomin`, `splitY := splitChoice' D₀ hD₀nomin`. -/

section Recover

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀nomin : D₀.NoMinimal) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β)

theorem atomPairG_splitChoice_eq (δ : ℕ → Bool × Bool) :
    ∀ n, atomPairG D₀ D₁ (splitChoice' D₀ hD₀nomin) (splitChoice' D₁ hD₁nomin) X Y δ n =
      atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show
      (let A := (atomPairG D₀ D₁ (splitChoice' D₀ hD₀nomin) (splitChoice' D₁ hD₁nomin) X Y δ n).1
       let B := (atomPairG D₀ D₁ (splitChoice' D₀ hD₀nomin) (splitChoice' D₁ hD₁nomin) X Y δ n).2
       let IJ1 := splitChoice' D₁ hD₁nomin A B (X n)
       let A1 := if (δ n).1 then A ∩ X n else A \ X n
       let B1 := if (δ n).1 then IJ1.1 else IJ1.2
       let IJ2 := splitChoice' D₀ hD₀nomin B1 A1 (Y n)
       let B2 := if (δ n).2 then B1 ∩ Y n else B1 \ Y n
       let A2 := if (δ n).2 then IJ2.1 else IJ2.2
       (A2, B2)) = atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ (n + 1)
    rw [atomPair_succ_eq]
    show
      (let A := (atomPairG D₀ D₁ (splitChoice' D₀ hD₀nomin) (splitChoice' D₁ hD₁nomin) X Y δ n).1
       let B := (atomPairG D₀ D₁ (splitChoice' D₀ hD₀nomin) (splitChoice' D₁ hD₁nomin) X Y δ n).2
       let IJ1 := splitChoice' D₁ hD₁nomin A B (X n)
       let A1 := if (δ n).1 then A ∩ X n else A \ X n
       let B1 := if (δ n).1 then IJ1.1 else IJ1.2
       let IJ2 := splitChoice' D₀ hD₀nomin B1 A1 (Y n)
       let B2 := if (δ n).2 then B1 ∩ Y n else B1 \ Y n
       let A2 := if (δ n).2 then IJ2.1 else IJ2.2
       (A2, B2)) =
        yStep D₀ hD₀nomin
          (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
            (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1
          (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
            (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).2
          (Y n) (δ n).2
    rw [ih]
    rfl

end Recover

/-! ## 8.12(d)(2): computable splits relative to two presentations

A split function `split : Set α → Set γ → Set α → Set γ × Set γ` is *computable relative to*
presentations `P` (of the `α`-side) and `Q` (of the `γ`-side) when both of its outputs are given by
a **primitive-recursive** function of the three input indices — mirroring `IsComputableMap`'s
"transport the semantic relation to the integer indices" idea (Definition 7.2), but for a genuine
*function* rather than a relation, so we ask for `Nat.Primrec` index functions with an exact
(rather than merely r.e.) correctness spec, matching `ComputablePresentation.inter`'s own shape
(a primitive-recursive intersection-index function, `inter_spec`).

This one structure serves **both** `splitX : Set α → Set β → Set α → Set β × Set β` (as
`IsComputableSplit P₀ P₁ splitX`) and `splitY : Set β → Set α → Set β → Set α × Set α` (as
`IsComputableSplit P₁ P₀ splitY`, roles swapped) — no separate `X`/`Y`-flavoured structure needed. -/

/-- **A split function is computable relative to two presentations** `P` (`α`-side), `Q` (`γ`-side)
when its two outputs are indexed by primitive-recursive functions of the three input indices
(indices of `A` in `P`, `B` in `Q`, `Xn` in `P`). Only the two index functions are data; primitive-
recursiveness and correctness (`posIdx_spec`/`negIdx_spec`) are `Prop`s, so this is choice-free. -/
structure IsComputableSplit {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
    (P : ComputablePresentation V) (Q : ComputablePresentation W)
    (split : Set α → Set γ → Set α → Set γ × Set γ) where
  /-- Index (in `Q`) of `(split (P.X n) (Q.X m) (P.X k)).1`, as a function of the three input
  indices `n, m, k`. -/
  posIdx : ℕ → ℕ → ℕ → ℕ
  /-- Index (in `Q`) of `(split (P.X n) (Q.X m) (P.X k)).2`. -/
  negIdx : ℕ → ℕ → ℕ → ℕ
  /-- `posIdx` is primitive recursive (on the `Nat.pair n (Nat.pair m k)` coding, matching
  `RecDecidable₃`'s convention). -/
  posIdx_primrec : Nat.Primrec (fun t => posIdx t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2)
  /-- `negIdx` is primitive recursive. -/
  negIdx_primrec : Nat.Primrec (fun t => negIdx t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2)
  /-- `posIdx n m k` genuinely indexes the split's first output **whenever that output is
  non-empty**. This is conditional (not `∀ n m k, … = Q.X (posIdx n m k)` outright) for a load-
  bearing reason found 2026-07-06 while repairing 8.12(g): `Q.X j` is *never* literally `∅` (every
  `ComputablePresentation` index is `Q.mem`-genuine, `Q.mem_X`), yet `SplitSpec'` (`Exercise812c.lean`)
  — the abstract correctness contract `atomPairG`'s classical layer needs `splitX`/`splitY` to
  satisfy — *requires* `(split A B Xn).1 = ∅` exactly when `A ∩ Xn = ∅`. An *unconditional*
  `posIdx_spec` is therefore jointly unsatisfiable with `SplitSpec'` for *any* split function
  whatsoever (not just a specific concrete one) — see `arxiv.md`'s 8.12(g) rows for the full
  argument. Weakening to "conditional on non-emptiness" is the fix: it costs nothing at any call
  site that already knows (from context, typically via `SplitSpec'`'s own emptiness ↔ clause) that
  the relevant output is non-empty — which is every existing use in this file — while making the
  structure satisfiable by a genuine `Set`-valued split whose output is sometimes literally `∅`. -/
  posIdx_spec : ∀ n m k, (split (P.X n) (Q.X m) (P.X k)).1 ≠ ∅ →
    (split (P.X n) (Q.X m) (P.X k)).1 = Q.X (posIdx n m k)
  /-- `negIdx n m k` genuinely indexes the split's second output whenever that output is
  non-empty. See `posIdx_spec`'s docstring for why this is conditional. -/
  negIdx_spec : ∀ n m k, (split (P.X n) (Q.X m) (P.X k)).2 ≠ ∅ →
    (split (P.X n) (Q.X m) (P.X k)).2 = Q.X (negIdx n m k)

namespace IsComputableSplit

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  {P : ComputablePresentation V} {Q : ComputablePresentation W}
  {split : Set α → Set γ → Set α → Set γ × Set γ}

/-- The split's first output is a genuine `W`-neighbourhood whenever it is non-empty (immediate
from `posIdx_spec` and `Q.mem_X`). Unlike the structure's original (unconditional) design, this is
now conditional on `(split …).1 ≠ ∅` — see `posIdx_spec`'s docstring. -/
theorem posIdx_mem (h : IsComputableSplit P Q split) (n m k : ℕ)
    (hne : (split (P.X n) (Q.X m) (P.X k)).1 ≠ ∅) :
    W.mem (split (P.X n) (Q.X m) (P.X k)).1 := by
  rw [h.posIdx_spec n m k hne]; exact Q.mem_X _

/-- The split's second output is a genuine `W`-neighbourhood whenever it is non-empty. -/
theorem negIdx_mem (h : IsComputableSplit P Q split) (n m k : ℕ)
    (hne : (split (P.X n) (Q.X m) (P.X k)).2 ≠ ∅) :
    W.mem (split (P.X n) (Q.X m) (P.X k)).2 := by
  rw [h.negIdx_spec n m k hne]; exact Q.mem_X _

end IsComputableSplit

/-! ## 8.12(d)(3)(a): `IsComputableDiff` — the missing "diff index" prerequisite

`ComputablePresentation` (Definition 7.1) only makes **intersection** effective (`inter`/
`inter_spec`, guarded by the consistency decider `cons_computable`). `atomPairG`'s recursion
(`xStepG`/`yStepG`) needs the *direct* refinement `A \ Xn` to stay effectively indexed at every
step too (the "split" sub-step is handled by `IsComputableSplit` above), and Definition 7.1 simply
has no such primitive for `\`. `IsComputableDiff` supplies exactly that, mirroring `inter`/
`inter_primrec`/`inter_spec`'s shape — with `cons_computable`'s role (deciding *consistency*,
i.e. whether the operation's output is a genuine neighbourhood) played here by `diff_computable`.

Both `IsComputableSplit`'s clause `A ∩ Xn = ∅ ↔ (split A B Xn).1 = ∅` (`SplitSpec'`) and
`NeighborhoodSystem.DiffClosed` (`X \ Y = ∅ ∨ D.mem (X \ Y)`, and no neighbourhood is `∅` under
`NoMinimal`) together mean "`X n \ X m` is a genuine neighbourhood" and "`X n \ X m` is non-empty"
coincide propositionally; `diff_computable` is phrased as the *existence* form (matching
`cons_computable`'s own phrasing) so it stays a direct structural mirror, but every later sub-part
is free to read it as an emptiness decider via that coincidence. One structure serves **both**
`P₀` and `P₁` symmetrically — no separate hypothesis needed per side. -/

/-- **`IsComputableDiff P`**: set-difference relative to the presentation `P` is computable — a
primitive-recursive `diffIdx : ℕ → ℕ → ℕ` indexing `X n \ X m` whenever that difference is a
genuine neighbourhood (`diffIdx_spec`, mirroring `inter_spec` exactly), together with a decider
for that very side-condition (`diff_computable`, mirroring `cons_computable`). Only `diffIdx` is
data; the rest are `Prop`s, so this stays choice-free to *state* (any particular instance may of
course need `Classical.choice` to *construct*, exactly like `inter`/`cons_computable` themselves
would for an arbitrary effectively-given system). -/
structure IsComputableDiff {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V) where
  /-- Index of `X n \ X m`, as a function of the two input indices. -/
  diffIdx : ℕ → ℕ → ℕ
  /-- `diffIdx` is primitive recursive (on the `Nat.pair` coding of `n, m`). -/
  diffIdx_primrec : Nat.Primrec (fun t => diffIdx t.unpair.1 t.unpair.2)
  /-- `diffIdx n m` genuinely indexes `X n \ X m` whenever that difference is (exactly) some
  `X k` — i.e. whenever it is a genuine neighbourhood. -/
  diffIdx_spec : ∀ {n m : ℕ}, (∃ k, P.X k = P.X n \ P.X m) → P.X (diffIdx n m) = P.X n \ P.X m
  /-- **7.1(i)-for-`\`**: "`X n \ X m` is a genuine neighbourhood" is recursively decidable in
  `n, m`, mirroring `cons_computable`'s role for `∩`. -/
  diff_computable : RecDecidable₂ (fun n m => ∃ k, P.X k = P.X n \ P.X m)

namespace IsComputableDiff

variable {α : Type*} {V : NeighborhoodSystem α} {P : ComputablePresentation V}

/-- **The emptiness/genuineness dichotomy**, transported through `DiffClosed` +
`NoMinimal.mem_ne_empty`: for a `DiffClosed`, `NoMinimal` system, "`X n \ X m` is a genuine
neighbourhood" and "`X n \ X m` is non-empty" are the *same* proposition — so `diff_computable`
may equally be read as an emptiness decider. Not needed to *state* `IsComputableDiff` (kept off
the structure itself, matching how `DiffClosed`/`NoMinimal` are separate hypotheses from
`ComputablePresentation` elsewhere in this file), but recorded here once for later sub-parts to
reuse directly instead of re-deriving. -/
theorem diff_exists_iff_ne_empty (hdiff : V.DiffClosed) (hnomin : V.NoMinimal) (n m : ℕ) :
    (∃ k, P.X k = P.X n \ P.X m) ↔ P.X n \ P.X m ≠ ∅ := by
  constructor
  · rintro ⟨k, hk⟩ hempty
    exact NoMinimal.mem_ne_empty hnomin (P.mem_X k) (hk.trans hempty)
  · intro hne
    rcases hdiff (P.mem_X n) (P.mem_X m) with hempty | hmem
    · exact absurd hempty hne
    · exact P.surj hmem

end IsComputableDiff

/-! ## 8.12(d)(3)(b): the `X`-sub-step's code-level state transition

`atomPairG`'s recursion state at depth `n` is a pair `(A_n, B_n) : Set α × Set β`. At the code
level we track it as a triple `(idx0, idx1, junk)`: `idx0`/`idx1` index `A_n`/`B_n` in `P₀`/`P₁`
(meaningful only when `junk = 0`), and `junk` is a **single shared** flag for "`A_n = B_n = ∅`
already". A single flag (rather than "one per side", as originally tentatively scoped) suffices
because `atomPairG_invariant`'s own `ihAB` clause (`(d)(1)`) already proves the two sides go empty
**together** at every depth — so a per-side flag would always just duplicate the other.

The `X`-sub-step (`xStepG`) refines `D₀`'s side **directly** (intersect/diff against `X n = P₀.X n`
— the presentation's own `n`-th neighbourhood; the eventual application enumerates *all* of `P₀`'s
neighbourhoods this way, mirroring `Theorem88d.lean`'s `idxSet (e P) n`) and `D₁`'s side via the
**split** (`(d)(2)`'s `IsComputableSplit`). This sub-part builds that half-step as a single
`Nat.Primrec` function of a packed `(n, bit, state)` argument; `(d)(3)(c)` composes it with the
symmetric `Y`-sub-step into the full `n → n + 1` transition. -/

/-! ### Direct-refinement decidability, extracted from `cons_computable`/`IsComputableDiff`

Two deciders, mirroring `Theorem88d.lean`'s `datomDec` extraction pattern (`Classical.choice` via
`RecDecidable`'s bare existential, then `isOne`-wrapped so the result is *literally* `{0,1}`-valued,
not just "`= 1` iff …"): whether `X n ∩ X m` (resp. `X n \ X m`) is empty. -/

section DirectDec

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)

/-- **Extracted existence decider for `∩`**: `1` iff `∃ k, X k ⊆ X n ∩ X m` (`cons_computable`'s
own predicate). -/
noncomputable def existsInterDec : ℕ → ℕ := fun t => isOne (P.cons_computable.choose t)

theorem primrec_existsInterDec : Nat.Primrec (existsInterDec P) :=
  (primrec_isOne.comp P.cons_computable.choose_spec.1).of_eq fun _ => rfl

theorem existsInterDec_le_one (t : ℕ) : existsInterDec P t ≤ 1 := isOne_le_one _

theorem existsInterDec_spec (n m : ℕ) :
    existsInterDec P (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m := by
  unfold existsInterDec
  rw [isOne_eq_one_iff]
  have h := P.cons_computable.choose_spec.2 (Nat.pair n m)
  dsimp only at h
  rw [unpair_pair_fst, unpair_pair_snd] at h
  exact h.symm

/-- **The `∩`-existence decider matches non-emptiness**, given `IsPositive` + `NoMinimal`: any
consistency witness is itself a non-empty neighbourhood (`NoMinimal.mem_ne_empty`), and conversely
a non-empty intersection is a neighbourhood by `IsPositive`, hence indexed by `surj`. -/
theorem existsInterDec_eq_zero_iff (hpos : V.IsPositive) (hnomin : V.NoMinimal) (n m : ℕ) :
    existsInterDec P (Nat.pair n m) = 0 ↔ P.X n ∩ P.X m = ∅ := by
  have hle := existsInterDec_le_one P (Nat.pair n m)
  constructor
  · intro h0
    by_contra hne
    have hmem : V.mem (P.X n ∩ P.X m) :=
      (hpos (P.mem_X n) (P.mem_X m)).mpr (Set.nonempty_iff_ne_empty.mpr hne)
    obtain ⟨k, hk⟩ := P.surj hmem
    have h1 : existsInterDec P (Nat.pair n m) = 1 :=
      (existsInterDec_spec P n m).mpr ⟨k, by rw [hk]⟩
    omega
  · intro hempty
    by_contra hne1
    have h1 : existsInterDec P (Nat.pair n m) = 1 := by omega
    obtain ⟨k, hk⟩ := (existsInterDec_spec P n m).mp h1
    exact absurd (Set.subset_eq_empty hk hempty) (hnomin.mem_ne_empty (P.mem_X k))

/-- **The `∩`-emptiness decider** (`1` iff `X n ∩ X m = ∅`): the complementary flag to
`existsInterDec`. -/
noncomputable def emptyInterDec : ℕ → ℕ := fun t => 1 - existsInterDec P t

theorem primrec_emptyInterDec : Nat.Primrec (emptyInterDec P) :=
  primrec_sub₂ (Nat.Primrec.const 1) (primrec_existsInterDec P)

theorem emptyInterDec_le_one (t : ℕ) : emptyInterDec P t ≤ 1 := by
  unfold emptyInterDec; have := existsInterDec_le_one P t; omega

theorem emptyInterDec_eq_one_iff (hpos : V.IsPositive) (hnomin : V.NoMinimal) (n m : ℕ) :
    emptyInterDec P (Nat.pair n m) = 1 ↔ P.X n ∩ P.X m = ∅ := by
  unfold emptyInterDec
  have hle := existsInterDec_le_one P (Nat.pair n m)
  have h0 := existsInterDec_eq_zero_iff P hpos hnomin n m
  constructor
  · intro h1; apply h0.mp; omega
  · intro hempty; have := h0.mpr hempty; omega

variable (hDiff : IsComputableDiff P)

/-- **Extracted existence decider for `\`**: `1` iff `∃ k, X k = X n \ X m`
(`IsComputableDiff.diff_computable`'s own predicate). -/
noncomputable def existsDiffDec : ℕ → ℕ := fun t => isOne (hDiff.diff_computable.choose t)

theorem primrec_existsDiffDec : Nat.Primrec (existsDiffDec P hDiff) :=
  (primrec_isOne.comp hDiff.diff_computable.choose_spec.1).of_eq fun _ => rfl

theorem existsDiffDec_le_one (t : ℕ) : existsDiffDec P hDiff t ≤ 1 := isOne_le_one _

theorem existsDiffDec_spec (n m : ℕ) :
    existsDiffDec P hDiff (Nat.pair n m) = 1 ↔ ∃ k, P.X k = P.X n \ P.X m := by
  unfold existsDiffDec
  rw [isOne_eq_one_iff]
  have h := hDiff.diff_computable.choose_spec.2 (Nat.pair n m)
  dsimp only at h
  rw [unpair_pair_fst, unpair_pair_snd] at h
  exact h.symm

/-- **The `\`-existence decider matches non-emptiness**, via `IsComputableDiff.diff_exists_iff_ne_empty`. -/
theorem existsDiffDec_eq_zero_iff (hdiff : V.DiffClosed) (hnomin : V.NoMinimal) (n m : ℕ) :
    existsDiffDec P hDiff (Nat.pair n m) = 0 ↔ P.X n \ P.X m = ∅ := by
  have hle := existsDiffDec_le_one P hDiff (Nat.pair n m)
  have h1 := existsDiffDec_spec P hDiff n m
  have h2 := IsComputableDiff.diff_exists_iff_ne_empty (P := P) hdiff hnomin n m
  constructor
  · intro h0
    by_contra hne
    have h1' : existsDiffDec P hDiff (Nat.pair n m) = 1 := h1.mpr (h2.mpr hne)
    omega
  · intro hempty
    by_contra hne0
    have h1' : existsDiffDec P hDiff (Nat.pair n m) = 1 := by omega
    exact (h2.mp (h1.mp h1')) hempty

/-- **The `\`-emptiness decider** (`1` iff `X n \ X m = ∅`). -/
noncomputable def emptyDiffDec : ℕ → ℕ := fun t => 1 - existsDiffDec P hDiff t

theorem primrec_emptyDiffDec : Nat.Primrec (emptyDiffDec P hDiff) :=
  primrec_sub₂ (Nat.Primrec.const 1) (primrec_existsDiffDec P hDiff)

theorem emptyDiffDec_le_one (t : ℕ) : emptyDiffDec P hDiff t ≤ 1 := by
  unfold emptyDiffDec; have := existsDiffDec_le_one P hDiff t; omega

theorem emptyDiffDec_eq_one_iff (hdiff : V.DiffClosed) (hnomin : V.NoMinimal) (n m : ℕ) :
    emptyDiffDec P hDiff (Nat.pair n m) = 1 ↔ P.X n \ P.X m = ∅ := by
  unfold emptyDiffDec
  have hle := existsDiffDec_le_one P hDiff (Nat.pair n m)
  have h0 := existsDiffDec_eq_zero_iff P hDiff hdiff hnomin n m
  constructor
  · intro h1; apply h0.mp; omega
  · intro hempty; have := h0.mpr hempty; omega

end DirectDec

/-! ### The two-sided packed state `(idx0, idx1, junk)` -/

/-- Pack a two-sided code state: `idx0` (`P₀`-index of `A_n`), `idx1` (`P₁`-index of `B_n`),
`junk` (`1` iff `A_n = B_n = ∅` already). -/
def packState2 (idx0 idx1 junk : ℕ) : ℕ := Nat.pair idx0 (Nat.pair idx1 junk)

def stateIdx0 (s : ℕ) : ℕ := s.unpair.1
def stateIdx1 (s : ℕ) : ℕ := s.unpair.2.unpair.1
def stateJunk (s : ℕ) : ℕ := s.unpair.2.unpair.2

@[simp] theorem stateIdx0_packState2 (a b c : ℕ) : stateIdx0 (packState2 a b c) = a := by
  unfold stateIdx0 packState2; simp only [unpair_pair_fst]
@[simp] theorem stateIdx1_packState2 (a b c : ℕ) : stateIdx1 (packState2 a b c) = b := by
  unfold stateIdx1 packState2; simp only [unpair_pair_fst, unpair_pair_snd]
@[simp] theorem stateJunk_packState2 (a b c : ℕ) : stateJunk (packState2 a b c) = c := by
  unfold stateJunk packState2; simp only [unpair_pair_snd]

theorem primrec_stateIdx0 : Nat.Primrec stateIdx0 := Nat.Primrec.left
theorem primrec_stateIdx1 : Nat.Primrec stateIdx1 := Nat.Primrec.left.comp Nat.Primrec.right
theorem primrec_stateJunk : Nat.Primrec stateJunk := Nat.Primrec.right.comp Nat.Primrec.right

/-- The base (depth-`0`) state: `A₀ = D₀.master`, `B₀ = D₁.master`, never junk. -/
def stateBase2 (masterIdx0 masterIdx1 : ℕ) : ℕ := packState2 masterIdx0 masterIdx1 0

/-! ### The `X`-sub-step

Packed-argument convention `w = pair n (pair b1 s)` (mirroring `Theorem88d.lean`'s `atomStep`
convention `w = pair k (pair y state)`): `n` is the current depth, `b1` is `(δ n).1` coded as
`0`/`1`, `s` is the incoming two-sided state. -/

section XSubStep

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)

def xwN (w : ℕ) : ℕ := w.unpair.1
def xwB1 (w : ℕ) : ℕ := w.unpair.2.unpair.1
def xwS (w : ℕ) : ℕ := w.unpair.2.unpair.2

theorem primrec_xwN : Nat.Primrec xwN := Nat.Primrec.left
theorem primrec_xwB1 : Nat.Primrec xwB1 := Nat.Primrec.left.comp Nat.Primrec.right
theorem primrec_xwS : Nat.Primrec xwS := Nat.Primrec.right.comp Nat.Primrec.right

/-- **The `X`-sub-step.** Refines `D₀`'s side (`idx0`) directly against `P₀.X n` (intersect if
`b1 = 1`, diff if `b1 = 0`, via `P₀.inter`/`hDiff0.diffIdx`), and `D₁`'s side (`idx1`) via the
matching branch of the split `hSplitX` — freezing both at the junk sentinel `0` the moment either
the incoming state was already junk, or this step's direct refinement is found empty. -/
noncomputable def xSubStep (w : ℕ) : ℕ :=
  let n := xwN w
  let b1 := xwB1 w
  let s := xwS w
  let idx0 := stateIdx0 s
  let idx1 := stateIdx1 s
  let junk := stateJunk s
  let directIdx := selectFn b1 (P₀.inter idx0 n) (hDiff0.diffIdx idx0 n)
  let directEmpty := selectFn b1 (emptyInterDec P₀ (Nat.pair idx0 n))
    (emptyDiffDec P₀ hDiff0 (Nat.pair idx0 n))
  let splitIdx := selectFn b1 (hSplitX.posIdx idx0 idx1 n) (hSplitX.negIdx idx0 idx1 n)
  let newJunk := selectFn junk 1 directEmpty
  packState2 (selectFn newJunk 0 directIdx) (selectFn newJunk 0 splitIdx) newJunk

theorem primrec_xSubStep : Nat.Primrec (xSubStep P₀ P₁ hDiff0 splitX hSplitX) := by
  have hn : Nat.Primrec xwN := primrec_xwN
  have hb1 : Nat.Primrec xwB1 := primrec_xwB1
  have hs : Nat.Primrec xwS := primrec_xwS
  have hidx0 : Nat.Primrec (fun w => stateIdx0 (xwS w)) := primrec_stateIdx0.comp hs
  have hidx1 : Nat.Primrec (fun w => stateIdx1 (xwS w)) := primrec_stateIdx1.comp hs
  have hjunk : Nat.Primrec (fun w => stateJunk (xwS w)) := primrec_stateJunk.comp hs
  have hinter : Nat.Primrec (fun w => P₀.inter (stateIdx0 (xwS w)) (xwN w)) :=
    (P₀.inter_primrec.comp (hidx0.pair hn)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hdiffidx : Nat.Primrec (fun w => hDiff0.diffIdx (stateIdx0 (xwS w)) (xwN w)) :=
    (hDiff0.diffIdx_primrec.comp (hidx0.pair hn)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hemptyInter : Nat.Primrec (fun w => emptyInterDec P₀ (Nat.pair (stateIdx0 (xwS w)) (xwN w))) :=
    (primrec_emptyInterDec P₀).comp (hidx0.pair hn)
  have hemptyDiff : Nat.Primrec
      (fun w => emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (xwS w)) (xwN w))) :=
    (primrec_emptyDiffDec P₀ hDiff0).comp (hidx0.pair hn)
  have hposIdx : Nat.Primrec
      (fun w => hSplitX.posIdx (stateIdx0 (xwS w)) (stateIdx1 (xwS w)) (xwN w)) :=
    (hSplitX.posIdx_primrec.comp (hidx0.pair (hidx1.pair hn))).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hnegIdx : Nat.Primrec
      (fun w => hSplitX.negIdx (stateIdx0 (xwS w)) (stateIdx1 (xwS w)) (xwN w)) :=
    (hSplitX.negIdx_primrec.comp (hidx0.pair (hidx1.pair hn))).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hdirectIdx : Nat.Primrec (fun w => selectFn (xwB1 w)
      (P₀.inter (stateIdx0 (xwS w)) (xwN w)) (hDiff0.diffIdx (stateIdx0 (xwS w)) (xwN w))) :=
    primrec_selectFn hb1 hinter hdiffidx
  have hdirectEmpty : Nat.Primrec (fun w => selectFn (xwB1 w)
      (emptyInterDec P₀ (Nat.pair (stateIdx0 (xwS w)) (xwN w)))
      (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (xwS w)) (xwN w)))) :=
    primrec_selectFn hb1 hemptyInter hemptyDiff
  have hsplitIdx : Nat.Primrec (fun w => selectFn (xwB1 w)
      (hSplitX.posIdx (stateIdx0 (xwS w)) (stateIdx1 (xwS w)) (xwN w))
      (hSplitX.negIdx (stateIdx0 (xwS w)) (stateIdx1 (xwS w)) (xwN w))) :=
    primrec_selectFn hb1 hposIdx hnegIdx
  have hnewJunk : Nat.Primrec (fun w => selectFn (stateJunk (xwS w)) 1 (selectFn (xwB1 w)
      (emptyInterDec P₀ (Nat.pair (stateIdx0 (xwS w)) (xwN w)))
      (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (xwS w)) (xwN w))))) :=
    primrec_selectFn hjunk (Nat.Primrec.const 1) hdirectEmpty
  have hidx0' : Nat.Primrec (fun w => selectFn (selectFn (stateJunk (xwS w)) 1 (selectFn (xwB1 w)
      (emptyInterDec P₀ (Nat.pair (stateIdx0 (xwS w)) (xwN w)))
      (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (xwS w)) (xwN w))))) 0
      (selectFn (xwB1 w) (P₀.inter (stateIdx0 (xwS w)) (xwN w))
        (hDiff0.diffIdx (stateIdx0 (xwS w)) (xwN w)))) :=
    primrec_selectFn hnewJunk (Nat.Primrec.const 0) hdirectIdx
  have hidx1' : Nat.Primrec (fun w => selectFn (selectFn (stateJunk (xwS w)) 1 (selectFn (xwB1 w)
      (emptyInterDec P₀ (Nat.pair (stateIdx0 (xwS w)) (xwN w)))
      (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (xwS w)) (xwN w))))) 0
      (selectFn (xwB1 w) (hSplitX.posIdx (stateIdx0 (xwS w)) (stateIdx1 (xwS w)) (xwN w))
        (hSplitX.negIdx (stateIdx0 (xwS w)) (stateIdx1 (xwS w)) (xwN w)))) :=
    primrec_selectFn hnewJunk (Nat.Primrec.const 0) hsplitIdx
  exact (hidx0'.pair (hidx1'.pair hnewJunk)).of_eq fun w => by
    unfold xSubStep packState2
    simp only []

end XSubStep

/-! ## 8.12(d)(3)(c): the `Y`-sub-step, composed into the full `atomPairCodeState`

`ySubStep` is symmetric to `xSubStep` (refines `D₁`'s index directly, `D₀`'s index via the split
`hSplitY`), using the *same* packed-argument convention (`xwN`/`xwB1`/`xwS`, reused unchanged since
they are pure `ℕ`-arithmetic, not tied to `X`). `atomPairStep` composes one `xSubStep` then one
`ySubStep` at the same depth `n`, and `atomPairCodeState` assembles the full recursion via
`Nat.Primrec.prec`, mirroring `Theorem88d.lean`'s `atomUCodeState`/`atomStep` exactly — including
reusing its `wY`/`wState` packed-argument projections for the *outer* `(bit-source, depth, state)`
wrapping. The bit-source `k` supplies **two** bits per depth (`(δ n).1`, `(δ n).2`), peeled via a
persistent `rem` field (divided by `4` each full step, mirroring `atomStep`'s `remK / 2`) carried
alongside the two-sided `packState2` triple in a fresh outer pairing, `packStateC`. -/

section YSubStep

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff1 : IsComputableDiff P₁)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

/-- **The `Y`-sub-step.** Symmetric to `xSubStep`: refines `D₁`'s side (`idx1`) directly against
`P₁.X n`, and `D₀`'s side (`idx0`) via the matching branch of the split `hSplitY`. Same packed
argument convention `w = pair n (pair b2 s)`. -/
noncomputable def ySubStep (w : ℕ) : ℕ :=
  let n := xwN w
  let b2 := xwB1 w
  let s := xwS w
  let idx0 := stateIdx0 s
  let idx1 := stateIdx1 s
  let junk := stateJunk s
  let directIdx := selectFn b2 (P₁.inter idx1 n) (hDiff1.diffIdx idx1 n)
  let directEmpty := selectFn b2 (emptyInterDec P₁ (Nat.pair idx1 n))
    (emptyDiffDec P₁ hDiff1 (Nat.pair idx1 n))
  let splitIdx := selectFn b2 (hSplitY.posIdx idx1 idx0 n) (hSplitY.negIdx idx1 idx0 n)
  let newJunk := selectFn junk 1 directEmpty
  packState2 (selectFn newJunk 0 splitIdx) (selectFn newJunk 0 directIdx) newJunk

theorem primrec_ySubStep : Nat.Primrec (ySubStep P₀ P₁ hDiff1 splitY hSplitY) := by
  have hn : Nat.Primrec xwN := primrec_xwN
  have hb2 : Nat.Primrec xwB1 := primrec_xwB1
  have hs : Nat.Primrec xwS := primrec_xwS
  have hidx0 : Nat.Primrec (fun w => stateIdx0 (xwS w)) := primrec_stateIdx0.comp hs
  have hidx1 : Nat.Primrec (fun w => stateIdx1 (xwS w)) := primrec_stateIdx1.comp hs
  have hjunk : Nat.Primrec (fun w => stateJunk (xwS w)) := primrec_stateJunk.comp hs
  have hinter : Nat.Primrec (fun w => P₁.inter (stateIdx1 (xwS w)) (xwN w)) :=
    (P₁.inter_primrec.comp (hidx1.pair hn)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hdiffidx : Nat.Primrec (fun w => hDiff1.diffIdx (stateIdx1 (xwS w)) (xwN w)) :=
    (hDiff1.diffIdx_primrec.comp (hidx1.pair hn)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hemptyInter : Nat.Primrec (fun w => emptyInterDec P₁ (Nat.pair (stateIdx1 (xwS w)) (xwN w))) :=
    (primrec_emptyInterDec P₁).comp (hidx1.pair hn)
  have hemptyDiff : Nat.Primrec
      (fun w => emptyDiffDec P₁ hDiff1 (Nat.pair (stateIdx1 (xwS w)) (xwN w))) :=
    (primrec_emptyDiffDec P₁ hDiff1).comp (hidx1.pair hn)
  have hposIdx : Nat.Primrec
      (fun w => hSplitY.posIdx (stateIdx1 (xwS w)) (stateIdx0 (xwS w)) (xwN w)) :=
    (hSplitY.posIdx_primrec.comp (hidx1.pair (hidx0.pair hn))).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hnegIdx : Nat.Primrec
      (fun w => hSplitY.negIdx (stateIdx1 (xwS w)) (stateIdx0 (xwS w)) (xwN w)) :=
    (hSplitY.negIdx_primrec.comp (hidx1.pair (hidx0.pair hn))).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hdirectIdx : Nat.Primrec (fun w => selectFn (xwB1 w)
      (P₁.inter (stateIdx1 (xwS w)) (xwN w)) (hDiff1.diffIdx (stateIdx1 (xwS w)) (xwN w))) :=
    primrec_selectFn hb2 hinter hdiffidx
  have hdirectEmpty : Nat.Primrec (fun w => selectFn (xwB1 w)
      (emptyInterDec P₁ (Nat.pair (stateIdx1 (xwS w)) (xwN w)))
      (emptyDiffDec P₁ hDiff1 (Nat.pair (stateIdx1 (xwS w)) (xwN w)))) :=
    primrec_selectFn hb2 hemptyInter hemptyDiff
  have hsplitIdx : Nat.Primrec (fun w => selectFn (xwB1 w)
      (hSplitY.posIdx (stateIdx1 (xwS w)) (stateIdx0 (xwS w)) (xwN w))
      (hSplitY.negIdx (stateIdx1 (xwS w)) (stateIdx0 (xwS w)) (xwN w))) :=
    primrec_selectFn hb2 hposIdx hnegIdx
  have hnewJunk : Nat.Primrec (fun w => selectFn (stateJunk (xwS w)) 1 (selectFn (xwB1 w)
      (emptyInterDec P₁ (Nat.pair (stateIdx1 (xwS w)) (xwN w)))
      (emptyDiffDec P₁ hDiff1 (Nat.pair (stateIdx1 (xwS w)) (xwN w))))) :=
    primrec_selectFn hjunk (Nat.Primrec.const 1) hdirectEmpty
  have hidx0' : Nat.Primrec (fun w => selectFn (selectFn (stateJunk (xwS w)) 1 (selectFn (xwB1 w)
      (emptyInterDec P₁ (Nat.pair (stateIdx1 (xwS w)) (xwN w)))
      (emptyDiffDec P₁ hDiff1 (Nat.pair (stateIdx1 (xwS w)) (xwN w))))) 0
      (selectFn (xwB1 w) (hSplitY.posIdx (stateIdx1 (xwS w)) (stateIdx0 (xwS w)) (xwN w))
        (hSplitY.negIdx (stateIdx1 (xwS w)) (stateIdx0 (xwS w)) (xwN w)))) :=
    primrec_selectFn hnewJunk (Nat.Primrec.const 0) hsplitIdx
  have hidx1' : Nat.Primrec (fun w => selectFn (selectFn (stateJunk (xwS w)) 1 (selectFn (xwB1 w)
      (emptyInterDec P₁ (Nat.pair (stateIdx1 (xwS w)) (xwN w)))
      (emptyDiffDec P₁ hDiff1 (Nat.pair (stateIdx1 (xwS w)) (xwN w))))) 0
      (selectFn (xwB1 w) (P₁.inter (stateIdx1 (xwS w)) (xwN w))
        (hDiff1.diffIdx (stateIdx1 (xwS w)) (xwN w)))) :=
    primrec_selectFn hnewJunk (Nat.Primrec.const 0) hdirectIdx
  exact (hidx0'.pair (hidx1'.pair hnewJunk)).of_eq fun w => by
    unfold ySubStep packState2
    simp only []

end YSubStep

/-! ### The outer `(bit-source, depth, state)` wrapping and the full recursion -/

/-- Pack the persistent bit-source remainder `rem` alongside the current two-sided
`packState2`-shaped inner state `s`. -/
def packStateC (rem s : ℕ) : ℕ := Nat.pair rem s

def stateRemC (t : ℕ) : ℕ := t.unpair.1
def stateInnerC (t : ℕ) : ℕ := t.unpair.2

@[simp] theorem stateRemC_packStateC (a b : ℕ) : stateRemC (packStateC a b) = a := by
  unfold stateRemC packStateC; simp only [unpair_pair_fst]
@[simp] theorem stateInnerC_packStateC (a b : ℕ) : stateInnerC (packStateC a b) = b := by
  unfold stateInnerC packStateC; simp only [unpair_pair_snd]

theorem primrec_stateRemC : Nat.Primrec stateRemC := Nat.Primrec.left
theorem primrec_stateInnerC : Nat.Primrec stateInnerC := Nat.Primrec.right

section AtomPairCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

/-- The initial state at depth `0`: `A₀ = D₀.master`, `B₀ = D₁.master` (never junk), bit-source
remainder `k` untouched. -/
def atomPairBase (k : ℕ) : ℕ := packStateC k (stateBase2 P₀.masterIdx P₁.masterIdx)

theorem primrec_atomPairBase : Nat.Primrec (atomPairBase P₀ P₁) :=
  (Nat.Primrec.id.pair (Nat.Primrec.const (stateBase2 P₀.masterIdx P₁.masterIdx))).of_eq
    fun k => by unfold atomPairBase packStateC; simp only [id_eq]

/-- Extract the depth `n` from the *outer* packed argument `w = pair k (pair n state)` (the
bit-source `k` itself is unused inside `atomPairStep`'s body — it is only threaded through by the
shape of `Nat.Primrec.prec`, exactly as `Theorem88d.lean`'s own `k` is unused inside `atomStep`). -/
def pcN (w : ℕ) : ℕ := xwB1 w
/-- Extract the current packed `(rem, s)` state from `w = pair k (pair n state)`. -/
def pcT (w : ℕ) : ℕ := xwS w

theorem primrec_pcN : Nat.Primrec pcN := primrec_xwB1
theorem primrec_pcT : Nat.Primrec pcT := primrec_xwS

/-- **The full per-depth step**: one `xSubStep` (bit `rem % 2`) followed by one `ySubStep` (bit
`(rem / 2) % 2`) at the same depth `n`, then peel both consumed bits from `rem` (`rem / 4`).
Packed-argument convention `w = pair k (pair n state)`, mirroring `Theorem88d.lean`'s `atomStep`
convention `w = pair k (pair y state)`. -/
noncomputable def atomPairStep (w : ℕ) : ℕ :=
  let n := pcN w
  let T := pcT w
  let rem := stateRemC T
  let s := stateInnerC T
  let b1 := rem % 2
  let b2 := (rem / 2) % 2
  let s1 := xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair b1 s))
  let s2 := ySubStep P₀ P₁ hDiff1 splitY hSplitY (Nat.pair n (Nat.pair b2 s1))
  packStateC (rem / 4) s2

theorem primrec_atomPairStep :
    Nat.Primrec (atomPairStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY) := by
  have hy : Nat.Primrec pcN := primrec_pcN
  have hst : Nat.Primrec pcT := primrec_pcT
  have hrem : Nat.Primrec (fun w => stateRemC (pcT w)) := primrec_stateRemC.comp hst
  have hs : Nat.Primrec (fun w => stateInnerC (pcT w)) := primrec_stateInnerC.comp hst
  have hb1 : Nat.Primrec (fun w => stateRemC (pcT w) % 2) := primrec_mod2.comp hrem
  have hb2 : Nat.Primrec (fun w => stateRemC (pcT w) / 2 % 2) :=
    primrec_mod2.comp (primrec_div2.comp hrem)
  have hw1 : Nat.Primrec (fun w => Nat.pair (pcN w) (Nat.pair (stateRemC (pcT w) % 2)
      (stateInnerC (pcT w)))) := hy.pair (hb1.pair hs)
  have hs1 : Nat.Primrec (fun w => xSubStep P₀ P₁ hDiff0 splitX hSplitX
      (Nat.pair (pcN w) (Nat.pair (stateRemC (pcT w) % 2) (stateInnerC (pcT w))))) :=
    (primrec_xSubStep P₀ P₁ hDiff0 splitX hSplitX).comp hw1
  have hw2 : Nat.Primrec (fun w => Nat.pair (pcN w) (Nat.pair (stateRemC (pcT w) / 2 % 2)
      (xSubStep P₀ P₁ hDiff0 splitX hSplitX
        (Nat.pair (pcN w) (Nat.pair (stateRemC (pcT w) % 2) (stateInnerC (pcT w))))))) :=
    hy.pair (hb2.pair hs1)
  have hs2 : Nat.Primrec (fun w => ySubStep P₀ P₁ hDiff1 splitY hSplitY
      (Nat.pair (pcN w) (Nat.pair (stateRemC (pcT w) / 2 % 2)
        (xSubStep P₀ P₁ hDiff0 splitX hSplitX
          (Nat.pair (pcN w) (Nat.pair (stateRemC (pcT w) % 2) (stateInnerC (pcT w)))))))) :=
    (primrec_ySubStep P₀ P₁ hDiff1 splitY hSplitY).comp hw2
  have hrem' : Nat.Primrec (fun w => stateRemC (pcT w) / 4) := by
    have : Nat.Primrec (fun w => stateRemC (pcT w) / 2 / 2) :=
      primrec_div2.comp (primrec_div2.comp hrem)
    exact this.of_eq fun w => by rw [Nat.div_div_eq_div_mul]
  exact (hrem'.pair hs2).of_eq fun w => by
    unfold atomPairStep packStateC
    simp only []

/-- **`atomPairCodeState`, the full recursion.** `atomPairCodeState (pair k n)` is the depth-`n`
packed state for bit-source `k` (whose bits `(k / 4ʸ) % 2`/`((k / 4ʸ) / 2) % 2` supply `(δ y).1`/
`(δ y).2` at every depth `y < n`) — mirroring `Theorem88d.lean`'s `atomUCodeState` exactly. -/
noncomputable def atomPairCodeState (t : ℕ) : ℕ :=
  t.unpair.2.rec (atomPairBase P₀ P₁ t.unpair.1) (fun y IH =>
    atomPairStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      (Nat.pair t.unpair.1 (Nat.pair y IH)))

theorem primrec_atomPairCodeState :
    Nat.Primrec (atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY) :=
  (Nat.Primrec.prec (primrec_atomPairBase P₀ P₁)
    (primrec_atomPairStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY)).of_eq fun _ => rfl

/-- **The depth-`n` `D₀`-side index**, for bit-source `k`. -/
noncomputable def atomPairIdx0 (n k : ℕ) : ℕ :=
  stateIdx0 (stateInnerC (atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    (Nat.pair k n)))

/-- **The depth-`n` `D₁`-side index**, for bit-source `k`. -/
noncomputable def atomPairIdx1 (n k : ℕ) : ℕ :=
  stateIdx1 (stateInnerC (atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    (Nat.pair k n)))

/-- **The depth-`n` shared junk flag**, for bit-source `k` (`1` iff both sides are already `∅`). -/
noncomputable def atomPairJunk (n k : ℕ) : ℕ :=
  stateJunk (stateInnerC (atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    (Nat.pair k n)))

theorem primrec_atomPairIdx0 : Nat.Primrec
    (fun t : ℕ => atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2) :=
  (primrec_stateIdx0.comp (primrec_stateInnerC.comp
    ((primrec_atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp
      (Nat.Primrec.right.pair Nat.Primrec.left)))).of_eq fun _ => rfl

theorem primrec_atomPairIdx1 : Nat.Primrec
    (fun t : ℕ => atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2) :=
  (primrec_stateIdx1.comp (primrec_stateInnerC.comp
    ((primrec_atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp
      (Nat.Primrec.right.pair Nat.Primrec.left)))).of_eq fun _ => rfl

theorem primrec_atomPairJunk : Nat.Primrec
    (fun t : ℕ => atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2) :=
  (primrec_stateJunk.comp (primrec_stateInnerC.comp
    ((primrec_atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp
      (Nat.Primrec.right.pair Nat.Primrec.left)))).of_eq fun _ => rfl

end AtomPairCode

/-! ## 8.12(d)(3)(d): per-step correctness against `atomPairG`

Whenever the recorded state at depth `n` is non-junk, `atomPairIdx0`/`atomPairIdx1`'s packed
indices literally index `atomPairG`'s depth-`n` component (instantiated at `X := P₀.X`, `Y :=
P₁.X`, `δ := deltaPair k`, the two-bits-per-depth sign sequence read off the bit-source `k`) — the
two-sided, code-level analogue of `Theorem88d.lean`'s `genAtom_atomUCode`. Unlike that single-sided
account (where `UX` is a *total* surjection and the code is always meaningful), here both sides'
codes are only meaningful when non-junk, so the statement is conditioned on `atomPairJunk = 0`
throughout. -/

/-- **The two-bits-per-depth sign sequence** read off a bit-source `k`, the `atomPairG`-shaped
analogue of `Theorem88d.lean`'s `deltaOf`: the depth-`i` nibble `(k / 4 ^ i) % 2` supplies `(δ i).1`,
and `(k / 4 ^ i / 2) % 2` supplies `(δ i).2` — matching exactly how `atomPairStep` peels two bits
per depth from `rem` (`rem % 2`, `(rem / 2) % 2`, then `rem / 4`). -/
def deltaPair (k : ℕ) : ℕ → Bool × Bool :=
  fun i => (decide ((k / 4 ^ i) % 2 = 1), decide ((k / 4 ^ i / 2) % 2 = 1))

theorem deltaPair_fst_eq_true_iff (k i : ℕ) : (deltaPair k i).1 = true ↔ (k / 4 ^ i) % 2 = 1 := by
  unfold deltaPair; simp

theorem deltaPair_snd_eq_true_iff (k i : ℕ) : (deltaPair k i).2 = true ↔ (k / 4 ^ i / 2) % 2 = 1 := by
  unfold deltaPair; simp

/-! ### `deltaPair` is `Nat.testBit` in disguise, two bits per depth

Mirrors `Theorem88d.lean`'s `deltaOf_eq_testBit` (`deltaOf k i = k.testBit i`), but reading *two*
`testBit`s per depth (`2 * i` for the `.1` component, `2 * i + 1` for `.2`) — the base-`4`/two-bit
analogue, needed below to reuse `Nat.eq_of_testBit_eq`/`Nat.testBit_lt_two_pow` verbatim for the
"distinct bounded bit-sources disagree somewhere" fact (`(d)(5)(b)`'s key combinatorial input,
avoiding a bespoke induction on `4 ^ n`). -/

theorem deltaPair_fst_eq_testBit (k i : ℕ) : (deltaPair k i).1 = k.testBit (2 * i) := by
  show decide ((k / 4 ^ i) % 2 = 1) = k.testBit (2 * i)
  rw [Nat.testBit_eq_decide_div_mod_eq, show (4 : ℕ) ^ i = 2 ^ (2 * i) by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]]

theorem deltaPair_snd_eq_testBit (k i : ℕ) : (deltaPair k i).2 = k.testBit (2 * i + 1) := by
  show decide ((k / 4 ^ i / 2) % 2 = 1) = k.testBit (2 * i + 1)
  rw [Nat.div_div_eq_div_mul, Nat.testBit_eq_decide_div_mod_eq, show (4 : ℕ) ^ i * 2 = 2 ^ (2 * i + 1)
    by rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, pow_succ]]

/-- **Distinctness of bounded bit-sources**: two bit-sources both `< 4 ^ n` and unequal must
disagree (via `deltaPair`) at some position strictly below `n`. Unlike `Theorem88d.lean`'s
`eq_of_deltaOf_agree_of_lt_two_pow` (which this directly mirrors), agreement of `deltaPair k`/
`deltaPair k'` on `[0, n)` means agreement of `k.testBit`/`k'.testBit` on *every* bit `< 2 * n` (both
the `2 * i` and `2 * i + 1` readings) — covering all of `testBit`'s bits below the bound `4 ^ n =
2 ^ (2 * n)`, so `Nat.eq_of_testBit_eq` still finishes in one step once every bit position is routed
through `deltaPair_fst_eq_testBit`/`deltaPair_snd_eq_testBit`. -/
theorem eq_of_deltaPair_agree_of_lt_four_pow {n k k' : ℕ} (hk : k < 4 ^ n) (hk' : k' < 4 ^ n)
    (hagree : ∀ i < n, deltaPair k i = deltaPair k' i) : k = k' := by
  apply Nat.eq_of_testBit_eq
  intro l
  rcases Nat.lt_or_ge l (2 * n) with hl | hl
  · rcases Nat.mod_two_eq_zero_or_one l with hmod | hmod
    · have hl2 : l = 2 * (l / 2) := by omega
      have hi : l / 2 < n := by omega
      have heq := congrArg Prod.fst (hagree (l / 2) hi)
      rw [deltaPair_fst_eq_testBit, deltaPair_fst_eq_testBit] at heq
      rwa [hl2]
    · have hl2 : l = 2 * (l / 2) + 1 := by omega
      have hi : l / 2 < n := by omega
      have heq := congrArg Prod.snd (hagree (l / 2) hi)
      rw [deltaPair_snd_eq_testBit, deltaPair_snd_eq_testBit] at heq
      rwa [hl2]
  · have h4n : (4 : ℕ) ^ n = 2 ^ (2 * n) := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
    have hile : (2 : ℕ) ^ (2 * n) ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl
    rw [Nat.testBit_lt_two_pow ((h4n ▸ hk).trans_le hile),
      Nat.testBit_lt_two_pow ((h4n ▸ hk').trans_le hile)]

/-- **Contrapositive form**: two distinct bit-sources both `< 4 ^ n` must disagree somewhere below
`n` — the form actually consumed by `(d)(5)(b)`'s I-formula lemmas (ruling out cross-terms from a
*different* bit-source witnessing the same point). -/
theorem exists_deltaPair_ne_of_lt_of_ne {n k k' : ℕ} (hk : k < 4 ^ n) (hk' : k' < 4 ^ n)
    (hne : k ≠ k') : ∃ i < n, deltaPair k i ≠ deltaPair k' i := by
  by_contra hcon
  push Not at hcon
  exact hne (eq_of_deltaPair_agree_of_lt_four_pow hk hk' hcon)

/-! ### `encodeDeltaPair`: realizing a prescribed finite `Bool × Bool` sign-prefix as a bit-source

**8.12(d)(4)(c)(iii).** The two-sided, base-`4` analogue of `Theorem88d.lean`'s `encodeBits`
(itself mirrored from `Theorem88a.lean`'s `Yidx_nonempty`-style existence device): given *any*
`δ : ℕ → Bool × Bool`, `encodeDeltaPair δ n` is a bit-source whose first `n` `deltaPair`-digits
match `δ`'s first `n` values exactly. Builds up one base-`4` digit (rather than one bit) per step,
packing `(δ n).1`/`(δ n).2` into that digit's two bits exactly as `atomPairStep` unpacks them
(`rem % 2`, `(rem / 2) % 2`). Purely a `Prop`-level existence tool, never claimed `Nat.Primrec` —
same status as `encodeBits`. -/

def encodeDeltaPair (δ : ℕ → Bool × Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => encodeDeltaPair δ n +
      ((if (δ n).1 then 1 else 0) + (if (δ n).2 then 2 else 0)) * 4 ^ n

theorem encodeDeltaPair_lt (δ : ℕ → Bool × Bool) : ∀ n, encodeDeltaPair δ n < 4 ^ n
  | 0 => by simp [encodeDeltaPair]
  | n + 1 => by
      have ih := encodeDeltaPair_lt δ n
      have h4 : (4 : ℕ) ^ (n + 1) = 4 ^ n * 4 := pow_succ 4 n
      show encodeDeltaPair δ n +
        ((if (δ n).1 then 1 else 0) + (if (δ n).2 then 2 else 0)) * 4 ^ n < 4 ^ (n + 1)
      rcases Bool.eq_false_or_eq_true (δ n).1 with h1 | h1 <;>
        rcases Bool.eq_false_or_eq_true (δ n).2 with h2 | h2 <;>
        simp only [h1, h2, if_true, if_false, Bool.false_eq_true] <;> omega

/-- Adding a higher digit (`d * 4 ^ n`, `n > i`) never disturbs a `deltaPair`-digit strictly
below `n`. The purely-arithmetic core making `encodeDeltaPair`'s induction go through. -/
private theorem digit_add_mul_pow_of_lt (m d i n : ℕ) (hi : i < n) :
    (m + d * 4 ^ n) / 4 ^ i % 4 = m / 4 ^ i % 4 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hi
  have heq : d * 4 ^ (i + j + 1) = 4 ^ i * (4 * 4 ^ j * d) := by ring
  rw [heq, Nat.add_mul_div_left m _ (pow_pos (by norm_num) i)]
  rw [show 4 * 4 ^ j * d = 4 * (4 ^ j * d) by ring]
  exact Nat.add_mul_mod_self_left _ _ _

/-- `encodeDeltaPair`'s freshly-added digit at position `n` is read straight back off by dividing
out the lower `4 ^ n` (which is exactly `encodeDeltaPair δ n`, `< 4 ^ n` by `encodeDeltaPair_lt`,
hence contributes `0` to the quotient). -/
private theorem digit_eq_of_encodeDeltaPair (δ : ℕ → Bool × Bool) (n : ℕ) :
    encodeDeltaPair δ (n + 1) / 4 ^ n =
      (if (δ n).1 then 1 else 0) + (if (δ n).2 then 2 else 0) := by
  show (encodeDeltaPair δ n +
      ((if (δ n).1 then 1 else 0) + (if (δ n).2 then 2 else 0)) * 4 ^ n) / 4 ^ n = _
  rw [Nat.add_mul_div_right _ _ (pow_pos (by norm_num) n),
    Nat.div_eq_of_lt (encodeDeltaPair_lt δ n), Nat.zero_add]

/-- **The inversion property**: `deltaPair (encodeDeltaPair δ n)` agrees with `δ` on every position
strictly below `n`. Combined with `atomPairG_congr` (`(d)(1)`, already `Pass`), this is exactly
what transports `(c)(ii)`'s `Fin n → Bool × Bool`-indexed classical covering fact into the
`deltaPair`/bit-source-indexed one `XPseqCode`'s fold actually uses (`atomPairG_master_covered_deltaPair`
below). -/
theorem deltaPair_encodeDeltaPair (δ : ℕ → Bool × Bool) :
    ∀ n i, i < n → deltaPair (encodeDeltaPair δ n) i = δ i := by
  intro n
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · show (decide ((encodeDeltaPair δ (n + 1) / 4 ^ i) % 2 = 1),
          decide ((encodeDeltaPair δ (n + 1) / 4 ^ i / 2) % 2 = 1)) = δ i
      have key : encodeDeltaPair δ (n + 1) / 4 ^ i % 4 = encodeDeltaPair δ n / 4 ^ i % 4 := by
        show (encodeDeltaPair δ n +
          ((if (δ n).1 then 1 else 0) + (if (δ n).2 then 2 else 0)) * 4 ^ n) / 4 ^ i % 4 = _
        exact digit_add_mul_pow_of_lt _ _ _ _ hi'
      have h1 : (encodeDeltaPair δ (n + 1) / 4 ^ i) % 2 =
          (encodeDeltaPair δ n / 4 ^ i) % 2 := by omega
      have h2 : (encodeDeltaPair δ (n + 1) / 4 ^ i / 2) % 2 =
          (encodeDeltaPair δ n / 4 ^ i / 2) % 2 := by omega
      rw [h1, h2]
      show (decide ((encodeDeltaPair δ n / 4 ^ i) % 2 = 1),
          decide ((encodeDeltaPair δ n / 4 ^ i / 2) % 2 = 1)) = δ i
      exact ih i hi'
    · have hd := digit_eq_of_encodeDeltaPair δ i
      show (decide ((encodeDeltaPair δ (i + 1) / 4 ^ i) % 2 = 1),
          decide ((encodeDeltaPair δ (i + 1) / 4 ^ i / 2) % 2 = 1)) = δ i
      rw [hd]
      rcases Bool.eq_false_or_eq_true (δ i).1 with h1 | h1 <;>
        rcases Bool.eq_false_or_eq_true (δ i).2 with h2 | h2 <;>
        simp [h1, h2, Prod.ext_iff]

section AtomPairGenDelta

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne in
/-- **8.12(d)(4)(c)(iii): transporting the covering fact to a `deltaPair`-indexed one.** Combines
`(c)(ii)`'s `atomPairG_master_covered` (covering by `Fin n → Bool × Bool` histories) with
`encodeDeltaPair`/`deltaPair_encodeDeltaPair` (realizing any such history, padded via
`extendTruePair`, as a genuine bit-source) and `atomPairG_congr` (depth-`n` value depends only on
history strictly below `n`) to land on exactly the indexing `XPseqCode`'s fold uses. -/
theorem atomPairG_master_covered_deltaPair (n : ℕ) :
    ∀ z ∈ D₀.master, ∃ i < 4 ^ n, z ∈ (atomPairG D₀ D₁ splitY splitX X Y (deltaPair i) n).1 := by
  intro z hz
  obtain ⟨δ', hδ'⟩ := atomPairG_master_covered D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne n z hz
  refine ⟨encodeDeltaPair (extendTruePair δ') n, encodeDeltaPair_lt _ n, ?_⟩
  rw [atomPairG_congr D₀ D₁ splitY splitX X Y
    (fun i hi => deltaPair_encodeDeltaPair (extendTruePair δ') n i hi)]
  exact hδ'

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne in
/-- **8.12(d)(4)(d)(iii): transporting the covering fact to a `deltaPair`-indexed one, `D₁`-side.**
The `D₁`-side mirror of `atomPairG_master_covered_deltaPair`: combines `(d)(ii)`'s
`atomPairG_master_covered_snd` (covering by `Fin n → Bool × Bool` histories) with
`encodeDeltaPair`/`deltaPair_encodeDeltaPair` (realizing any such history, padded via
`extendTruePair`, as a genuine bit-source) and `atomPairG_congr` to land on exactly the indexing
`YPseqCode`'s fold uses. Verbatim transcription of `atomPairG_master_covered_deltaPair`'s proof,
swapping `.1`→`.2`, `D₀.master`→`D₁.master`, `atomPairG_master_covered`→`atomPairG_master_covered_snd`
— no new base-4 encoding needed, since `encodeDeltaPair`/`deltaPair` are already symmetric in
`.1`/`.2`. -/
theorem atomPairG_master_covered_deltaPair_snd (n : ℕ) :
    ∀ z ∈ D₁.master, ∃ i < 4 ^ n, z ∈ (atomPairG D₀ D₁ splitY splitX X Y (deltaPair i) n).2 := by
  intro z hz
  obtain ⟨δ', hδ'⟩ := atomPairG_master_covered_snd D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
    hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne n z hz
  refine ⟨encodeDeltaPair (extendTruePair δ') n, encodeDeltaPair_lt _ n, ?_⟩
  rw [atomPairG_congr D₀ D₁ splitY splitX X Y
    (fun i hi => deltaPair_encodeDeltaPair (extendTruePair δ') n i hi)]
  exact hδ'

end AtomPairGenDelta

section AtomPairCorrect

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

/-- **Unfolding `atomPairCodeState` one step.** -/
theorem atomPairCodeState_succ (k n : ℕ) :
    atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY (Nat.pair k (n + 1)) =
      atomPairStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        (Nat.pair k (Nat.pair n (atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
          hSplitY (Nat.pair k n)))) := by
  unfold atomPairCodeState
  simp only [unpair_pair_fst, unpair_pair_snd]

/-- The unconsumed bit-source at depth `n` is exactly `k / 4 ^ n` (peeling two bits per depth). -/
theorem stateRemC_atomPairCodeState (k n : ℕ) :
    stateRemC (atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      (Nat.pair k n)) = k / 4 ^ n := by
  induction n with
  | zero => simp [atomPairCodeState, atomPairBase]
  | succ n ih =>
    rw [atomPairCodeState_succ]
    unfold atomPairStep pcN pcT xwB1 xwS
    simp only [unpair_pair_fst, unpair_pair_snd, stateRemC_packStateC, ih,
      Nat.div_div_eq_div_mul, ← pow_succ]

/-! ### Unconditional per-step algebra for `xSubStep`/`ySubStep`

Both sub-steps' code-level behaviour matches `xyStep` (hence `xStepG`/`yStepG`) **unconditionally**
in the incoming `junk` flag and the bit `b1`/`b2` — no `SplitSpec'`/`atomPairG_invariant`-style side
hypotheses needed at all: `IsComputableSplit`'s `posIdx_spec`/`negIdx_spec` are already unconditional
equalities, and the direct-refinement side only ever needs the corresponding emptiness-decider
readout to be `0`, which is connected to genuine set (in)equality unconditionally too (via
`existsInterDec_spec`/`existsDiffDec_spec` + `P.inter_spec`/`hDiff.diffIdx_spec`). -/

theorem xSubStep_junk_eq (s n b1 : ℕ) :
    stateJunk (xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair b1 s))) =
      selectFn (stateJunk s) 1 (selectFn b1 (emptyInterDec P₀ (Nat.pair (stateIdx0 s) n))
        (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 s) n))) := by
  unfold xSubStep
  simp only [xwN, xwB1, xwS, unpair_pair_fst, unpair_pair_snd, stateJunk_packState2]

theorem xSubStep_idx0_eq {s n b1 : ℕ}
    (h : selectFn (stateJunk s) 1 (selectFn b1 (emptyInterDec P₀ (Nat.pair (stateIdx0 s) n))
      (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 s) n))) = 0) :
    stateIdx0 (xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair b1 s))) =
      selectFn b1 (P₀.inter (stateIdx0 s) n) (hDiff0.diffIdx (stateIdx0 s) n) := by
  unfold xSubStep
  simp only [xwN, xwB1, xwS, unpair_pair_fst, unpair_pair_snd, stateIdx0_packState2, h,
    selectFn_zero]

theorem xSubStep_idx1_eq {s n b1 : ℕ}
    (h : selectFn (stateJunk s) 1 (selectFn b1 (emptyInterDec P₀ (Nat.pair (stateIdx0 s) n))
      (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 s) n))) = 0) :
    stateIdx1 (xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair b1 s))) =
      selectFn b1 (hSplitX.posIdx (stateIdx0 s) (stateIdx1 s) n)
        (hSplitX.negIdx (stateIdx0 s) (stateIdx1 s) n) := by
  unfold xSubStep
  simp only [xwN, xwB1, xwS, unpair_pair_fst, unpair_pair_snd, stateIdx1_packState2, h,
    selectFn_zero]

theorem ySubStep_junk_eq (s n b2 : ℕ) :
    stateJunk (ySubStep P₀ P₁ hDiff1 splitY hSplitY (Nat.pair n (Nat.pair b2 s))) =
      selectFn (stateJunk s) 1 (selectFn b2 (emptyInterDec P₁ (Nat.pair (stateIdx1 s) n))
        (emptyDiffDec P₁ hDiff1 (Nat.pair (stateIdx1 s) n))) := by
  unfold ySubStep
  simp only [xwN, xwB1, xwS, unpair_pair_fst, unpair_pair_snd, stateJunk_packState2]

theorem ySubStep_idx0_eq {s n b2 : ℕ}
    (h : selectFn (stateJunk s) 1 (selectFn b2 (emptyInterDec P₁ (Nat.pair (stateIdx1 s) n))
      (emptyDiffDec P₁ hDiff1 (Nat.pair (stateIdx1 s) n))) = 0) :
    stateIdx0 (ySubStep P₀ P₁ hDiff1 splitY hSplitY (Nat.pair n (Nat.pair b2 s))) =
      selectFn b2 (hSplitY.posIdx (stateIdx1 s) (stateIdx0 s) n)
        (hSplitY.negIdx (stateIdx1 s) (stateIdx0 s) n) := by
  unfold ySubStep
  simp only [xwN, xwB1, xwS, unpair_pair_fst, unpair_pair_snd, stateIdx0_packState2, h,
    selectFn_zero]

theorem ySubStep_idx1_eq {s n b2 : ℕ}
    (h : selectFn (stateJunk s) 1 (selectFn b2 (emptyInterDec P₁ (Nat.pair (stateIdx1 s) n))
      (emptyDiffDec P₁ hDiff1 (Nat.pair (stateIdx1 s) n))) = 0) :
    stateIdx1 (ySubStep P₀ P₁ hDiff1 splitY hSplitY (Nat.pair n (Nat.pair b2 s))) =
      selectFn b2 (P₁.inter (stateIdx1 s) n) (hDiff1.diffIdx (stateIdx1 s) n) := by
  unfold ySubStep
  simp only [xwN, xwB1, xwS, unpair_pair_fst, unpair_pair_snd, stateIdx1_packState2, h,
    selectFn_zero]

/-- If the outgoing `selectFn junk 1 X` reads `0`, the incoming `junk` was already `0` (a `1`
would force the result to `1` regardless of `X`, via `selectFn`'s definition). -/
theorem junk_eq_zero_of_selectFn_eq_zero {junk X : ℕ} (h : selectFn junk 1 X = 0) : junk = 0 := by
  rcases Nat.eq_zero_or_pos junk with h0 | h0
  · exact h0
  · exfalso; unfold selectFn at h; have : 1 ≤ junk := h0; nlinarith

/-- **`atomPairJunk` propagates**: once a bit-source's depth-`(n+1)` state is non-junk, its
depth-`n` state already was (the contrapositive of "junk is frozen forever", a one-step algebraic
fact needing no induction: `xSubStep`/`ySubStep` both force their *output* junk flag to `1`
whenever their *input* junk flag already was, via `selectFn junk 1 _`). -/
theorem atomPairJunk_eq_zero_of_succ {k n : ℕ}
    (h : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY (n + 1) k = 0) :
    atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 0 := by
  unfold atomPairJunk at h ⊢
  rw [atomPairCodeState_succ] at h
  unfold atomPairStep pcN pcT xwB1 xwS at h
  simp only [unpair_pair_fst, unpair_pair_snd, stateInnerC_packStateC] at h
  rw [ySubStep_junk_eq] at h
  have h1 := junk_eq_zero_of_selectFn_eq_zero h
  rw [xSubStep_junk_eq] at h1
  exact junk_eq_zero_of_selectFn_eq_zero h1

/-- `selectFn c 1 X = 0` forces **both** `c = 0` and `X = 0` (not just `c = 0`): with `c = 0`,
`selectFn` reduces to the "else" branch `X` outright. -/
theorem selectFn_one_eq_zero_iff {c X : ℕ} : selectFn c 1 X = 0 ↔ c = 0 ∧ X = 0 := by
  constructor
  · intro h
    have hc0 : c = 0 := junk_eq_zero_of_selectFn_eq_zero h
    subst hc0
    simpa [selectFn_zero] using h
  · rintro ⟨rfl, rfl⟩
    simp [selectFn_zero]

end AtomPairCorrect

/-- **Genuine `∩`-index equality**, given the emptiness decider reads `0`: the raw existence fact
(`existsInterDec_spec`) plugged straight into `Q.inter_spec` — unconditional, no `IsPositive`/
`NoMinimal` needed. -/
theorem interIdx_eq_of_empty_zero {γ : Type*} {W : NeighborhoodSystem γ} (Q : ComputablePresentation W)
    {idx0 n0 : ℕ} (h : emptyInterDec Q (Nat.pair idx0 n0) = 0) :
    Q.X (Q.inter idx0 n0) = Q.X idx0 ∩ Q.X n0 := by
  apply Q.inter_spec
  have hle := existsInterDec_le_one Q (Nat.pair idx0 n0)
  have h1 : existsInterDec Q (Nat.pair idx0 n0) = 1 := by unfold emptyInterDec at h; omega
  exact (existsInterDec_spec Q idx0 n0).mp h1

/-- **Genuine `\`-index equality**, given the emptiness decider reads `0`: the raw existence fact
(`existsDiffDec_spec`) plugged straight into `hDiff.diffIdx_spec` — unconditional. -/
theorem diffIdx_eq_of_empty_zero {γ : Type*} {W : NeighborhoodSystem γ} {Q : ComputablePresentation W}
    (hDiff : IsComputableDiff Q) {idx0 n0 : ℕ} (h : emptyDiffDec Q hDiff (Nat.pair idx0 n0) = 0) :
    Q.X (hDiff.diffIdx idx0 n0) = Q.X idx0 \ Q.X n0 := by
  apply hDiff.diffIdx_spec
  have hle := existsDiffDec_le_one Q hDiff (Nat.pair idx0 n0)
  have h1 : existsDiffDec Q hDiff (Nat.pair idx0 n0) = 1 := by unfold emptyDiffDec at h; omega
  exact (existsDiffDec_spec Q hDiff idx0 n0).mp h1

section AtomPairCorrect2

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀nomin hD₀diff hxSplit in
/-- **The `X`-sub-step matches `xStepG` exactly**, given the previous state's indices already match
`A`/`B` and the sub-step's output is non-junk. **No longer fully unconditional in `A`/`B`** (2026-
07-06, repairing 8.12(g)): now that `posIdx_spec`/`negIdx_spec` are conditional on non-emptiness,
deriving the split side needs `SplitSpec'`'s "empty iff empty" conjunct, which itself needs the
`atomPairG_invariant`-style precondition on `A`/`B` (`hAB`/`hBmem`) to fire. At every call site
these come straight from `atomPairG_invariant`/`xStepG_spec`. -/
theorem xSubStep_correct {s n : ℕ} {A : Set α} {B : Set β}
    (hA : P₀.X (stateIdx0 s) = A) (hB : P₁.X (stateIdx1 s) = B)
    (hAB : A = ∅ ↔ B = ∅) (hBmem : B = ∅ ∨ D₁.mem B) (b : Bool)
    (hnonjunk : stateJunk (xSubStep P₀ P₁ hDiff0 splitX hSplitX
        (Nat.pair n (Nat.pair (if b then 1 else 0) s))) = 0) :
    P₀.X (stateIdx0 (xSubStep P₀ P₁ hDiff0 splitX hSplitX
        (Nat.pair n (Nat.pair (if b then 1 else 0) s)))) = (xStepG splitX A B (P₀.X n) b).1 ∧
    P₁.X (stateIdx1 (xSubStep P₀ P₁ hDiff0 splitX hSplitX
        (Nat.pair n (Nat.pair (if b then 1 else 0) s)))) = (xStepG splitX A B (P₀.X n) b).2 := by
  have hspec1 := hxSplit hAB hBmem (P₀.X n)
  subst hA; subst hB
  by_cases hb : b = true
  · simp only [xStepG, xyStep, hb, if_true] at hnonjunk ⊢
    rw [xSubStep_junk_eq] at hnonjunk
    obtain ⟨-, hemp⟩ := selectFn_one_eq_zero_iff.mp hnonjunk
    rw [selectFn_one] at hemp
    have hemp' : P₀.X (stateIdx0 s) ∩ P₀.X n ≠ ∅ :=
      (emptyInterDec_eq_one_iff P₀ hD₀pos hD₀nomin (stateIdx0 s) n).not.mp (by omega)
    have hne : (splitX (P₀.X (stateIdx0 s)) (P₁.X (stateIdx1 s)) (P₀.X n)).1 ≠ ∅ :=
      hspec1.2.2.1.not.mp hemp'
    refine ⟨?_, ?_⟩
    · rw [xSubStep_idx0_eq (h := hnonjunk), selectFn_one]
      exact interIdx_eq_of_empty_zero P₀ hemp
    · rw [xSubStep_idx1_eq (h := hnonjunk), selectFn_one]
      exact (hSplitX.posIdx_spec (stateIdx0 s) (stateIdx1 s) n hne).symm
  · simp only [xStepG, xyStep, hb, Bool.false_eq_true, if_false] at hnonjunk ⊢
    rw [xSubStep_junk_eq] at hnonjunk
    obtain ⟨-, hemp⟩ := selectFn_one_eq_zero_iff.mp hnonjunk
    rw [selectFn_zero] at hemp
    have hemp' : P₀.X (stateIdx0 s) \ P₀.X n ≠ ∅ :=
      (emptyDiffDec_eq_one_iff P₀ hDiff0 hD₀diff hD₀nomin (stateIdx0 s) n).not.mp (by omega)
    have hne : (splitX (P₀.X (stateIdx0 s)) (P₁.X (stateIdx1 s)) (P₀.X n)).2 ≠ ∅ :=
      hspec1.2.2.2.1.not.mp hemp'
    refine ⟨?_, ?_⟩
    · rw [xSubStep_idx0_eq (h := hnonjunk), selectFn_zero]
      exact diffIdx_eq_of_empty_zero hDiff0 hemp
    · rw [xSubStep_idx1_eq (h := hnonjunk), selectFn_zero]
      exact (hSplitX.negIdx_spec (stateIdx0 s) (stateIdx1 s) n hne).symm

include hD₁pos hD₁nomin hD₁diff hySplit in
/-- **The `Y`-sub-step matches `yStepG` exactly**, symmetric to `xSubStep_correct`. -/
theorem ySubStep_correct {s n : ℕ} {A : Set α} {B : Set β}
    (hA : P₀.X (stateIdx0 s) = A) (hB : P₁.X (stateIdx1 s) = B)
    (hBA : B = ∅ ↔ A = ∅) (hAmem : A = ∅ ∨ D₀.mem A) (b : Bool)
    (hnonjunk : stateJunk (ySubStep P₀ P₁ hDiff1 splitY hSplitY
        (Nat.pair n (Nat.pair (if b then 1 else 0) s))) = 0) :
    P₀.X (stateIdx0 (ySubStep P₀ P₁ hDiff1 splitY hSplitY
        (Nat.pair n (Nat.pair (if b then 1 else 0) s)))) = (yStepG splitY A B (P₁.X n) b).1 ∧
    P₁.X (stateIdx1 (ySubStep P₀ P₁ hDiff1 splitY hSplitY
        (Nat.pair n (Nat.pair (if b then 1 else 0) s)))) = (yStepG splitY A B (P₁.X n) b).2 := by
  have hspec2 := hySplit hBA hAmem (P₁.X n)
  subst hA; subst hB
  by_cases hb : b = true
  · simp only [yStepG, xyStep, Prod.swap, hb, if_true] at hnonjunk ⊢
    rw [ySubStep_junk_eq] at hnonjunk
    obtain ⟨-, hemp⟩ := selectFn_one_eq_zero_iff.mp hnonjunk
    rw [selectFn_one] at hemp
    have hemp' : P₁.X (stateIdx1 s) ∩ P₁.X n ≠ ∅ :=
      (emptyInterDec_eq_one_iff P₁ hD₁pos hD₁nomin (stateIdx1 s) n).not.mp (by omega)
    have hne : (splitY (P₁.X (stateIdx1 s)) (P₀.X (stateIdx0 s)) (P₁.X n)).1 ≠ ∅ :=
      hspec2.2.2.1.not.mp hemp'
    refine ⟨?_, ?_⟩
    · rw [ySubStep_idx0_eq (h := hnonjunk), selectFn_one]
      exact (hSplitY.posIdx_spec (stateIdx1 s) (stateIdx0 s) n hne).symm
    · rw [ySubStep_idx1_eq (h := hnonjunk), selectFn_one]
      exact interIdx_eq_of_empty_zero P₁ hemp
  · simp only [yStepG, xyStep, Prod.swap, hb, Bool.false_eq_true, if_false] at hnonjunk ⊢
    rw [ySubStep_junk_eq] at hnonjunk
    obtain ⟨-, hemp⟩ := selectFn_one_eq_zero_iff.mp hnonjunk
    rw [selectFn_zero] at hemp
    have hemp' : P₁.X (stateIdx1 s) \ P₁.X n ≠ ∅ :=
      (emptyDiffDec_eq_one_iff P₁ hDiff1 hD₁diff hD₁nomin (stateIdx1 s) n).not.mp (by omega)
    have hne : (splitY (P₁.X (stateIdx1 s)) (P₀.X (stateIdx0 s)) (P₁.X n)).2 ≠ ∅ :=
      hspec2.2.2.2.1.not.mp hemp'
    refine ⟨?_, ?_⟩
    · rw [ySubStep_idx0_eq (h := hnonjunk), selectFn_zero]
      exact (hSplitY.negIdx_spec (stateIdx1 s) (stateIdx0 s) n hne).symm
    · rw [ySubStep_idx1_eq (h := hnonjunk), selectFn_zero]
      exact diffIdx_eq_of_empty_zero hDiff1 hemp

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
/-- **Per-step correctness against `atomPairG`** (the two-sided analogue of `Theorem88d.lean`'s
`genAtom_atomUCode`): whenever depth `n`'s recorded state (for bit-source `k`) is non-junk, its
packed `D₀`-side/`D₁`-side indices literally index `atomPairG`'s depth-`n` component,
instantiated at `X := P₀.X`, `Y := P₁.X`, `δ := deltaPair k`. -/
theorem atomPairCodeState_correct (k n : ℕ)
    (hjunk : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 0) :
    P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) =
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair k) n).1 ∧
      P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) =
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair k) n).2 := by
  induction n with
  | zero =>
    unfold atomPairIdx0 atomPairIdx1
    simp [atomPairCodeState, atomPairBase, stateBase2]
    exact ⟨P₀.masterIdx_spec, P₁.masterIdx_spec⟩
  | succ n ih =>
    have hjunk_n := atomPairJunk_eq_zero_of_succ (h := hjunk)
    obtain ⟨hidx0, hidx1⟩ := ih hjunk_n
    unfold atomPairJunk at hjunk
    unfold atomPairIdx0 at hidx0
    unfold atomPairIdx1 at hidx1
    unfold atomPairIdx0 atomPairIdx1
    rw [atomPairCodeState_succ] at hjunk ⊢
    unfold atomPairStep pcN pcT xwB1 xwS at hjunk ⊢
    simp only [unpair_pair_fst, unpair_pair_snd, stateInnerC_packStateC] at hjunk hidx0 hidx1 ⊢
    set T := atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY (Nat.pair k n)
      with hTdef
    have hrem : stateRemC T = k / 4 ^ n := stateRemC_atomPairCodeState P₀ P₁ hDiff0 hDiff1
      splitX hSplitX splitY hSplitY k n
    have hb1 : stateRemC T % 2 = if (deltaPair k n).1 then 1 else 0 := by
      rw [hrem]
      rcases Nat.mod_two_eq_zero_or_one (k / 4 ^ n) with h0 | h1
      · have hδ : (deltaPair k n).1 = false := by unfold deltaPair; simp [h0]
        simp [hδ, h0]
      · have hδ : (deltaPair k n).1 = true := by unfold deltaPair; simp [h1]
        simp [hδ, h1]
    have hb2 : stateRemC T / 2 % 2 = if (deltaPair k n).2 then 1 else 0 := by
      rw [hrem]
      rcases Nat.mod_two_eq_zero_or_one (k / 4 ^ n / 2) with h0 | h1
      · have hδ : (deltaPair k n).2 = false := by unfold deltaPair; simp [h0]
        simp [hδ, h0]
      · have hδ : (deltaPair k n).2 = true := by unfold deltaPair; simp [h1]
        simp [hδ, h1]
    rw [hb1] at hjunk ⊢
    rw [hb2] at hjunk ⊢
    have hxjunk : stateJunk (xSubStep P₀ P₁ hDiff0 splitX hSplitX
        (Nat.pair n (Nat.pair (if (deltaPair k n).1 then 1 else 0) (stateInnerC T)))) = 0 := by
      have hj2 := hjunk
      rw [ySubStep_junk_eq] at hj2
      exact junk_eq_zero_of_selectFn_eq_zero hj2
    obtain ⟨hAB, -, hBmem⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
      splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair k) n
    obtain ⟨hx0, hx1⟩ := xSubStep_correct P₀ P₁ hDiff0 splitX hSplitX hD₀pos hD₀diff hD₀nomin
      hxSplit hidx0 hidx1 hAB hBmem (deltaPair k n).1 hxjunk
    have hxspec := xStepG_spec D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff splitX hxSplit
      P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair k) n
    rw [atomPairG_succ_eq]
    exact ySubStep_correct P₀ P₁ hDiff1 splitY hSplitY hD₁pos hD₁diff hD₁nomin hySplit hx0 hx1
      hxspec.1 hxspec.2 (deltaPair k n).2 hjunk

/-! ## 8.12(d)(3)(e): the junk invariant and validity

Mirrors `Theorem88d.lean`'s `atomUEmpty_mono`/`atomUCode_mem`. -/

/-- **`selectFn` of two `{0,1}`-bounded values, gated by a `{0,1}`-bounded flag, is itself
`{0,1}`-bounded** — `selectFn c a b` is literally `a` or `b` once `c ≤ 1`, so this is immediate by
splitting on `c`. -/
theorem selectFn_le_one {c a b : ℕ} (hc : c ≤ 1) (ha : a ≤ 1) (hb : b ≤ 1) :
    selectFn c a b ≤ 1 := by
  rcases (show c = 0 ∨ c = 1 from by omega) with h | h <;> rw [h]
  · rw [selectFn_zero]; exact hb
  · rw [selectFn_one]; exact ha

/-- **`atomPairJunk` is always `0` or `1`** (never any other natural number), by induction through
the nested `selectFn`s: the base case is the literal `0` of `stateBase2`, and each step is a chain
of `selectFn_le_one` applications — the outer flag bounded by the outer induction hypothesis, the
inner emptiness deciders bounded by `emptyInterDec_le_one`/`emptyDiffDec_le_one`. -/
theorem atomPairJunk_le_one (k n : ℕ) :
    atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k ≤ 1 := by
  induction n with
  | zero => simp [atomPairJunk, atomPairCodeState, atomPairBase, stateBase2]
  | succ n ih =>
    unfold atomPairJunk at ih ⊢
    rw [atomPairCodeState_succ]
    unfold atomPairStep pcN pcT xwB1 xwS
    simp only [unpair_pair_fst, unpair_pair_snd, stateInnerC_packStateC]
    set T := atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY (Nat.pair k n)
    rw [ySubStep_junk_eq, xSubStep_junk_eq]
    have hb1 : stateRemC T % 2 ≤ 1 := Nat.le_of_lt_succ (by omega)
    have hb2 : stateRemC T / 2 % 2 ≤ 1 := Nat.le_of_lt_succ (by omega)
    exact selectFn_le_one
      (selectFn_le_one ih (le_refl 1)
        (selectFn_le_one hb1 (emptyInterDec_le_one P₀ _) (emptyDiffDec_le_one P₀ hDiff0 _)))
      (le_refl 1)
      (selectFn_le_one hb2 (emptyInterDec_le_one P₁ _) (emptyDiffDec_le_one P₁ hDiff1 _))

/-- **Junk propagates forward** (once a bit-source's state is junk at depth `n`, it stays junk at
every later depth): the contrapositive of `atomPairJunk_eq_zero_of_succ`, using
`atomPairJunk_le_one` to convert "`≠ 0`" into "`= 1`" on both sides. -/
theorem atomPairJunk_mono {n k : ℕ}
    (h : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 1) :
    atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY (n + 1) k = 1 := by
  have hle := atomPairJunk_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY k (n + 1)
  by_contra hne
  have h0 : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY (n + 1) k = 0 := by
    omega
  have := atomPairJunk_eq_zero_of_succ (h := h0)
  omega

/-- **Validity**: `atomPairIdx0`/`atomPairIdx1`'s recorded indices are always genuine `D₀`-side/
`D₁`-side neighbourhoods — junk or not — since `ComputablePresentation.mem_X` holds unconditionally
for every index (mirroring `Theorem88d.lean`'s `atomUCode_mem`/`U_mem_UX`, itself unconditional for
the same reason). -/
theorem atomPairIdx0_mem (n k : ℕ) :
    D₀.mem (P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k)) :=
  P₀.mem_X _

theorem atomPairIdx1_mem (n k : ℕ) :
    D₁.mem (P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k)) :=
  P₁.mem_X _

end AtomPairCorrect2

/-! ## 8.12(d)(3)(f): disjointness across disagreeing, non-junk sign-sequences

Mirrors `Theorem88d.lean`'s `atomUCode_disjoint`. Completes 8.12(d)(3). Unlike `atomUCode_disjoint`
(which reproves disjointness by induction at the code level, since `Theorem88d.lean`'s `U`/`D`
account has no free-standing `Set`-level disjointness fact to transfer from), here the *entire*
mathematical content is already `atomPairG_disjoint` from `(d)(1)` — this sub-part is purely a
transfer along `(d)(3)(d)`'s `atomPairCodeState_correct`, so needs `(d)(1)`'s full hypothesis list
(`SplitSpec'` for `splitX`/`splitY`, `IsPositive`/`DiffClosed`/`Nonempty` for `D₀`/`D₁`) in addition
to `(d)(3)`'s own computability hypotheses. -/

section AtomPairCorrect3

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
/-- **Disjointness at the code level**: two bit-sources `k`/`k'` disagreeing (via `deltaPair`)
somewhere below depth `n`, with *both* recorded states still non-junk at `n`, index disjoint sets
on both the `D₀`-side and the `D₁`-side. Immediate from `atomPairCodeState_correct` (rewriting both
sides' indexed sets as `atomPairG` components) plus `atomPairG_disjoint` (from `(d)(1)`). -/
theorem atomPairCodeState_disjoint {n k k' : ℕ}
    (hk : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 0)
    (hk' : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k' = 0)
    (hne : ∃ i < n, deltaPair k i ≠ deltaPair k' i) :
    P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) ∩
        P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k') = ∅ ∧
      P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) ∩
        P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k') = ∅ := by
  obtain ⟨h0, h1⟩ := atomPairCodeState_correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne k n hk
  obtain ⟨h0', h1'⟩ := atomPairCodeState_correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne k' n hk'
  rw [h0, h0', h1, h1']
  exact atomPairG_disjoint D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff splitX hxSplit
    P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair k) (deltaPair k') n hne

end AtomPairCorrect3

/-! ## 8.12(d)(4)(a): `IsComputableUnion` — the missing "union index" prerequisite

`ComputablePresentation` (Definition 7.1) only makes **intersection** effective (`inter`/
`inter_spec`, guarded by `cons_computable`), because `NeighborhoodSystem.inter_mem` makes
intersection a *primitive* closure property of a neighbourhood system — unlike `∩`, `∪` is not
required to stay inside `V.mem` at all. `Exercise812c.lean`'s `XPseq`/`YPseq` (`(d)(4)`'s eventual
code-level targets, `XPseqCode`/`YPseqCode`) are nonetheless *growing unions* of atoms that Scott's
own `NoMinimal`/`SplitSpec'` argument (`XPseq_mem`/`YPseq_mem`, already `Pass`) shows land back
inside `D₁.mem`/`D₀.mem` — but only as a `Prop`-level existential (via `P.surj`), giving no way to
*compute* the resulting index. `IsComputableUnion` supplies exactly that missing effective witness,
mirroring `IsComputableDiff` (`(d)(3)(a)`)'s shape verbatim but for `∪` instead of `\`. One
structure again serves **both** `P₀` and `P₁` symmetrically. -/

/-- **Union-closure**, the `∪` analogue of `NeighborhoodSystem.DiffClosed`: the union of two
neighbourhoods is again a neighbourhood. Unlike `DiffClosed`, no "`-or-∅`" branch is needed — a
union of two `NoMinimal`-nonempty neighbourhoods is automatically itself non-empty, so the only
question `UnionClosed` settles is whether the union stays inside `V.mem`. -/
def NeighborhoodSystem.UnionClosed {α : Type*} (D : NeighborhoodSystem α) : Prop :=
  ∀ {X Y : Set α}, D.mem X → D.mem Y → D.mem (X ∪ Y)

/-- **`IsComputableUnion P`**: set-union relative to the presentation `P` is computable — a
primitive-recursive `unionIdx : ℕ → ℕ → ℕ` indexing `X n ∪ X m` whenever that union is a genuine
neighbourhood (`unionIdx_spec`, mirroring `inter_spec`/`IsComputableDiff.diffIdx_spec` exactly),
together with a decider for that side-condition (`union_computable`, mirroring
`cons_computable`/`IsComputableDiff.diff_computable`). Only `unionIdx` is data; the rest are
`Prop`s, so this stays choice-free to *state* (any particular instance may of course need
`Classical.choice` to *construct*, exactly like `inter`/`cons_computable`/`IsComputableDiff`
themselves would for an arbitrary effectively-given system). -/
structure IsComputableUnion {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
    where
  /-- Index of `X n ∪ X m`, as a function of the two input indices. -/
  unionIdx : ℕ → ℕ → ℕ
  /-- `unionIdx` is primitive recursive (on the `Nat.pair` coding of `n, m`). -/
  unionIdx_primrec : Nat.Primrec (fun t => unionIdx t.unpair.1 t.unpair.2)
  /-- `unionIdx n m` genuinely indexes `X n ∪ X m` whenever that union is (exactly) some `X k` —
  i.e. whenever it is a genuine neighbourhood. -/
  unionIdx_spec : ∀ {n m : ℕ}, (∃ k, P.X k = P.X n ∪ P.X m) → P.X (unionIdx n m) = P.X n ∪ P.X m
  /-- **7.1(i)-for-`∪`**: "`X n ∪ X m` is a genuine neighbourhood" is recursively decidable in
  `n, m`, mirroring `cons_computable`'s role for `∩`. -/
  union_computable : RecDecidable₂ (fun n m => ∃ k, P.X k = P.X n ∪ P.X m)

namespace IsComputableUnion

variable {α : Type*} {V : NeighborhoodSystem α} {P : ComputablePresentation V}

/-- **Under `UnionClosed`, the existential is unconditionally true** — every `X n ∪ X m` is a
genuine neighbourhood, hence indexed by `P.surj`. Mirrors
`IsComputableDiff.diff_exists_iff_ne_empty`, but simpler: `∪` has no "-or-empty" branch to rule
out, so this is a plain existence fact rather than an `iff`. Not needed to *state*
`IsComputableUnion` (kept off the structure itself, matching how `DiffClosed`/`UnionClosed` are
separate hypotheses from `ComputablePresentation` elsewhere in this file); recorded here for
convenience, though the eventual `(d)(4)(c)`/`(d)` instantiation is expected to discharge
`unionIdx_spec`'s hypothesis directly from `XPseq_mem`/`YPseq_mem`-style facts specific to the
atoms actually in play, rather than from a blanket `UnionClosed` on all of `D`. -/
theorem union_exists (hunion : V.UnionClosed) (n m : ℕ) :
    ∃ k, P.X k = P.X n ∪ P.X m :=
  P.surj (hunion (P.mem_X n) (P.mem_X m))

end IsComputableUnion

/-! ## 8.12(d)(4)(b): unions of already-genuine neighbourhoods are genuine

**Scope note (adjustment from the original `arxiv.md` scoping, discovered during execution):** the
original scoping anticipated `XPseqG`/`YPseqG`, a classical `Set`-level generalization of
`Exercise812c.lean`'s `XPseq`/`YPseq` over abstract `splitX`/`splitY`, transcribing
`XPseq_mem`/`XPseq_zero`/`YPseq_mem`/`YPseq_zero` onto the abstracted definitions, as the
prerequisite for `(d)(4)(c)`/`(d)`'s code-level folds. On inspection this is both **unnecessary**
and, worse, **not the right shape**: `XPseq_mem` (`Exercise812c.lean`) is proved via the heavy
`combinedX`/`combinedY`/`transfer_inter_empty_combined` detour, which exists to relate `XPseq n`'s
*emptiness* back to `X n`'s (so as to rule out the `∅` branch of a prior dichotomy) — machinery that
is about identifying `XPseq n` with *Scott's specific* recovered neighbourhood, not about the bare
fact the upcoming code-level fold actually needs: that a *finite, growing union* of already-`mem`
pieces stays `mem`. That bare fact is available far more cheaply, directly from the two hypotheses
already in scope everywhere in this file (`IsPositive`, `DiffClosed`) plus `NoMinimal`, via
`Exercise812c.lean`'s own generic `union_mem_or_empty` (proved from `IsPositive`/`DiffClosed` alone,
**no** `NoMinimal` needed there since it only claims the *dichotomy* `= ∅ ∨ mem`) composed with one
line ruling out the `∅` branch whenever both inputs are *already* known `mem` (so *already* known
non-empty, via `NoMinimal`). This lemma is *the* prerequisite `(d)(4)(c)`/`(d)`'s folds actually
use to discharge `IsComputableUnion.unionIdx_spec`'s existential hypothesis at every step: each
half-step atom folded in is unconditionally `P.mem_X`-genuine (`ComputablePresentation.mem_X` is
total, regardless of any code-level "junk" bookkeeping — cf. `atomPairIdx0_mem`/`atomPairIdx1_mem`,
`(d)(3)(e)`), so the running union of finitely many such atoms is genuine by a one-line induction
via this lemma, with **no** need to first relate any of it back to `XPseq`/`YPseq` or to redo any
part of `(d)(1)`'s already-completed abstraction over `splitX`/`splitY`. -/

/-- **A union of two already-genuine neighbourhoods is again genuine** (sharper than
`union_mem_or_empty`'s bare dichotomy): under `NoMinimal`, a `mem` set is never empty
(`NoMinimal.mem_ne_empty`), so `X ∪ Y ⊇ X ≠ ∅` rules out the dichotomy's `∅` branch outright. -/
theorem NeighborhoodSystem.mem_union_of_mem {γ : Type*} {D : NeighborhoodSystem γ}
    (hpos : D.IsPositive) (hdiff : D.DiffClosed) (hnomin : D.NoMinimal) {X Y : Set γ}
    (hX : D.mem X) (hY : D.mem Y) : D.mem (X ∪ Y) :=
  (union_mem_or_empty hpos hdiff (Or.inr hX) (Or.inr hY)).resolve_left fun h =>
    hnomin.mem_ne_empty hX (Set.subset_eq_empty Set.subset_union_left h)

/-! ## 8.12(d)(4)(c): `XPseqCode` — the code-level `X`-side union fold

Mirrors `Theorem88d.lean`'s `yFoldStep`/`yFold`/`YseqCode` (the union fold over non-junk atoms),
staying purely at the *code* level throughout (no reference to `Exercise812c.lean`'s classical
`XPseq`/`atomPair`, nor even to `(d)(1)`'s classical `atomPairG` — see `(d)(4)(b)`'s scope note for
why that classical detour turned out unnecessary). Correctness (`XFold_found_iff`/
`XFold_mem_of_found`/`XFold_mem_iff`) is stated *conditionally* on the fold's "found" flag
throughout, exactly mirroring `yFold_found_iff`/`yFold_mem_iff`'s own phrasing; see the closing
docstring below for why the *unconditional* form at `N = 4ⁿ` is a flagged, deferred gap rather than
forced through today. -/

section XPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hUnion1 : IsComputableUnion P₁)

/-- **The `X`-side half-step atom's packed state** at depth `n`, index `i` (`i` playing the role of
a length-`n` prefix of sign-pairs, via its own base-4 digits, matching `(d)(3)(d)`'s `deltaPair`
convention): re-run `xSubStep` on the depth-`n` two-sided state at bit-source `i`, with the
`X`-sub-step's own bit forced to `1` — the `"+"`/`true` branch `XPseq`'s classical definition
(`Exercise812c.lean`) always selects, regardless of what the *paired* direct-refinement of the
`D₀`-side would otherwise do with a different bit. -/
noncomputable def xPseqAtomState (n i : ℕ) : ℕ :=
  xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair 1
    (packState2 (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
      (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
      (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i))))

/-- The half-step atom's `D₁`-side index. -/
noncomputable def xPseqAtomIdx (n i : ℕ) : ℕ :=
  stateIdx1 (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)

/-- The half-step atom's junk flag (`1` iff the incoming depth-`n` state was already junk, or its
`D₀`-side direct-refine against `P₀.X n` is itself empty). -/
noncomputable def xPseqAtomJunk (n i : ℕ) : ℕ :=
  stateJunk (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)

theorem primrec_xPseqAtomState : Nat.Primrec
    (fun t : ℕ => xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      t.unpair.1 t.unpair.2) := by
  have hn : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hidx0 : Nat.Primrec (fun t : ℕ =>
      atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2) :=
    primrec_atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
  have hidx1 : Nat.Primrec (fun t : ℕ =>
      atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2) :=
    primrec_atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
  have hjunk : Nat.Primrec (fun t : ℕ =>
      atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2) :=
    primrec_atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
  have hpacked : Nat.Primrec (fun t : ℕ => packState2
      (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2)
      (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2)
      (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2)) :=
    (hidx0.pair (hidx1.pair hjunk)).of_eq fun _ => rfl
  have hinner : Nat.Primrec (fun t : ℕ => Nat.pair 1 (packState2
      (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2)
      (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2)
      (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2))) :=
    (Nat.Primrec.const 1).pair hpacked
  exact ((primrec_xSubStep P₀ P₁ hDiff0 splitX hSplitX).comp (hn.pair hinner)).of_eq fun _ => rfl

theorem primrec_xPseqAtomIdx : Nat.Primrec
    (fun t : ℕ => xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      t.unpair.1 t.unpair.2) :=
  (primrec_stateIdx1.comp (primrec_xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
    hSplitY)).of_eq fun _ => rfl

theorem primrec_xPseqAtomJunk : Nat.Primrec
    (fun t : ℕ => xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      t.unpair.1 t.unpair.2) :=
  (primrec_stateJunk.comp (primrec_xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
    hSplitY)).of_eq fun _ => rfl

theorem xPseqAtomJunk_eq (n i : ℕ) :
    xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i =
      selectFn (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) 1
        (emptyInterDec P₀ (Nat.pair
          (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) n)) := by
  unfold xPseqAtomJunk xPseqAtomState
  rw [xSubStep_junk_eq, stateIdx0_packState2, stateJunk_packState2, selectFn_one]

theorem xPseqAtomJunk_le_one (n i : ℕ) :
    xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i ≤ 1 := by
  rw [xPseqAtomJunk_eq]
  exact selectFn_le_one (atomPairJunk_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY i n)
    (le_refl 1) (emptyInterDec_le_one P₀ _)

theorem xPseqAtomJunk_zero_or_one (n i : ℕ) :
    xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 ∨
      xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 1 := by
  have := xPseqAtomJunk_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i
  omega

/-- **The half-step atom's index, in closed form, when non-junk**: exactly the `X`-sub-step split's
`"+"`/positive branch, `hSplitX.posIdx`, applied to the incoming depth-`n` two-sided indices. -/
theorem xPseqAtomIdx_eq {n i : ℕ}
    (h : xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0) :
    xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i =
      hSplitX.posIdx (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
        (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) n := by
  have h' : stateJunk (xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair 1
      (packState2 (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
        (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
        (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i))))) = 0 := h
  rw [xSubStep_junk_eq] at h'
  unfold xPseqAtomIdx xPseqAtomState
  rw [xSubStep_idx1_eq (h := h'), stateIdx0_packState2, stateIdx1_packState2, selectFn_one]

/-- **The half-step atom is always genuine** on `D₁`'s side, regardless of junk status: any code
index of a `ComputablePresentation` is `mem`-genuine (`ComputablePresentation.mem_X` is total). -/
theorem xPseqAtomIdx_mem (n i : ℕ) :
    D₁.mem (P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)) :=
  P₁.mem_X _

/-- One step of the depth-`n` union fold over `i < N`: silently skip over half-step-junk atoms
(frozen at a sentinel that would otherwise contribute nonsense to the union), and union in every
genuine (non-junk) atom's index via `(d)(4)(a)`'s `hUnion1.unionIdx`. The accumulator is packed as
`(found, code)`, exactly mirroring `Theorem88d.lean`'s `yFoldStep`. -/
noncomputable def XFoldStep (w : ℕ) : ℕ :=
  let n := w.unpair.1
  let i := w.unpair.2.unpair.1
  let acc := w.unpair.2.unpair.2
  selectFn (xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) acc
    (selectFn acc.unpair.1
      (Nat.pair 1 (hUnion1.unionIdx acc.unpair.2
        (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)))
      (Nat.pair 1 (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)))

theorem XFoldStep_eq (n i acc : ℕ) :
    XFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
        (Nat.pair n (Nat.pair i acc)) =
      selectFn (xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) acc
        (selectFn acc.unpair.1
          (Nat.pair 1 (hUnion1.unionIdx acc.unpair.2
            (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)))
          (Nat.pair 1 (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i))) := by
  unfold XFoldStep
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem primrec_XFoldStep :
    Nat.Primrec (XFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1) := by
  have hn : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hi : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hni : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.1 w.unpair.2.unpair.1) := hn.pair hi
  have hjunk : Nat.Primrec (fun w : ℕ =>
      xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY w.unpair.1
        w.unpair.2.unpair.1) :=
    ((primrec_xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp hni).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hidx : Nat.Primrec (fun w : ℕ =>
      xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY w.unpair.1
        w.unpair.2.unpair.1) :=
    ((primrec_xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp hni).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hfound : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp hacc
  have hval : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp hacc
  have hunion : Nat.Primrec (fun w : ℕ => hUnion1.unionIdx w.unpair.2.unpair.2.unpair.2
      (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY w.unpair.1
        w.unpair.2.unpair.1)) :=
    (hUnion1.unionIdx_primrec.comp (hval.pair hidx)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hinner : Nat.Primrec (fun w : ℕ => selectFn w.unpair.2.unpair.2.unpair.1
      (Nat.pair 1 (hUnion1.unionIdx w.unpair.2.unpair.2.unpair.2
        (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY w.unpair.1
          w.unpair.2.unpair.1)))
      (Nat.pair 1 (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY w.unpair.1
        w.unpair.2.unpair.1))) :=
    primrec_selectFn hfound ((Nat.Primrec.const 1).pair hunion) ((Nat.Primrec.const 1).pair hidx)
  exact (primrec_selectFn hjunk hacc hinner).of_eq fun w => by unfold XFoldStep; simp only []

/-- The depth-`n` union fold over `i < N`, starting from the "nothing found yet" accumulator
`(0, 0)`. -/
noncomputable def XFold (n N : ℕ) : ℕ :=
  N.rec (Nat.pair 0 0) (fun i acc => XFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hUnion1 (Nat.pair n (Nat.pair i acc)))

theorem XFold_zero (n : ℕ) : XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n 0 =
    Nat.pair 0 0 := rfl

theorem XFold_succ (n N : ℕ) :
    XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n (N + 1) =
      XFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
        (Nat.pair n (Nat.pair N (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
          n N))) := rfl

theorem primrec_XFold : Nat.Primrec
    (fun t : ℕ => XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
      t.unpair.1 t.unpair.2) :=
  (Nat.Primrec.prec (Nat.Primrec.const (Nat.pair 0 0))
    (primrec_XFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1)).of_eq
    fun _ => rfl

theorem XFold_found_le_one (n : ℕ) :
    ∀ N, (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1 ≤ 1 := by
  intro N
  induction N with
  | zero => simp [XFold_zero]
  | succ N ih =>
    rw [XFold_succ, XFoldStep_eq]
    rcases xPseqAtomJunk_zero_or_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N with
      h0 | h1
    · rw [h0, selectFn_zero]
      rcases Nat.eq_zero_or_pos
          (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1 with
        hf0 | hfpos
      · rw [show (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1
          = 0 from hf0, selectFn_zero, unpair_pair_fst]
      · rw [show (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1
          = 1 from by omega, selectFn_one, unpair_pair_fst]
    · rw [h1, selectFn_one]; exact ih

/-- **The "found" flag exactly tracks existence of a non-junk half-step atom below `N`.** -/
theorem XFold_found_iff (n : ℕ) :
    ∀ N, (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1 = 1 ↔
      ∃ i < N, xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 := by
  intro N
  induction N with
  | zero => simp [XFold_zero]
  | succ N ih =>
    rw [XFold_succ, XFoldStep_eq]
    rcases xPseqAtomJunk_zero_or_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N with
      h0 | h1
    · rw [h0, selectFn_zero]
      have hval1 : (selectFn
          (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1
          (Nat.pair 1 (hUnion1.unionIdx
            (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.2
            (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N)))
          (Nat.pair 1 (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N))
          ).unpair.1 = 1 := by
        have hle := XFold_found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N
        rcases Nat.eq_zero_or_pos
            (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1 with
          hf | hf
        · rw [show (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1
            = 0 from hf, selectFn_zero, unpair_pair_fst]
        · rw [show (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1
            = 1 from by omega, selectFn_one, unpair_pair_fst]
      rw [hval1]
      exact ⟨fun _ => ⟨N, Nat.lt_succ_self N, h0⟩, fun _ => rfl⟩
    · rw [h1, selectFn_one, ih]
      constructor
      · rintro ⟨i, hi, hie⟩; exact ⟨i, Nat.lt_succ_of_lt hi, hie⟩
      · rintro ⟨i, hi, hie⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact ⟨i, hi', hie⟩
        · exact absurd hie (by omega)

include hD₁pos hD₁diff hD₁nomin in
/-- **Once "found", the running union's code is always `D₁`-genuine.** New content beyond
`Theorem88d.lean`'s precedent (there, `unionUX`'s output is unconditionally genuine, since `U` is
unconditionally union-closed): here `hUnion1.unionIdx_spec`'s conclusion is conditional on its
existential hypothesis, discharged at each step via `(d)(4)(b)`'s `mem_union_of_mem` applied to the
running union (genuine, by this very induction) and the new atom (genuine, `xPseqAtomIdx_mem`,
unconditionally). This is exactly the fact `XFold_mem_iff` below needs to legally rewrite through
`unionIdx_spec` at its own inductive step. -/
theorem XFold_mem_of_found (n : ℕ) :
    ∀ N, (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1 = 1 →
      D₁.mem (P₁.X (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.2) := by
  intro N
  induction N with
  | zero => intro h; simp [XFold_zero] at h
  | succ N ih =>
    intro hfound1
    rw [XFold_succ, XFoldStep_eq] at hfound1 ⊢
    rcases xPseqAtomJunk_zero_or_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N with
      h0 | h1
    · rw [h0, selectFn_zero] at hfound1 ⊢
      have hle := XFold_found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N
      rcases Nat.eq_zero_or_pos
          (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1 with
        hf0 | hfpos
      · rw [show (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1
          = 0 from hf0, selectFn_zero, unpair_pair_snd]
        exact xPseqAtomIdx_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N
      · have hf1 : (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1
            = 1 := by omega
        rw [hf1, selectFn_one, unpair_pair_snd]
        have hprevmem := ih hf1
        have hnewmem := xPseqAtomIdx_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N
        have hex : ∃ k, P₁.X k =
            P₁.X (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.2 ∪
              P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N) :=
          P₁.surj (NeighborhoodSystem.mem_union_of_mem hD₁pos hD₁diff hD₁nomin hprevmem hnewmem)
        rw [hUnion1.unionIdx_spec hex]
        exact NeighborhoodSystem.mem_union_of_mem hD₁pos hD₁diff hD₁nomin hprevmem hnewmem
    · rw [h1, selectFn_one] at hfound1 ⊢
      exact ih hfound1

include hD₁pos hD₁diff hD₁nomin in
/-- **The membership form of `XFold`'s correctness**: once a non-junk half-step atom has been found
below `N`, the running code's `P₁`-image is exactly the union of the genuine (non-junk) atoms seen
so far. Mirrors `yFold_mem_iff`, with `unionIdx_spec`'s conditional rewrite (discharged via
`XFold_mem_of_found`/`mem_union_of_mem`) in place of `unionUX`'s unconditional `UX_unionUX`. -/
theorem XFold_mem_iff (n : ℕ) :
    ∀ N, (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1 = 1 →
      ∀ z : β, z ∈ P₁.X (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.2 ↔
        ∃ i < N, xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 ∧
          z ∈ P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) := by
  intro N
  induction N with
  | zero => intro h; simp [XFold_zero] at h
  | succ N ih =>
    intro hfound1 z
    rw [XFold_succ, XFoldStep_eq] at hfound1 ⊢
    rcases xPseqAtomJunk_zero_or_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N with
      h0 | h1
    · rw [h0, selectFn_zero] at hfound1 ⊢
      have hle := XFold_found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N
      rcases Nat.eq_zero_or_pos
          (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1 with
        hf0 | hfpos
      · rw [show (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1
          = 0 from hf0, selectFn_zero, unpair_pair_snd]
        constructor
        · intro hz; exact ⟨N, Nat.lt_succ_self N, h0, hz⟩
        · rintro ⟨i, hi, hie, hz⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact absurd ((XFold_found_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
              hUnion1 n N).mpr ⟨i, hi', hie⟩) (by rw [hf0]; omega)
          · exact hz
      · have hf1 : (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1
            = 1 := by omega
        rw [hf1, selectFn_one, unpair_pair_snd]
        have hprevmem := XFold_mem_of_found P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
          hD₁pos hD₁diff hD₁nomin hUnion1 n N hf1
        have hnewmem := xPseqAtomIdx_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N
        have hex : ∃ k, P₁.X k =
            P₁.X (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.2 ∪
              P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N) :=
          P₁.surj (NeighborhoodSystem.mem_union_of_mem hD₁pos hD₁diff hD₁nomin hprevmem hnewmem)
        rw [hUnion1.unionIdx_spec hex, Set.mem_union, ih hf1 z]
        constructor
        · rintro (⟨i, hi, hie, hz⟩ | hz)
          · exact ⟨i, Nat.lt_succ_of_lt hi, hie, hz⟩
          · exact ⟨N, Nat.lt_succ_self N, h0, hz⟩
        · rintro ⟨i, hi, hie, hz⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact Or.inl ⟨i, hi', hie, hz⟩
          · exact Or.inr hz
    · rw [h1, selectFn_one] at hfound1 ⊢
      rw [ih hfound1 z]
      constructor
      · rintro ⟨i, hi, hie, hz⟩; exact ⟨i, Nat.lt_succ_of_lt hi, hie, hz⟩
      · rintro ⟨i, hi, hie, hz⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact ⟨i, hi', hie, hz⟩
        · exact absurd hie (by omega)

/-- **`XPseqCode`, the code-level analogue of `Exercise812c.lean`'s `XPseq`.** The `Nat.Primrec`
union, over the `4ⁿ` bit-sources `i < 4ⁿ`, of the genuine (non-junk) half-step atoms
`xPseqAtomIdx n i`. -/
noncomputable def XPseqCode (n : ℕ) : ℕ :=
  (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n (4 ^ n)).unpair.2

theorem primrec_XPseqCode : Nat.Primrec
    (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1) := by
  have h4n : Nat.Primrec (fun n : ℕ => 4 ^ n) := primrec_pow₂ (Nat.Primrec.const 4) Nat.Primrec.id
  refine (Nat.Primrec.right.comp
    ((primrec_XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1).comp
      (Nat.Primrec.id.pair h4n))).of_eq fun n => ?_
  show (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
    (Nat.pair n (4 ^ n)).unpair.1 (Nat.pair n (4 ^ n)).unpair.2).unpair.2 = XPseqCode P₀ P₁ hDiff0
      hDiff1 splitX hSplitX splitY hSplitY hUnion1 n
  rw [unpair_pair_fst, unpair_pair_snd]; rfl

include hD₁pos hD₁diff hD₁nomin in
/-- **Once "found" at `N = 4ⁿ`, `XPseqCode n` is `D₁`-genuine.** Conditional exactly as
`XFold_mem_of_found` is; see the section's closing docstring for the deferred unconditional gap. -/
theorem XPseqCode_mem {n : ℕ}
    (hfound : (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n (4 ^ n)).unpair.1
      = 1) :
    D₁.mem (P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n)) :=
  XFold_mem_of_found P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₁pos hD₁diff hD₁nomin
    hUnion1 n (4 ^ n) hfound

include hD₁pos hD₁diff hD₁nomin in
/-- **The closed-form membership characterization of `XPseqCode`, conditional on "found" at
`N = 4ⁿ`**: a point lies in `P₁.X (XPseqCode n)` iff it lies in some genuine (non-junk) half-step
atom `xPseqAtomIdx n i`, `i < 4ⁿ`. -/
theorem mem_XPseqCode_iff {n : ℕ}
    (hfound : (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n (4 ^ n)).unpair.1
      = 1) (z : β) :
    z ∈ P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n) ↔
      ∃ i < 4 ^ n, xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 ∧
        z ∈ P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) :=
  XFold_mem_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₁pos hD₁diff hD₁nomin hUnion1
    n (4 ^ n) hfound z

end XPseqCode

section AtomPairCorrect4

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty) (hD₀nomin : D₀.NoMinimal)

include hD₀pos hD₀diff hxSplit hD₁pos hD₁diff hySplit hD₀mne hD₁mne hD₀nomin in
/-- **8.12(d)(4)(c)(iv): non-trivial intersection with `P₀.X n`, still classical.** Combines
`(c)(iii)`'s `atomPairG_master_covered_deltaPair` with `P₀.X n ⊆ D₀.master` (`sub_master`) and
`P₀.X n ≠ ∅` (fresh here: `hD₀nomin.mem_ne_empty`, the one place in `(d)(4)(c)`'s whole closure that
needs `NoMinimal` itself, rather than just `SplitSpec'`/`IsPositive`/`DiffClosed` — `(d)(1)`'s
generalized layer deliberately dropped `NoMinimal`, but this specific fact ("every genuine
neighbourhood, not just the master, is non-empty") has no substitute among the weaker hypotheses).
Picks any `z ∈ P₀.X n` (exists by the above), lands it in some covering piece via `(c)(iii)`, and
that piece's `i` is exactly the witness. -/
theorem exists_atomPairG_deltaPair_inter_Xn_ne_empty (n : ℕ) :
    ∃ i < 4 ^ n, (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1 ∩ P₀.X n ≠ ∅ := by
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr (hD₀nomin.mem_ne_empty (P₀.mem_X n))
  have hzmaster : z ∈ D₀.master := D₀.sub_master (P₀.mem_X n) hz
  obtain ⟨i, hi, hzcover⟩ := atomPairG_master_covered_deltaPair D₀ D₁ hD₀pos hD₀diff splitY hySplit
    hD₁pos hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne n z hzmaster
  exact ⟨i, hi, Set.nonempty_iff_ne_empty.mp ⟨z, hzcover, hz⟩⟩

end AtomPairCorrect4

section AtomPairCorrect4Snd

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty) (hD₁nomin : D₁.NoMinimal)

include hD₀pos hD₀diff hxSplit hD₁pos hD₁diff hySplit hD₀mne hD₁mne hD₁nomin in
/-- **8.12(d)(4)(d)(iv): non-trivial intersection with `P₁.X n`, still classical, `D₁`-side.** The
`D₁`-side mirror of `(c)(iv)`'s `exists_atomPairG_deltaPair_inter_Xn_ne_empty`: combines `(d)(iii)`'s
`atomPairG_master_covered_deltaPair_snd` with `P₁.X n ⊆ D₁.master` (`sub_master`) and `P₁.X n ≠ ∅`
(fresh `hD₁nomin.mem_ne_empty`, the `D₁`-side analogue of `(c)(iv)`'s one genuinely new hypothesis).
Picks any `z ∈ P₁.X n` (exists by the above), lands it in some covering piece via `(d)(iii)`, and
that piece's `i` is exactly the witness. Note this alone doesn't fix the `bx` bit `YPseqCode`'s fold
also needs — that's resolved only in `(d)(vi)`. -/
theorem exists_atomPairG_deltaPair_inter_Yn_ne_empty (n : ℕ) :
    ∃ i < 4 ^ n, (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 ∩ P₁.X n ≠ ∅ := by
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr (hD₁nomin.mem_ne_empty (P₁.mem_X n))
  have hzmaster : z ∈ D₁.master := D₁.sub_master (P₁.mem_X n) hz
  obtain ⟨i, hi, hzcover⟩ := atomPairG_master_covered_deltaPair_snd D₀ D₁ hD₀pos hD₀diff splitY
    hySplit hD₁pos hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne n z hzmaster
  exact ⟨i, hi, Set.nonempty_iff_ne_empty.mp ⟨z, hzcover, hz⟩⟩

end AtomPairCorrect4Snd

section AtomPairCorrect5

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
/-- **8.12(d)(4)(c)(v): the converse-biconditional.** Once a bit-source `i`'s recorded state at
depth `n` is genuinely junk, the classical `atomPairG`-component at that depth is already `∅` (the
`D₀`-side; contrapositive-equivalent to `(atomPairG ... n).1 ≠ ∅ → atomPairJunk n i = 0`). Proved
by induction on `n`: a junk state at depth `n + 1` either (i) was *already* junk at depth `n` (the
induction hypothesis, then propagated forward via `atomPairG_fst_subset`), or (ii) is *freshly*
created at this very step by exactly one of the two half-steps' direct-refine checks tripping —
the `X`-sub-step's check trips the `D₀`-side directly (mirrored onto `atomPairG`'s own `A1`, then
propagated to `A2` via `yStepG_fst_subset`), or the `Y`-sub-step's check trips the `D₁`-side
directly (`B2`, transferred to the `D₀`-side via `atomPairG_invariant`'s dichotomy at `n + 1`). -/
theorem atomPairG_fst_eq_empty_of_junk_eq_one (i : ℕ) : ∀ n,
    atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 1 →
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1 = ∅ := by
  intro n
  induction n with
  | zero =>
    intro h
    exfalso
    have h0 : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 i = 0 := by
      simp [atomPairJunk, atomPairCodeState, atomPairBase, stateBase2]
    omega
  | succ n ih =>
    intro hjunk1
    rcases Nat.eq_zero_or_pos (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
      with hn0 | hnpos
    · -- freshly junk at this step: chase the per-step algebra
      obtain ⟨hidx0, hidx1⟩ := atomPairCodeState_correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
        hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne i n
        hn0
      unfold atomPairJunk at hjunk1 hn0
      unfold atomPairIdx0 at hidx0
      unfold atomPairIdx1 at hidx1
      rw [atomPairCodeState_succ] at hjunk1
      unfold atomPairStep pcN pcT xwB1 xwS at hjunk1
      simp only [unpair_pair_fst, unpair_pair_snd, stateInnerC_packStateC] at hjunk1 hidx0 hidx1
      set T := atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY (Nat.pair i n)
        with hTdef
      have hrem : stateRemC T = i / 4 ^ n :=
        stateRemC_atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY i n
      have hb1 : stateRemC T % 2 = if (deltaPair i n).1 then 1 else 0 := by
        rw [hrem]
        rcases Nat.mod_two_eq_zero_or_one (i / 4 ^ n) with h0 | h1
        · have hδ : (deltaPair i n).1 = false := by unfold deltaPair; simp [h0]
          simp [hδ, h0]
        · have hδ : (deltaPair i n).1 = true := by unfold deltaPair; simp [h1]
          simp [hδ, h1]
      have hb2 : stateRemC T / 2 % 2 = if (deltaPair i n).2 then 1 else 0 := by
        rw [hrem]
        rcases Nat.mod_two_eq_zero_or_one (i / 4 ^ n / 2) with h0 | h1
        · have hδ : (deltaPair i n).2 = false := by unfold deltaPair; simp [h0]
          simp [hδ, h0]
        · have hδ : (deltaPair i n).2 = true := by unfold deltaPair; simp [h1]
          simp [hδ, h1]
      rw [hb1, hb2] at hjunk1
      rw [ySubStep_junk_eq] at hjunk1
      rw [xSubStep_junk_eq, hn0, selectFn_zero] at hjunk1
      -- `hjunk1 : selectFn xcheck 1 ycheck = 1`, `xcheck`/`ycheck` the two direct-refine checks
      have hb1le : (if (deltaPair i n).1 then (1 : ℕ) else 0) ≤ 1 := by
        rcases Bool.eq_false_or_eq_true (deltaPair i n).1 with h | h <;> simp [h]
      have hxle : selectFn (if (deltaPair i n).1 then 1 else 0)
          (emptyInterDec P₀ (Nat.pair (stateIdx0 (stateInnerC T)) n))
          (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (stateInnerC T)) n)) ≤ 1 :=
        selectFn_le_one hb1le (emptyInterDec_le_one P₀ _) (emptyDiffDec_le_one P₀ hDiff0 _)
      rcases Nat.eq_zero_or_pos (selectFn (if (deltaPair i n).1 then 1 else 0)
          (emptyInterDec P₀ (Nat.pair (stateIdx0 (stateInnerC T)) n))
          (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (stateInnerC T)) n))) with hx0 | hxpos
      · -- the `X`-sub-step's check didn't trip: it's genuinely non-junk, so chase the `Y`-check
        rw [hx0, selectFn_zero] at hjunk1
        have hxnonjunk : stateJunk (xSubStep P₀ P₁ hDiff0 splitX hSplitX
            (Nat.pair n (Nat.pair (if (deltaPair i n).1 then 1 else 0) (stateInnerC T)))) = 0 := by
          rw [xSubStep_junk_eq, hn0, selectFn_zero]; exact hx0
        obtain ⟨ihAB, -, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
          hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n
        obtain ⟨hxA1, hxB1⟩ := xSubStep_correct P₀ P₁ hDiff0 splitX hSplitX hD₀pos hD₀diff hD₀nomin
          hxSplit hidx0 hidx1 ihAB ihB (deltaPair i n).1 hxnonjunk
        have hB2 : (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) (n + 1)).2 = ∅ := by
          rw [atomPairG_succ_eq]
          by_cases hδ2 : (deltaPair i n).2 = true
          · simp only [hδ2, if_true] at hjunk1
            rw [selectFn_one] at hjunk1
            have hBe := (emptyInterDec_eq_one_iff P₁ hD₁pos hD₁nomin _ _).mp hjunk1
            rw [hxB1] at hBe
            simp only [yStepG, xyStep, Prod.swap, hδ2, if_true]
            exact hBe
          · simp only [hδ2, Bool.false_eq_true, if_false] at hjunk1
            rw [selectFn_zero] at hjunk1
            have hBe := (emptyDiffDec_eq_one_iff P₁ hDiff1 hD₁diff hD₁nomin _ _).mp hjunk1
            rw [hxB1] at hBe
            simp only [yStepG, xyStep, Prod.swap, hδ2, Bool.false_eq_true, if_false]
            exact hBe
        exact (atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff splitX
          hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) (n + 1)).1.mpr hB2
      · -- the `X`-sub-step's check tripped: the direct-refine component is already `∅`
        have hx1 : selectFn (if (deltaPair i n).1 then 1 else 0)
            (emptyInterDec P₀ (Nat.pair (stateIdx0 (stateInnerC T)) n))
            (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (stateInnerC T)) n)) = 1 := by omega
        have hA1eq : (xStepG splitX
            (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
            (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n)
            (deltaPair i n).1).1 = ∅ := by
          by_cases hδ1 : (deltaPair i n).1 = true
          · simp only [xStepG, xyStep, hδ1, if_true] at hx1 ⊢
            rw [selectFn_one] at hx1
            have hAe := (emptyInterDec_eq_one_iff P₀ hD₀pos hD₀nomin _ _).mp hx1
            rw [hidx0] at hAe
            exact hAe
          · simp only [xStepG, xyStep, hδ1, Bool.false_eq_true, if_false] at hx1 ⊢
            rw [selectFn_zero] at hx1
            have hAe := (emptyDiffDec_eq_one_iff P₀ hDiff0 hD₀diff hD₀nomin _ _).mp hx1
            rw [hidx0] at hAe
            exact hAe
        obtain ⟨hspecAB, hspecAmem⟩ := xStepG_spec D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
          hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n
        rw [atomPairG_succ_eq]
        exact Set.subset_eq_empty
          (yStepG_fst_subset hySplit hspecAB hspecAmem (P₁.X n) (deltaPair i n).2) hA1eq
    · -- already junk at depth `n`: propagate forward
      have hn1 : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 1 := by
        have := atomPairJunk_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY i n
        omega
      exact Set.subset_eq_empty (atomPairG_fst_subset D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
        hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n) (ih hn1)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
/-- **The contrapositive form**, matching `(d)(4)(c)`'s originally-flagged gap statement exactly:
a non-empty classical `D₀`-side component forces the recorded state to be non-junk. -/
theorem atomPairJunk_eq_zero_of_ne_empty {i n : ℕ}
    (h : (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1 ≠ ∅) :
    atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 := by
  by_contra hne
  have h1 : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 1 := by
    have := atomPairJunk_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY i n
    omega
  exact h (atomPairG_fst_eq_empty_of_junk_eq_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne i n h1)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
/-- **8.12(d)(4)(d)(v): the converse-biconditional, `D₁`-side.** The `D₁`-side mirror of
`atomPairG_fst_eq_empty_of_junk_eq_one` — but **not** a naive `.1`↔`.2` transcription: the two
per-step sub-cases' roles *swap* relative to the `D₀`-side proof. A junk state at depth `n + 1`
either (i) was already junk at depth `n` (propagated forward via `atomPairG_snd_subset`), or
(ii) freshly created this step, splitting on the exact same `xcheck`/`ycheck` decomposition
(`selectFn xcheck 1 ycheck = 1`, tied to `P₀`/`A1` and `P₁`/`B2` respectively, shared verbatim with
the `D₀`-side proof — the underlying per-step algebra doesn't know which side we're targeting):
**`xcheck = 0`** (`X`-sub-step non-junk) — the *`Y`-sub-step's own direct-refine check* trips the
`D₁`-side (`B2`) *directly*, and since `B2` **is** this branch's target, **no
`atomPairG_invariant` hop is needed** (unlike the `D₀`-side proof, where this same branch's direct
trigger is `B2` but the target is `A2`, needing the invariant to hop across). **`xcheck = 1`**
(`X`-sub-step's own check trips) — this gives `A1 = ∅` directly (identical derivation to the
`D₀`-side proof), but now the target `B2` needs a hop *from* `A1` *to* `B1` via `xStepG_spec`'s own
half-step biconditional `hspecAB` (not the depth-crossing `atomPairG_invariant` — this is a purely
local one-step fact, already in scope), then propagates via the *trivial* `yStepG_snd_subset` (no
`SplitSpec'` hypotheses needed at all) rather than the `D₀`-side's `SplitSpec'`-needing
`yStepG_fst_subset`. Net effect: this `D₁`-side proof needs `atomPairG_invariant` in *neither*
branch, genuinely simpler than `(c)(v)`'s own proof. -/
theorem atomPairG_snd_eq_empty_of_junk_eq_one (i : ℕ) : ∀ n,
    atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 1 →
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 = ∅ := by
  intro n
  induction n with
  | zero =>
    intro h
    exfalso
    have h0 : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 i = 0 := by
      simp [atomPairJunk, atomPairCodeState, atomPairBase, stateBase2]
    omega
  | succ n ih =>
    intro hjunk1
    rcases Nat.eq_zero_or_pos (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
      with hn0 | hnpos
    · -- freshly junk at this step: chase the per-step algebra (identical unfolding to `(c)(v)`)
      obtain ⟨hidx0, hidx1⟩ := atomPairCodeState_correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
        hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne i n
        hn0
      unfold atomPairJunk at hjunk1 hn0
      unfold atomPairIdx0 at hidx0
      unfold atomPairIdx1 at hidx1
      rw [atomPairCodeState_succ] at hjunk1
      unfold atomPairStep pcN pcT xwB1 xwS at hjunk1
      simp only [unpair_pair_fst, unpair_pair_snd, stateInnerC_packStateC] at hjunk1 hidx0 hidx1
      set T := atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY (Nat.pair i n)
        with hTdef
      have hrem : stateRemC T = i / 4 ^ n :=
        stateRemC_atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY i n
      have hb1 : stateRemC T % 2 = if (deltaPair i n).1 then 1 else 0 := by
        rw [hrem]
        rcases Nat.mod_two_eq_zero_or_one (i / 4 ^ n) with h0 | h1
        · have hδ : (deltaPair i n).1 = false := by unfold deltaPair; simp [h0]
          simp [hδ, h0]
        · have hδ : (deltaPair i n).1 = true := by unfold deltaPair; simp [h1]
          simp [hδ, h1]
      have hb2 : stateRemC T / 2 % 2 = if (deltaPair i n).2 then 1 else 0 := by
        rw [hrem]
        rcases Nat.mod_two_eq_zero_or_one (i / 4 ^ n / 2) with h0 | h1
        · have hδ : (deltaPair i n).2 = false := by unfold deltaPair; simp [h0]
          simp [hδ, h0]
        · have hδ : (deltaPair i n).2 = true := by unfold deltaPair; simp [h1]
          simp [hδ, h1]
      rw [hb1, hb2] at hjunk1
      rw [ySubStep_junk_eq] at hjunk1
      rw [xSubStep_junk_eq, hn0, selectFn_zero] at hjunk1
      -- `hjunk1 : selectFn xcheck 1 ycheck = 1`, `xcheck`/`ycheck` the two direct-refine checks
      have hb1le : (if (deltaPair i n).1 then (1 : ℕ) else 0) ≤ 1 := by
        rcases Bool.eq_false_or_eq_true (deltaPair i n).1 with h | h <;> simp [h]
      have hxle : selectFn (if (deltaPair i n).1 then 1 else 0)
          (emptyInterDec P₀ (Nat.pair (stateIdx0 (stateInnerC T)) n))
          (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (stateInnerC T)) n)) ≤ 1 :=
        selectFn_le_one hb1le (emptyInterDec_le_one P₀ _) (emptyDiffDec_le_one P₀ hDiff0 _)
      rcases Nat.eq_zero_or_pos (selectFn (if (deltaPair i n).1 then 1 else 0)
          (emptyInterDec P₀ (Nat.pair (stateIdx0 (stateInnerC T)) n))
          (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (stateInnerC T)) n))) with hx0 | hxpos
      · -- `xcheck = 0`: `X`-sub-step non-junk, chase the `Y`-check — hits `B2` *directly*
        rw [hx0, selectFn_zero] at hjunk1
        have hxnonjunk : stateJunk (xSubStep P₀ P₁ hDiff0 splitX hSplitX
            (Nat.pair n (Nat.pair (if (deltaPair i n).1 then 1 else 0) (stateInnerC T)))) = 0 := by
          rw [xSubStep_junk_eq, hn0, selectFn_zero]; exact hx0
        obtain ⟨ihAB, -, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
          hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n
        obtain ⟨-, hxB1⟩ := xSubStep_correct P₀ P₁ hDiff0 splitX hSplitX hD₀pos hD₀diff hD₀nomin
          hxSplit hidx0 hidx1 ihAB ihB (deltaPair i n).1 hxnonjunk
        rw [atomPairG_succ_eq]
        by_cases hδ2 : (deltaPair i n).2 = true
        · simp only [hδ2, if_true] at hjunk1
          rw [selectFn_one] at hjunk1
          have hBe := (emptyInterDec_eq_one_iff P₁ hD₁pos hD₁nomin _ _).mp hjunk1
          rw [hxB1] at hBe
          simp only [yStepG, xyStep, Prod.swap, hδ2, if_true]
          exact hBe
        · simp only [hδ2, Bool.false_eq_true, if_false] at hjunk1
          rw [selectFn_zero] at hjunk1
          have hBe := (emptyDiffDec_eq_one_iff P₁ hDiff1 hD₁diff hD₁nomin _ _).mp hjunk1
          rw [hxB1] at hBe
          simp only [yStepG, xyStep, Prod.swap, hδ2, Bool.false_eq_true, if_false]
          exact hBe
      · -- `xcheck = 1`: the `A1`-check tripped; hop to `B1` via `xStepG_spec`'s local biconditional,
        -- then propagate via the trivial `yStepG_snd_subset` (no `SplitSpec'` needed)
        have hx1 : selectFn (if (deltaPair i n).1 then 1 else 0)
            (emptyInterDec P₀ (Nat.pair (stateIdx0 (stateInnerC T)) n))
            (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (stateInnerC T)) n)) = 1 := by omega
        have hA1eq : (xStepG splitX
            (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
            (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n)
            (deltaPair i n).1).1 = ∅ := by
          by_cases hδ1 : (deltaPair i n).1 = true
          · simp only [xStepG, xyStep, hδ1, if_true] at hx1 ⊢
            rw [selectFn_one] at hx1
            have hAe := (emptyInterDec_eq_one_iff P₀ hD₀pos hD₀nomin _ _).mp hx1
            rw [hidx0] at hAe
            exact hAe
          · simp only [xStepG, xyStep, hδ1, Bool.false_eq_true, if_false] at hx1 ⊢
            rw [selectFn_zero] at hx1
            have hAe := (emptyDiffDec_eq_one_iff P₀ hDiff0 hD₀diff hD₀nomin _ _).mp hx1
            rw [hidx0] at hAe
            exact hAe
        obtain ⟨hspecAB, -⟩ := xStepG_spec D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
          hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n
        rw [atomPairG_succ_eq]
        exact Set.subset_eq_empty
          (yStepG_snd_subset splitY _ _ (P₁.X n) (deltaPair i n).2) (hspecAB.mpr hA1eq)
    · -- already junk at depth `n`: propagate forward
      have hn1 : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 1 := by
        have := atomPairJunk_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY i n
        omega
      exact Set.subset_eq_empty (atomPairG_snd_subset D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
        hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n) (ih hn1)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
/-- **The contrapositive form, `D₁`-side.** The exact `D₁`-side analogue of
`atomPairJunk_eq_zero_of_ne_empty`: a non-empty classical `D₁`-side component forces the recorded
state to be non-junk. -/
theorem atomPairJunk_eq_zero_of_snd_ne_empty {i n : ℕ}
    (h : (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 ≠ ∅) :
    atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 := by
  by_contra hne
  have h1 : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 1 := by
    have := atomPairJunk_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY i n
    omega
  exact h (atomPairG_snd_eq_empty_of_junk_eq_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne i n h1)

end AtomPairCorrect5

/-! ### 8.12(d)(4)(c)(vi): assembling the unconditional "found" fact

`Theorem88d.lean` discharges its own analogous conditional hypothesis unconditionally via
`exists_atomUEmpty_zero`/`yFold_two_pow_found`, using structure specific to that one-sided
embedding (`idxSet (e P)`, `self_mem_idxSet`) that has no analogue here. For this two-sided
construction, "`∃ i < 4ⁿ, xPseqAtomJunk n i = 0`" needs, classically, some `i` with the depth-`n`
state non-junk *and* its `D₀`-side specifically intersecting `P₀.X n` non-trivially — i.e. an
analogue of `Exercise812c.lean`'s `XPseq_ne_empty`, which is there proved via the heavy
`combinedX`/`combinedY`/`transfer_inter_empty_combined` detour (the same machinery `(d)(4)(b)`'s
scope note found unnecessary for the *conditional* correctness above).

**Both classical and converse-biconditional halves were already done** (`(d)(4)(c)`'s nested
sub-goals `(c)(i)`–`(c)(v)`, all `Pass`): by induction on `n`, the classical `atomPairG`-pieces
cover `D₀.master` (`atomPairG_master_covered`/`atomPairG_master_covered_deltaPair`), giving
`exists_atomPairG_deltaPair_inter_Xn_ne_empty` — some bit-source `i < 4ⁿ` whose depth-`n` `D₀`-side
intersects `P₀.X n` non-trivially, purely classically (`(c)(i)`–`(c)(iv)`). `(c)(v)`'s
`atomPairJunk_eq_zero_of_ne_empty` supplies exactly the missing converse half of
`(d)(3)(d)`'s `atomPairCodeState_correct` needed to transport this non-emptiness witness back to
the code level: since `(atomPairG ... n).1 ∩ P₀.X n ≠ ∅` forces `(atomPairG ... n).1 ≠ ∅`, it
forces `atomPairJunk n i = 0` (i.e. `xPseqAtomJunk n i = 0`, `atomPairJunk_eq_zero_of_ne_empty`),
discharging `XFold_found_iff`'s hypothesis at exactly the witness `i` from
`exists_atomPairG_deltaPair_inter_Xn_ne_empty`.

**This section (`(c)(vi)`) is the final assembly**, chaining those two facts exactly as planned:
`xPseqAtomJunk_exists_zero` is the unconditional "found" existential itself; `XFold_four_pow_found`
transports it through `XFold_found_iff` to the fold's own found flag at `N = 4ⁿ`
(mirroring `Theorem88d.lean`'s `yFold_two_pow_found`); and `XPseqCode_mem_unconditional`/
`mem_XPseqCode_iff_unconditional` re-specialize `XPseqCode_mem`/`mem_XPseqCode_iff` at that
unconditional witness, dropping the `hfound` hypothesis entirely. This closes `(d)(4)(c)` in full
(all of `(c)(i)`–`(c)(vi)` now `Pass`, unconditionally). -/

section XPseqCodeUnconditional

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
/-- **8.12(d)(4)(c)(vi), step 1: the unconditional "found" existential.** Combines
`exists_atomPairG_deltaPair_inter_Xn_ne_empty` (some bit-source `i < 4ⁿ` whose depth-`n` `D₀`-side
classical piece meets `P₀.X n`) with `atomPairJunk_eq_zero_of_ne_empty` (a non-empty classical
piece forces its recorded state non-junk) and `atomPairCodeState_correct`'s forward half (rewriting
the now-known-non-junk classical piece as the code-indexed `P₀.X (atomPairIdx0 ...)`) to land the
non-trivial intersection at the *code* level, `P₀.X (atomPairIdx0 ... n i) ∩ P₀.X n ≠ ∅`. Reading
this off `emptyInterDec`'s converse (`emptyInterDec_eq_one_iff`, contrapositive via
`emptyInterDec_le_one`) gives exactly `emptyInterDec P₀ (atomPairIdx0 ... n i, n) = 0`, which is
`xPseqAtomJunk_eq`'s defining condition once `atomPairJunk n i = 0` collapses the `selectFn`. -/
theorem xPseqAtomJunk_exists_zero (n : ℕ) :
    ∃ i < 4 ^ n, xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 := by
  obtain ⟨i, hi, hne⟩ := exists_atomPairG_deltaPair_inter_Xn_ne_empty P₀ P₁ splitX splitY
    hD₀pos hD₀diff hxSplit hD₁pos hD₁diff hySplit hD₀mne hD₁mne hD₀nomin n
  have hAne : (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1 ≠ ∅ := fun hA =>
    hne (Set.subset_eq_empty Set.inter_subset_left hA)
  have hjunk0 : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 :=
    atomPairJunk_eq_zero_of_ne_empty P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hAne
  obtain ⟨hidx0, -⟩ := atomPairCodeState_correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne i n hjunk0
  have hne' : P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) ∩
      P₀.X n ≠ ∅ := by rw [hidx0]; exact hne
  refine ⟨i, hi, ?_⟩
  rw [xPseqAtomJunk_eq, hjunk0, selectFn_zero]
  by_contra hcon
  have hle := emptyInterDec_le_one P₀ (Nat.pair
    (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) n)
  have h1 : emptyInterDec P₀ (Nat.pair
      (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) n) = 1 := by omega
  exact hne' ((emptyInterDec_eq_one_iff P₀ hD₀pos hD₀nomin _ _).mp h1)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
/-- **Step 2: the fold's "found" flag is unconditionally `1` at `N = 4ⁿ`**, mirroring
`Theorem88d.lean`'s `yFold_two_pow_found` — transport `xPseqAtomJunk_exists_zero` through
`XFold_found_iff`. -/
theorem XFold_four_pow_found (n : ℕ) :
    (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n (4 ^ n)).unpair.1 = 1 :=
  (XFold_found_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n (4 ^ n)).mpr
    (xPseqAtomJunk_exists_zero P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne n)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
/-- **Step 3a: `XPseqCode n` is unconditionally `D₁`-genuine** — `XPseqCode_mem` specialized at
`XFold_four_pow_found`'s unconditional witness, dropping the `hfound` hypothesis entirely. -/
theorem XPseqCode_mem_unconditional (n : ℕ) :
    D₁.mem (P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n)) :=
  XPseqCode_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₁pos hD₁diff hD₁nomin hUnion1
    (XFold_four_pow_found P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin
      hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 n)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
/-- **Step 3b: the closed-form membership characterization of `XPseqCode`, unconditionally** —
`mem_XPseqCode_iff` specialized the same way. This is `(d)(4)(c)`'s headline closed form, matching
Scott's `X`-side recursion with no residual "found" side-condition. -/
theorem mem_XPseqCode_iff_unconditional (n : ℕ) (z : β) :
    z ∈ P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n) ↔
      ∃ i < 4 ^ n, xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 ∧
        z ∈ P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) :=
  mem_XPseqCode_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₁pos hD₁diff hD₁nomin
    hUnion1 (XFold_four_pow_found P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 n) z

end XPseqCodeUnconditional

/-! ## 8.12(d)(4)(d): `YPseqCode`, the code-level `Y`-side union fold

Symmetric to `(d)(4)(c)`'s `XPseqCode`, but genuinely harder in one respect (matching
`Exercise812c.lean`'s own `YPseq` docstring): `ySubStep`'s inputs already depend on position `n`'s
own `X`-sub-step bit, so the half-step atom needs an *extra* free bit `bx`, and the resulting fold
is a union over *two* indices (`i < 4ⁿ` and `bx ∈ {0,1}`), not one. Rather than combine `i`/`bx`
into a single `2·4ⁿ`-element fold, this is built as an **outer `2`-way union of two inner `4ⁿ`-folds**
(`YFoldInner n 0 _`, `YFoldInner n 1 _`, one per literal value of `bx`) via a new, reusable
`combineFound2` helper — simpler than threading `bx` through the recursion state itself, since
`Nat.Primrec.prec` already needs `n` held fixed as its own outer parameter, and pairing `bx`
alongside it costs nothing. -/

/-- **Combine two `(found, code)` packed fold results into one**: union their codes via `hUnion`
when both found something, and simply propagate whichever single side found something otherwise
(mirroring `XFoldStep`/`YFoldStep`'s own "skip junk, else union" shape one level up). Generic in any
`IsComputableUnion`, reused below for `YPseqCode`'s "outer 2-way union" of its two `bx`-fixed inner
folds. -/
noncomputable def combineFound2 {γ : Type*} {W : NeighborhoodSystem γ}
    {Q : ComputablePresentation W} (hUnion : IsComputableUnion Q) (r0 r1 : ℕ) : ℕ :=
  selectFn r0.unpair.1
    (selectFn r1.unpair.1 (Nat.pair 1 (hUnion.unionIdx r0.unpair.2 r1.unpair.2)) r0)
    r1

theorem primrec_combineFound2 {γ : Type*} {W : NeighborhoodSystem γ}
    {Q : ComputablePresentation W} (hUnion : IsComputableUnion Q) :
    Nat.Primrec (fun t : ℕ => combineFound2 hUnion t.unpair.1 t.unpair.2) := by
  have h0 : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have h1 : Nat.Primrec (fun t : ℕ => t.unpair.2) := Nat.Primrec.right
  have hf0 : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.1) := Nat.Primrec.left.comp h0
  have hf1 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp h1
  have hv0 : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.2) := Nat.Primrec.right.comp h0
  have hv1 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) := Nat.Primrec.right.comp h1
  have hunion : Nat.Primrec
      (fun t : ℕ => hUnion.unionIdx t.unpair.1.unpair.2 t.unpair.2.unpair.2) :=
    (hUnion.unionIdx_primrec.comp (hv0.pair hv1)).of_eq
      fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hinner : Nat.Primrec (fun t : ℕ => selectFn t.unpair.2.unpair.1
      (Nat.pair 1 (hUnion.unionIdx t.unpair.1.unpair.2 t.unpair.2.unpair.2)) t.unpair.1) :=
    primrec_selectFn hf1 ((Nat.Primrec.const 1).pair hunion) h0
  exact (primrec_selectFn hf0 hinner h1).of_eq fun t => by unfold combineFound2; simp only []

theorem combineFound2_found_le_one {γ : Type*} {W : NeighborhoodSystem γ}
    {Q : ComputablePresentation W} (hUnion : IsComputableUnion Q) {r0 r1 : ℕ}
    (h0 : r0.unpair.1 ≤ 1) (h1 : r1.unpair.1 ≤ 1) :
    (combineFound2 hUnion r0 r1).unpair.1 ≤ 1 := by
  unfold combineFound2
  rcases Nat.eq_zero_or_pos r0.unpair.1 with hr0 | hr0
  · rw [hr0, selectFn_zero]; exact h1
  · rw [show r0.unpair.1 = 1 from by omega, selectFn_one]
    rcases Nat.eq_zero_or_pos r1.unpair.1 with hr1 | hr1
    · rw [hr1, selectFn_zero]; exact h0
    · rw [show r1.unpair.1 = 1 from by omega, selectFn_one, unpair_pair_fst]

theorem combineFound2_found_iff {γ : Type*} {W : NeighborhoodSystem γ}
    {Q : ComputablePresentation W} (hUnion : IsComputableUnion Q) {r0 r1 : ℕ}
    (h0 : r0.unpair.1 ≤ 1) (h1 : r1.unpair.1 ≤ 1) :
    (combineFound2 hUnion r0 r1).unpair.1 = 1 ↔ r0.unpair.1 = 1 ∨ r1.unpair.1 = 1 := by
  unfold combineFound2
  rcases Nat.eq_zero_or_pos r0.unpair.1 with hr0 | hr0
  · rw [hr0, selectFn_zero]; omega
  · rw [show r0.unpair.1 = 1 from by omega, selectFn_one]
    rcases Nat.eq_zero_or_pos r1.unpair.1 with hr1 | hr1
    · rw [hr1, selectFn_zero]; omega
    · rw [show r1.unpair.1 = 1 from by omega, selectFn_one, unpair_pair_fst]; omega

theorem combineFound2_mem_of_found {γ : Type*} {W : NeighborhoodSystem γ}
    {Q : ComputablePresentation W} (hpos : W.IsPositive) (hdiff : W.DiffClosed)
    (hnomin : W.NoMinimal) (hUnion : IsComputableUnion Q) {r0 r1 : ℕ}
    (h0 : r0.unpair.1 ≤ 1) (h1 : r1.unpair.1 ≤ 1)
    (hmem0 : r0.unpair.1 = 1 → W.mem (Q.X r0.unpair.2))
    (hmem1 : r1.unpair.1 = 1 → W.mem (Q.X r1.unpair.2)) :
    (combineFound2 hUnion r0 r1).unpair.1 = 1 →
      W.mem (Q.X (combineFound2 hUnion r0 r1).unpair.2) := by
  unfold combineFound2
  rcases Nat.eq_zero_or_pos r0.unpair.1 with hr0 | hr0
  · rw [hr0, selectFn_zero]
    exact hmem1
  · rw [show r0.unpair.1 = 1 from by omega, selectFn_one]
    have hmem0' := hmem0 (by omega)
    rcases Nat.eq_zero_or_pos r1.unpair.1 with hr1 | hr1
    · rw [hr1, selectFn_zero]
      exact fun _ => hmem0'
    · rw [show r1.unpair.1 = 1 from by omega, selectFn_one, unpair_pair_snd]
      intro _
      have hmem1' := hmem1 (by omega)
      have hex : ∃ k, Q.X k = Q.X r0.unpair.2 ∪ Q.X r1.unpair.2 :=
        Q.surj (NeighborhoodSystem.mem_union_of_mem hpos hdiff hnomin hmem0' hmem1')
      rw [hUnion.unionIdx_spec hex]
      exact NeighborhoodSystem.mem_union_of_mem hpos hdiff hnomin hmem0' hmem1'

theorem combineFound2_mem_iff {γ : Type*} {W : NeighborhoodSystem γ}
    {Q : ComputablePresentation W} (hpos : W.IsPositive) (hdiff : W.DiffClosed)
    (hnomin : W.NoMinimal) (hUnion : IsComputableUnion Q) {r0 r1 : ℕ}
    (h0 : r0.unpair.1 ≤ 1) (h1 : r1.unpair.1 ≤ 1)
    (hmem0 : r0.unpair.1 = 1 → W.mem (Q.X r0.unpair.2))
    (hmem1 : r1.unpair.1 = 1 → W.mem (Q.X r1.unpair.2))
    (hfound : (combineFound2 hUnion r0 r1).unpair.1 = 1) (z : γ) :
    z ∈ Q.X (combineFound2 hUnion r0 r1).unpair.2 ↔
      (r0.unpair.1 = 1 ∧ z ∈ Q.X r0.unpair.2) ∨ (r1.unpair.1 = 1 ∧ z ∈ Q.X r1.unpair.2) := by
  unfold combineFound2 at hfound ⊢
  rcases Nat.eq_zero_or_pos r0.unpair.1 with hr0 | hr0
  · rw [hr0, selectFn_zero] at hfound ⊢
    constructor
    · intro hz; exact Or.inr ⟨hfound, hz⟩
    · rintro (⟨h, -⟩ | ⟨-, hz⟩)
      · omega
      · exact hz
  · rw [show r0.unpair.1 = 1 from by omega, selectFn_one] at hfound ⊢
    have hmem0' := hmem0 (by omega)
    rcases Nat.eq_zero_or_pos r1.unpair.1 with hr1 | hr1
    · rw [hr1, selectFn_zero] at hfound ⊢
      constructor
      · intro hz; exact Or.inl ⟨by omega, hz⟩
      · rintro (⟨-, hz⟩ | ⟨h, -⟩)
        · exact hz
        · omega
    · rw [show r1.unpair.1 = 1 from by omega, selectFn_one, unpair_pair_snd]
      have hmem1' := hmem1 (by omega)
      have hex : ∃ k, Q.X k = Q.X r0.unpair.2 ∪ Q.X r1.unpair.2 :=
        Q.surj (NeighborhoodSystem.mem_union_of_mem hpos hdiff hnomin hmem0' hmem1')
      rw [hUnion.unionIdx_spec hex, Set.mem_union]
      constructor
      · rintro (hz | hz)
        · exact Or.inl ⟨by omega, hz⟩
        · exact Or.inr ⟨by omega, hz⟩
      · rintro (⟨-, hz⟩ | ⟨-, hz⟩)
        · exact Or.inl hz
        · exact Or.inr hz

section YPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hUnion0 : IsComputableUnion P₀)

/-- **The `Y`-side half-step atom's packed state** at depth `n`, index `i`, and free `X`-sub-step
bit `bx`: run `xSubStep` first at bit `bx` (arbitrary — `YPseq`'s classical definition
(`Exercise812c.lean`) unions over *both* `δ' : Fin n → Bool × Bool` and a free `bx : Bool` for
position `n`'s own `X`-sub-step bit, since `yStep`'s own inputs already depend on it), then
`ySubStep` with its own bit forced to `1` (the `"+"`/`true` branch). -/
noncomputable def yPseqAtomState (n i bx : ℕ) : ℕ :=
  ySubStep P₀ P₁ hDiff1 splitY hSplitY (Nat.pair n (Nat.pair 1
    (xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair bx
      (packState2 (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
        (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
        (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)))))))

/-- The half-step atom's `D₀`-side index (`ySubStep`'s `"+"`/pos branch is the *split* side, since
`ySubStep` refines `D₁` directly and `D₀` via `hSplitY`). -/
noncomputable def yPseqAtomIdx (n i bx : ℕ) : ℕ :=
  stateIdx0 (yPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx)

/-- The half-step atom's junk flag. -/
noncomputable def yPseqAtomJunk (n i bx : ℕ) : ℕ :=
  stateJunk (yPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx)

theorem primrec_yPseqAtomState : Nat.Primrec
    (fun t : ℕ => yPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) := by
  have hn : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hi : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hbx : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hni : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 t.unpair.2.unpair.1) := hn.pair hi
  have hidx0 : Nat.Primrec (fun t : ℕ =>
      atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
        t.unpair.2.unpair.1) :=
    ((primrec_atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp hni).of_eq
      fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hidx1 : Nat.Primrec (fun t : ℕ =>
      atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
        t.unpair.2.unpair.1) :=
    ((primrec_atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp hni).of_eq
      fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hjunk : Nat.Primrec (fun t : ℕ =>
      atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
        t.unpair.2.unpair.1) :=
    ((primrec_atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp hni).of_eq
      fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hpacked : Nat.Primrec (fun t : ℕ => packState2
      (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
        t.unpair.2.unpair.1)
      (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
        t.unpair.2.unpair.1)
      (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
        t.unpair.2.unpair.1)) :=
    (hidx0.pair (hidx1.pair hjunk)).of_eq fun _ => rfl
  have hxinner : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.2.unpair.2 (packState2
      (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
        t.unpair.2.unpair.1)
      (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
        t.unpair.2.unpair.1)
      (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
        t.unpair.2.unpair.1))) :=
    hbx.pair hpacked
  have hxarg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 (Nat.pair t.unpair.2.unpair.2
      (packState2 (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
          t.unpair.2.unpair.1)
        (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
          t.unpair.2.unpair.1)
        (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
          t.unpair.2.unpair.1)))) :=
    hn.pair hxinner
  have hxstep : Nat.Primrec (fun t : ℕ => xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair
      t.unpair.1 (Nat.pair t.unpair.2.unpair.2 (packState2
        (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
          t.unpair.2.unpair.1)
        (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
          t.unpair.2.unpair.1)
        (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
          t.unpair.2.unpair.1))))) :=
    (primrec_xSubStep P₀ P₁ hDiff0 splitX hSplitX).comp hxarg
  have hystep_arg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 (Nat.pair 1
      (xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair t.unpair.1 (Nat.pair t.unpair.2.unpair.2
        (packState2 (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
            t.unpair.2.unpair.1)
          (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
            t.unpair.2.unpair.1)
          (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
            t.unpair.2.unpair.1))))))) :=
    hn.pair ((Nat.Primrec.const 1).pair hxstep)
  exact ((primrec_ySubStep P₀ P₁ hDiff1 splitY hSplitY).comp hystep_arg).of_eq fun _ => rfl

theorem primrec_yPseqAtomIdx : Nat.Primrec
    (fun t : ℕ => yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) :=
  (primrec_stateIdx0.comp (primrec_yPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
    hSplitY)).of_eq fun _ => rfl

theorem primrec_yPseqAtomJunk : Nat.Primrec
    (fun t : ℕ => yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) :=
  (primrec_stateJunk.comp (primrec_yPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
    hSplitY)).of_eq fun _ => rfl

theorem yPseqAtomJunk_le_one {bx : ℕ} (hbx : bx ≤ 1) (n i : ℕ) :
    yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx ≤ 1 := by
  unfold yPseqAtomJunk yPseqAtomState
  rw [ySubStep_junk_eq, selectFn_one]
  refine selectFn_le_one ?_ (le_refl 1) (emptyInterDec_le_one P₁ _)
  rw [xSubStep_junk_eq, stateJunk_packState2]
  exact selectFn_le_one (atomPairJunk_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY i n)
    (le_refl 1) (selectFn_le_one hbx (emptyInterDec_le_one P₀ _) (emptyDiffDec_le_one P₀ hDiff0 _))

theorem yPseqAtomJunk_zero_or_one {bx : ℕ} (hbx : bx ≤ 1) (n i : ℕ) :
    yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx = 0 ∨
      yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx = 1 := by
  have := yPseqAtomJunk_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hbx n i
  omega

/-- **The half-step atom is always genuine** on `D₀`'s side, regardless of junk status. -/
theorem yPseqAtomIdx_mem (n i bx : ℕ) :
    D₀.mem (P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx)) :=
  P₀.mem_X _

/-- One step of the depth-`n`, bit-`bx` union fold over `i < N`: identical shape to `XFoldStep`,
folding via `(d)(4)(a)`'s `hUnion0.unionIdx` on `D₀`'s side instead of `D₁`'s. -/
noncomputable def YFoldStep (w : ℕ) : ℕ :=
  let n := w.unpair.1.unpair.1
  let bx := w.unpair.1.unpair.2
  let i := w.unpair.2.unpair.1
  let acc := w.unpair.2.unpair.2
  selectFn (yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx) acc
    (selectFn acc.unpair.1
      (Nat.pair 1 (hUnion0.unionIdx acc.unpair.2
        (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx)))
      (Nat.pair 1 (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx)))

theorem YFoldStep_eq (n bx i acc : ℕ) :
    YFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
        (Nat.pair (Nat.pair n bx) (Nat.pair i acc)) =
      selectFn (yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx) acc
        (selectFn acc.unpair.1
          (Nat.pair 1 (hUnion0.unionIdx acc.unpair.2
            (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx)))
          (Nat.pair 1 (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx))) := by
  unfold YFoldStep
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem primrec_YFoldStep :
    Nat.Primrec (YFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0) := by
  have hn : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.left
  have hbx : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.left
  have hi : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hnibx : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.1.unpair.1
      (Nat.pair w.unpair.2.unpair.1 w.unpair.1.unpair.2)) := hn.pair (hi.pair hbx)
  have hjunk : Nat.Primrec (fun w : ℕ =>
      yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY w.unpair.1.unpair.1
        w.unpair.2.unpair.1 w.unpair.1.unpair.2) :=
    ((primrec_yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp hnibx).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hidx : Nat.Primrec (fun w : ℕ =>
      yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY w.unpair.1.unpair.1
        w.unpair.2.unpair.1 w.unpair.1.unpair.2) :=
    ((primrec_yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp hnibx).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hfound : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp hacc
  have hval : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp hacc
  have hunion : Nat.Primrec (fun w : ℕ => hUnion0.unionIdx w.unpair.2.unpair.2.unpair.2
      (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY w.unpair.1.unpair.1
        w.unpair.2.unpair.1 w.unpair.1.unpair.2)) :=
    (hUnion0.unionIdx_primrec.comp (hval.pair hidx)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hinner : Nat.Primrec (fun w : ℕ => selectFn w.unpair.2.unpair.2.unpair.1
      (Nat.pair 1 (hUnion0.unionIdx w.unpair.2.unpair.2.unpair.2
        (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY w.unpair.1.unpair.1
          w.unpair.2.unpair.1 w.unpair.1.unpair.2)))
      (Nat.pair 1 (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        w.unpair.1.unpair.1 w.unpair.2.unpair.1 w.unpair.1.unpair.2))) :=
    primrec_selectFn hfound ((Nat.Primrec.const 1).pair hunion) ((Nat.Primrec.const 1).pair hidx)
  exact (primrec_selectFn hjunk hacc hinner).of_eq fun w => by unfold YFoldStep; simp only []

/-- The depth-`n`, bit-`bx` union fold over `i < N`, starting from `(0, 0)`. `n`/`bx` are held
fixed across the recursion by packing them together as `Nat.Primrec.prec`'s own outer parameter. -/
noncomputable def YFoldInner (n bx N : ℕ) : ℕ :=
  N.rec (Nat.pair 0 0) (fun i acc => YFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hUnion0 (Nat.pair (Nat.pair n bx) (Nat.pair i acc)))

theorem YFoldInner_zero (n bx : ℕ) :
    YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx 0 =
      Nat.pair 0 0 := rfl

theorem YFoldInner_succ (n bx N : ℕ) :
    YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx (N + 1) =
      YFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
        (Nat.pair (Nat.pair n bx) (Nat.pair N (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX
          splitY hSplitY hUnion0 n bx N))) := rfl

/-- **Auxiliary single-argument-`z` repackaging of `YFoldInner`**, matching `Nat.Primrec.prec`'s
own shape exactly (`z := nb` used *directly*, with no `Nat.pair`/`unpair` round-trip needed for
`rfl` to see through) — mirroring `XFold`'s own successful pattern, where `z := n` needed no
repackaging at all since `XFold` has only one "held-fixed" parameter. `YFoldInner` needs *two*
(`n`, `bx`), so this auxiliary exists purely to keep `primrec_YFoldInner`'s own proof cheap: the
`Nat.pair`/`unpair` round-trip (`pair_unpair`, *not* definitionally `rfl` — it needs the `Nat.sqrt`
case split) is pushed into `unpair_pair_fst`/`_snd`-driven `simp`, not the kernel's `whnf`. -/
noncomputable def YFoldInnerPair (nb N : ℕ) : ℕ :=
  N.rec (Nat.pair 0 0) (fun i acc => YFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hUnion0 (Nat.pair nb (Nat.pair i acc)))

theorem primrec_YFoldInnerPair : Nat.Primrec
    (fun t : ℕ => YFoldInnerPair P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
      t.unpair.1 t.unpair.2) :=
  (Nat.Primrec.prec (Nat.Primrec.const (Nat.pair 0 0))
    (primrec_YFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0)).of_eq
    fun _ => rfl

theorem YFoldInner_eq_pair (n bx N : ℕ) :
    YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N =
      YFoldInnerPair P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
        (Nat.pair n bx) N := rfl

theorem primrec_YFoldInner : Nat.Primrec
    (fun t : ℕ => YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
      t.unpair.1.unpair.1 t.unpair.1.unpair.2 t.unpair.2) := by
  have h1 : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1.unpair.1 t.unpair.1.unpair.2) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.left)
  have h2 : Nat.Primrec (fun t : ℕ => Nat.pair
      (Nat.pair t.unpair.1.unpair.1 t.unpair.1.unpair.2) t.unpair.2) :=
    h1.pair Nat.Primrec.right
  exact ((primrec_YFoldInnerPair P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0).comp
    h2).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
      exact (YFoldInner_eq_pair P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
        t.unpair.1.unpair.1 t.unpair.1.unpair.2 t.unpair.2).symm

theorem YFoldInner_found_le_one {bx : ℕ} (hbx : bx ≤ 1) (n : ℕ) :
    ∀ N, (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N).unpair.1
      ≤ 1 := by
  intro N
  induction N with
  | zero => simp [YFoldInner_zero]
  | succ N ih =>
    rw [YFoldInner_succ, YFoldStep_eq]
    rcases yPseqAtomJunk_zero_or_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hbx n N with
      h0 | h1
    · rw [h0, selectFn_zero]
      rcases Nat.eq_zero_or_pos
          (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N).unpair.1
        with hf0 | hfpos
      · rw [show (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
          ).unpair.1 = 0 from hf0, selectFn_zero, unpair_pair_fst]
      · rw [show (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
          ).unpair.1 = 1 from by omega, selectFn_one, unpair_pair_fst]
    · rw [h1, selectFn_one]; exact ih

/-- **The "found" flag exactly tracks existence of a non-junk half-step atom below `N`.** -/
theorem YFoldInner_found_iff {bx : ℕ} (hbx : bx ≤ 1) (n : ℕ) :
    ∀ N, (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N).unpair.1 = 1
      ↔ ∃ i < N, yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx = 0 := by
  intro N
  induction N with
  | zero => simp [YFoldInner_zero]
  | succ N ih =>
    rw [YFoldInner_succ, YFoldStep_eq]
    rcases yPseqAtomJunk_zero_or_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hbx n N with
      h0 | h1
    · rw [h0, selectFn_zero]
      have hval1 : (selectFn
          (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N).unpair.1
          (Nat.pair 1 (hUnion0.unionIdx
            (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N).unpair.2
            (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N bx)))
          (Nat.pair 1 (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N bx))
          ).unpair.1 = 1 := by
        have hle := YFoldInner_found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
          hUnion0 hbx n N
        rcases Nat.eq_zero_or_pos
            (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N).unpair.1
          with hf | hf
        · rw [show (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
            ).unpair.1 = 0 from hf, selectFn_zero, unpair_pair_fst]
        · rw [show (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
            ).unpair.1 = 1 from by omega, selectFn_one, unpair_pair_fst]
      rw [hval1]
      exact ⟨fun _ => ⟨N, Nat.lt_succ_self N, h0⟩, fun _ => rfl⟩
    · rw [h1, selectFn_one, ih]
      constructor
      · rintro ⟨i, hi, hie⟩; exact ⟨i, Nat.lt_succ_of_lt hi, hie⟩
      · rintro ⟨i, hi, hie⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact ⟨i, hi', hie⟩
        · exact absurd hie (by omega)

include hD₀pos hD₀diff hD₀nomin in
/-- **Once "found", the running union's code is always `D₀`-genuine.** Exactly mirrors
`XFold_mem_of_found`, with `hUnion0`/`D₀` in place of `hUnion1`/`D₁`. -/
theorem YFoldInner_mem_of_found {bx : ℕ} (hbx : bx ≤ 1) (n : ℕ) :
    ∀ N, (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N).unpair.1 = 1
      → D₀.mem (P₀.X (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
        n bx N).unpair.2) := by
  intro N
  induction N with
  | zero => intro h; simp [YFoldInner_zero] at h
  | succ N ih =>
    intro hfound1
    rw [YFoldInner_succ, YFoldStep_eq] at hfound1 ⊢
    rcases yPseqAtomJunk_zero_or_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hbx n N with
      h0 | h1
    · rw [h0, selectFn_zero] at hfound1 ⊢
      have hle := YFoldInner_found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
        hbx n N
      rcases Nat.eq_zero_or_pos
          (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N).unpair.1
        with hf0 | hfpos
      · rw [show (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
          ).unpair.1 = 0 from hf0, selectFn_zero, unpair_pair_snd]
        exact yPseqAtomIdx_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N bx
      · have hf1 : (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
            ).unpair.1 = 1 := by omega
        rw [hf1, selectFn_one, unpair_pair_snd]
        have hprevmem := ih hf1
        have hnewmem := yPseqAtomIdx_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N bx
        have hex : ∃ k, P₀.X k =
            P₀.X (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
              ).unpair.2 ∪
              P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N bx) :=
          P₀.surj (NeighborhoodSystem.mem_union_of_mem hD₀pos hD₀diff hD₀nomin hprevmem hnewmem)
        rw [hUnion0.unionIdx_spec hex]
        exact NeighborhoodSystem.mem_union_of_mem hD₀pos hD₀diff hD₀nomin hprevmem hnewmem
    · rw [h1, selectFn_one] at hfound1 ⊢
      exact ih hfound1

include hD₀pos hD₀diff hD₀nomin in
/-- **The membership form of `YFoldInner`'s correctness**, exactly mirroring `XFold_mem_iff`. -/
theorem YFoldInner_mem_iff {bx : ℕ} (hbx : bx ≤ 1) (n : ℕ) :
    ∀ N, (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N).unpair.1 = 1
      → ∀ z : α, z ∈ P₀.X (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
          n bx N).unpair.2 ↔
        ∃ i < N, yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx = 0 ∧
          z ∈ P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx) := by
  intro N
  induction N with
  | zero => intro h; simp [YFoldInner_zero] at h
  | succ N ih =>
    intro hfound1 z
    rw [YFoldInner_succ, YFoldStep_eq] at hfound1 ⊢
    rcases yPseqAtomJunk_zero_or_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hbx n N with
      h0 | h1
    · rw [h0, selectFn_zero] at hfound1 ⊢
      have hle := YFoldInner_found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
        hbx n N
      rcases Nat.eq_zero_or_pos
          (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N).unpair.1
        with hf0 | hfpos
      · rw [show (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
          ).unpair.1 = 0 from hf0, selectFn_zero, unpair_pair_snd]
        constructor
        · intro hz; exact ⟨N, Nat.lt_succ_self N, h0, hz⟩
        · rintro ⟨i, hi, hie, hz⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact absurd ((YFoldInner_found_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
              hUnion0 hbx n N).mpr ⟨i, hi', hie⟩) (by rw [hf0]; omega)
          · exact hz
      · have hf1 : (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
            ).unpair.1 = 1 := by omega
        rw [hf1, selectFn_one, unpair_pair_snd]
        have hprevmem := YFoldInner_mem_of_found P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
          hD₀pos hD₀diff hD₀nomin hUnion0 hbx n N hf1
        have hnewmem := yPseqAtomIdx_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N bx
        have hex : ∃ k, P₀.X k =
            P₀.X (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
              ).unpair.2 ∪
              P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N bx) :=
          P₀.surj (NeighborhoodSystem.mem_union_of_mem hD₀pos hD₀diff hD₀nomin hprevmem hnewmem)
        rw [hUnion0.unionIdx_spec hex, Set.mem_union, ih hf1 z]
        constructor
        · rintro (⟨i, hi, hie, hz⟩ | hz)
          · exact ⟨i, Nat.lt_succ_of_lt hi, hie, hz⟩
          · exact ⟨N, Nat.lt_succ_self N, h0, hz⟩
        · rintro ⟨i, hi, hie, hz⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact Or.inl ⟨i, hi', hie, hz⟩
          · exact Or.inr hz
    · rw [h1, selectFn_one] at hfound1 ⊢
      rw [ih hfound1 z]
      constructor
      · rintro ⟨i, hi, hie, hz⟩; exact ⟨i, Nat.lt_succ_of_lt hi, hie, hz⟩
      · rintro ⟨i, hi, hie, hz⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact ⟨i, hi', hie, hz⟩
        · exact absurd hie (by omega)

/-- **`YPseqCode`, the code-level analogue of `Exercise812c.lean`'s `YPseq`.** The outer `2`-way
`combineFound2` union of the two `bx`-fixed inner folds `YFoldInner n 0 (4ⁿ)`/`YFoldInner n 1 (4ⁿ)`. -/
noncomputable def YPseqCode (n : ℕ) : ℕ :=
  (combineFound2 hUnion0
    (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 0 (4 ^ n))
    (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 1 (4 ^ n))).unpair.2

theorem primrec_YPseqCode : Nat.Primrec
    (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0) := by
  have h4n : Nat.Primrec (fun n : ℕ => 4 ^ n) := primrec_pow₂ (Nat.Primrec.const 4) Nat.Primrec.id
  have hr0 : Nat.Primrec (fun n : ℕ =>
      YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 0 (4 ^ n)) := by
    have harg : Nat.Primrec (fun n : ℕ => Nat.pair (Nat.pair n 0) (4 ^ n)) :=
      (Nat.Primrec.id.pair (Nat.Primrec.const 0)).pair h4n
    exact ((primrec_YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0).comp
      harg).of_eq fun n => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hr1 : Nat.Primrec (fun n : ℕ =>
      YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 1 (4 ^ n)) := by
    have harg : Nat.Primrec (fun n : ℕ => Nat.pair (Nat.pair n 1) (4 ^ n)) :=
      (Nat.Primrec.id.pair (Nat.Primrec.const 1)).pair h4n
    exact ((primrec_YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0).comp
      harg).of_eq fun n => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hcomb : Nat.Primrec (fun n : ℕ => combineFound2 hUnion0
      (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 0 (4 ^ n))
      (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 1 (4 ^ n))) :=
    ((primrec_combineFound2 hUnion0).comp (hr0.pair hr1)).of_eq
      fun n => by simp only [unpair_pair_fst, unpair_pair_snd]
  exact (Nat.Primrec.right.comp hcomb).of_eq fun _ => rfl

include hD₀pos hD₀diff hD₀nomin in
/-- **Once "found" at `N = 4ⁿ`** (on either `bx`-branch), **`YPseqCode n` is `D₀`-genuine.** -/
theorem YPseqCode_mem {n : ℕ}
    (hfound : (combineFound2 hUnion0
      (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 0 (4 ^ n))
      (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 1 (4 ^ n))
      ).unpair.1 = 1) :
    D₀.mem (P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n)) :=
  combineFound2_mem_of_found hD₀pos hD₀diff hD₀nomin hUnion0
    (YFoldInner_found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
      (Nat.zero_le 1) n (4 ^ n))
    (YFoldInner_found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
      (le_refl 1) n (4 ^ n))
    (YFoldInner_mem_of_found P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hUnion0 (Nat.zero_le 1) n (4 ^ n))
    (YFoldInner_mem_of_found P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hUnion0 (le_refl 1) n (4 ^ n))
    hfound

include hD₀pos hD₀diff hD₀nomin in
/-- **The closed-form membership characterization of `YPseqCode`, conditional on "found" at
`N = 4ⁿ`**: a point lies in `P₀.X (YPseqCode n)` iff it lies in some genuine (non-junk) half-step
atom `yPseqAtomIdx n i bx`, for `i < 4ⁿ` on *either* `bx`-branch. -/
theorem mem_YPseqCode_iff {n : ℕ}
    (hfound : (combineFound2 hUnion0
      (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 0 (4 ^ n))
      (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 1 (4 ^ n))
      ).unpair.1 = 1) (z : α) :
    z ∈ P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) ↔
      (∃ i < 4 ^ n, yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i 0 = 0 ∧
        z ∈ P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i 0)) ∨
      (∃ i < 4 ^ n, yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i 1 = 0 ∧
        z ∈ P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i 1)) := by
  have hle0 := YFoldInner_found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
    (Nat.zero_le 1) n (4 ^ n)
  have hle1 := YFoldInner_found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
    (le_refl 1) n (4 ^ n)
  have hmem0 := YFoldInner_mem_of_found P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hUnion0 (Nat.zero_le 1) n (4 ^ n)
  have hmem1 := YFoldInner_mem_of_found P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hUnion0 (le_refl 1) n (4 ^ n)
  have heq : YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n =
      (combineFound2 hUnion0
        (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 0 (4 ^ n))
        (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 1 (4 ^ n))
        ).unpair.2 := rfl
  rw [heq, combineFound2_mem_iff hD₀pos hD₀diff hD₀nomin hUnion0 hle0 hle1 hmem0 hmem1 hfound z]
  constructor
  · rintro (⟨hf0, hz⟩ | ⟨hf1, hz⟩)
    · exact Or.inl ((YFoldInner_mem_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hUnion0 (Nat.zero_le 1) n (4 ^ n) hf0 z).mp hz)
    · exact Or.inr ((YFoldInner_mem_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hUnion0 (le_refl 1) n (4 ^ n) hf1 z).mp hz)
  · rintro (⟨i, hi, hie, hz⟩ | ⟨i, hi, hie, hz⟩)
    · have hf0 : (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 0 (4 ^ n)
          ).unpair.1 = 1 :=
        (YFoldInner_found_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
          (Nat.zero_le 1) n (4 ^ n)).mpr ⟨i, hi, hie⟩
      exact Or.inl ⟨hf0, (YFoldInner_mem_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hD₀nomin hUnion0 (Nat.zero_le 1) n (4 ^ n) hf0 z).mpr ⟨i, hi, hie, hz⟩⟩
    · have hf1 : (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 1 (4 ^ n)
          ).unpair.1 = 1 :=
        (YFoldInner_found_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
          (le_refl 1) n (4 ^ n)).mpr ⟨i, hi, hie⟩
      exact Or.inr ⟨hf1, (YFoldInner_mem_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hD₀nomin hUnion0 (le_refl 1) n (4 ^ n) hf1 z).mpr ⟨i, hi, hie, hz⟩⟩

end YPseqCode

/-! ## 8.12(d)(4)(d)(vi): `YPseqCode`'s "found" flag is unconditionally `1`

Mirrors `XPseqCodeUnconditional`, but doubled over `bx`. The extra wrinkle beyond `(c)(vi)`'s
template: `(d)(iv)`'s covering fact (`exists_atomPairG_deltaPair_inter_Yn_ne_empty`) only pins down
a non-trivial intersection of `B := (atomPairG (deltaPair i) n).2` itself with `P₁.X n` — *before*
any half-step — whereas `yPseqAtomJunk n i bx = 0`'s witnessing genuinely needs a non-trivial
intersection of `B`'s **half-step-`bx` split piece** `(xStepG splitX A B (P₀.X n) bx).2` with
`P₁.X n`. The bridge: `xStepG_snd_union` (`(d)(i)`) says these two split pieces (`bx = true`/
`false`) reunion to exactly `B`, so `B ∩ P₁.X n ≠ ∅` forces *at least one* of them to meet `P₁.X n`
non-trivially (a `Set.union_inter_distrib_right` chase) — no need to know *which* `bx` in advance,
matching `arxiv.md`'s own scoping prediction exactly. -/

section YPseqCodeUnconditional

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty) (hUnion0 : IsComputableUnion P₀)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
/-- **The half-step-`bx` atom is non-junk, given the classical split piece meets `P₁.X n`.** The
one-bit-generic engine behind `yPseqAtomJunk_exists_zero`: given the incoming depth-`n` state is
non-junk (`hjunk0`) and, for a *chosen* bit `b`, both the direct-refine piece `A1(b) ≠ ∅` (`hne`)
and the split piece meets `P₁.X n` non-trivially (`hinter`), the half-step atom
`yPseqAtomJunk n i (if b then 1 else 0)` is `0`. Chases `xSubStep`'s own junk formula down to
`emptyInterDec`/`emptyDiffDec` (`P₀`-side, from `hne` via `atomPairCodeState_correct`'s forward
identification) to get `xSubStep`'s output non-junk, then `xSubStep_correct` to identify its
`D₁`-side index with the classical split piece, then the same `emptyInterDec` reading (`P₁`-side,
from `hinter`) collapses `ySubStep`'s own forced-`"+"` junk check to `0`. -/
private theorem yPseqAtomJunk_eq_zero_of_bit {i n : ℕ}
    (hjunk0 : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0) (b : Bool)
    (hne : (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b).1 ≠ ∅)
    (hinter : (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b).2 ∩ P₁.X n ≠ ∅) :
    yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i (if b then 1 else 0) = 0 := by
  obtain ⟨hidx0, hidx1⟩ := atomPairCodeState_correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
    hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne i n
    hjunk0
  have hxc0 : selectFn (if b then 1 else 0)
      (emptyInterDec P₀ (Nat.pair (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        n i) n))
      (emptyDiffDec P₀ hDiff0 (Nat.pair (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
        hSplitY n i) n)) = 0 := by
    by_cases hb : b = true
    · simp only [xStepG, xyStep, hb, if_true] at hne
      have hne' : P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) ∩
          P₀.X n ≠ ∅ := by rw [hidx0]; exact hne
      simp only [hb, if_true, selectFn_one]
      by_contra hcon
      have hle := emptyInterDec_le_one P₀ (Nat.pair
        (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) n)
      have h1 : emptyInterDec P₀ (Nat.pair
          (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) n) = 1 := by omega
      exact hne' ((emptyInterDec_eq_one_iff P₀ hD₀pos hD₀nomin _ _).mp h1)
    · simp only [xStepG, xyStep, hb, Bool.false_eq_true, if_false] at hne
      have hne' : P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) \
          P₀.X n ≠ ∅ := by rw [hidx0]; exact hne
      simp only [hb, Bool.false_eq_true, if_false, selectFn_zero]
      by_contra hcon
      have hle := emptyDiffDec_le_one P₀ hDiff0 (Nat.pair
        (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) n)
      have h1 : emptyDiffDec P₀ hDiff0 (Nat.pair
          (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) n) = 1 := by omega
      exact hne' ((emptyDiffDec_eq_one_iff P₀ hDiff0 hD₀diff hD₀nomin _ _).mp h1)
  set s0 := packState2
      (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
      (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
      (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) with hs0def
  have hidx0' : P₀.X (stateIdx0 s0) =
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1 := by
    rw [hs0def, stateIdx0_packState2]; exact hidx0
  have hidx1' : P₁.X (stateIdx1 s0) =
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 := by
    rw [hs0def, stateIdx1_packState2]; exact hidx1
  set s1 := xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair (if b then 1 else 0) s0))
    with hs1def
  have hxnonjunk : stateJunk s1 = 0 := by
    rw [hs1def, xSubStep_junk_eq, hs0def, stateJunk_packState2, stateIdx0_packState2, hjunk0,
      selectFn_zero]
    exact hxc0
  obtain ⟨hAB, -, hBmem⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n
  obtain ⟨-, hxB1⟩ := xSubStep_correct P₀ P₁ hDiff0 splitX hSplitX hD₀pos hD₀diff hD₀nomin hxSplit
    hidx0' hidx1' hAB hBmem b hxnonjunk
  rw [← hs1def] at hxB1
  have hB1inter : P₁.X (stateIdx1 s1) ∩ P₁.X n ≠ ∅ := by rw [hxB1]; exact hinter
  have hyc0 : emptyInterDec P₁ (Nat.pair (stateIdx1 s1) n) = 0 := by
    by_contra hcon
    have hle := emptyInterDec_le_one P₁ (Nat.pair (stateIdx1 s1) n)
    have h1 : emptyInterDec P₁ (Nat.pair (stateIdx1 s1) n) = 1 := by omega
    exact hB1inter ((emptyInterDec_eq_one_iff P₁ hD₁pos hD₁nomin _ _).mp h1)
  unfold yPseqAtomJunk yPseqAtomState
  rw [← hs0def, ← hs1def, ySubStep_junk_eq, selectFn_one, hxnonjunk, selectFn_zero]
  exact hyc0

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
/-- **8.12(d)(4)(d)(vi), step 1: the unconditional "found" existential, doubled over `bx`.**
Combines `(d)(iv)`'s `exists_atomPairG_deltaPair_inter_Yn_ne_empty` with `xStepG_snd_union`
(`(d)(i)`) to locate a bit `bx ∈ {0, 1}` whose split piece meets `P₁.X n`, the `SplitSpec'`-level
dichotomy (`hxSplit`, applied directly rather than via the depth-crossing `atomPairG_invariant`)
to promote that to the direct-refine piece being non-empty, and
`yPseqAtomJunk_eq_zero_of_bit` to land the half-step atom's junk flag at `0`. -/
theorem yPseqAtomJunk_exists_zero (n : ℕ) :
    ∃ i < 4 ^ n, ∃ bx ≤ 1,
      yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx = 0 := by
  obtain ⟨i, hi, hBinter⟩ := exists_atomPairG_deltaPair_inter_Yn_ne_empty P₀ P₁ splitX splitY
    hD₀pos hD₀diff hxSplit hD₁pos hD₁diff hySplit hD₀mne hD₁mne hD₁nomin n
  have hBne : (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 ≠ ∅ := fun hB =>
    hBinter (by rw [hB]; simp)
  have hjunk0 : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 :=
    atomPairJunk_eq_zero_of_snd_ne_empty P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hBne
  obtain ⟨ihAB, ihA, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n
  have hunion := xStepG_snd_union hxSplit ihAB ihB (P₀.X n)
  rw [← hunion, Set.union_inter_distrib_right] at hBinter
  have hspec1 := hxSplit ihAB ihB (P₀.X n)
  have hex : (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) true).2 ∩
      P₁.X n ≠ ∅ ∨
      (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) false).2 ∩
      P₁.X n ≠ ∅ := by
    by_contra hcon
    push Not at hcon
    exact hBinter (by rw [hcon.1, hcon.2]; simp)
  rcases hex with hTinter | hFinter
  · have hTne : (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) true).2 ≠ ∅ :=
      fun h => hTinter (by rw [h]; simp)
    have hA1ne : (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) true).1 ≠ ∅ :=
      mt hspec1.2.2.1.mp hTne
    have hzero := yPseqAtomJunk_eq_zero_of_bit P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hjunk0 true
      hA1ne hTinter
    exact ⟨i, hi, 1, le_refl 1, hzero⟩
  · have hFne : (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) false).2 ≠ ∅ :=
      fun h => hFinter (by rw [h]; simp)
    have hA1ne : (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) false).1 ≠ ∅ :=
      mt hspec1.2.2.2.1.mp hFne
    have hzero := yPseqAtomJunk_eq_zero_of_bit P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hjunk0 false
      hA1ne hFinter
    exact ⟨i, hi, 0, Nat.zero_le 1, hzero⟩

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 in
/-- **Step 2: at least one of the two `bx`-fixed inner folds' "found" flag is `1` at `N = 4ⁿ`.** -/
theorem YFoldInner_or_found (n : ℕ) :
    (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 0 (4 ^ n)).unpair.1 = 1
      ∨ (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 1 (4 ^ n)
        ).unpair.1 = 1 := by
  obtain ⟨i, hi, bx, hbx, hzero⟩ := yPseqAtomJunk_exists_zero P₀ P₁ hDiff0 hDiff1 splitX hSplitX
    splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne n
  interval_cases bx
  · exact Or.inl ((YFoldInner_found_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
      (Nat.zero_le 1) n (4 ^ n)).mpr ⟨i, hi, hzero⟩)
  · exact Or.inr ((YFoldInner_found_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
      (le_refl 1) n (4 ^ n)).mpr ⟨i, hi, hzero⟩)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 in
/-- **Step 3: `YPseqCode`'s own outer `combineFound2` "found" flag is unconditionally `1`.** -/
theorem YPseqCode_four_pow_found (n : ℕ) :
    (combineFound2 hUnion0
      (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 0 (4 ^ n))
      (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 1 (4 ^ n))
      ).unpair.1 = 1 :=
  (combineFound2_found_iff hUnion0
    (YFoldInner_found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
      (Nat.zero_le 1) n (4 ^ n))
    (YFoldInner_found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
      (le_refl 1) n (4 ^ n))).mpr
    (YFoldInner_or_found P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin
      hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 n)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 in
/-- **Step 4a: `YPseqCode n` is unconditionally `D₀`-genuine.** -/
theorem YPseqCode_mem_unconditional (n : ℕ) :
    D₀.mem (P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n)) :=
  YPseqCode_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hUnion0
    (YPseqCode_four_pow_found P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 n)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 in
/-- **Step 4b: the closed-form membership characterization of `YPseqCode`, unconditionally** —
`(d)(4)(d)`'s headline closed form, matching Scott's `Y`-side recursion with no residual "found"
side-condition. -/
theorem mem_YPseqCode_iff_unconditional (n : ℕ) (z : α) :
    z ∈ P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) ↔
      (∃ i < 4 ^ n, yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i 0 = 0 ∧
        z ∈ P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i 0)) ∨
      (∃ i < 4 ^ n, yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i 1 = 0 ∧
        z ∈ P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i 1)) :=
  mem_YPseqCode_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin
    hUnion0 (YPseqCode_four_pow_found P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
      hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 n) z

end YPseqCodeUnconditional

/-! ## 8.12(d)(5)(a): zero/master facts for `XPseqCode`/`YPseqCode`

Generalizes `Exercise812c.lean`'s `XPseq_zero`/`YPseq_zero` to the code level: given Scott's
zero-convention `hX0 : P₀.X 0 = D₀.master`/`hY0 : P₁.X 0 = D₁.master` (the code-level analogue of
`(c)(vii)`'s own `hX0`/`hY0`), `P₁.X (XPseqCode … 0) = D₁.master` and `P₀.X (YPseqCode … 0) =
D₀.master`.

Both proofs need only the depth-`0` slice of the fold: `4 ^ 0 = 1` forces the existential witness
`i` in `mem_XPseqCode_iff_unconditional`/`mem_YPseqCode_iff_unconditional` to be `0`, `atomPairG`'s
own `n = 0` base clause is `(D₀.master, D₁.master)` regardless of sign-history
(`atomPairCodeState_correct`'s zero case, unconditionally non-junk via the new `atomPairJunk_zero`),
and the *same* `SplitSpec'` argument `XPseq_zero`/`YPseq_zero` use — the "−"-branch forced empty by
`A \ Xn = D₀.master \ D₀.master = ∅` (resp. `D₁`-side), pinning the "+"-branch to the full union via
`(split A B Xn).1 ∪ (split A B Xn).2 = B` — transports through `IsComputableSplit.posIdx_spec`
verbatim. The `⊆ D₁.master`/`⊆ D₀.master` half of each equality needs no case analysis at all: every
half-step atom is `mem`-genuine unconditionally (`xPseqAtomIdx_mem`/`yPseqAtomIdx_mem`), hence
`⊆ D₁.master`/`D₀.master` via `sub_master` regardless of which bit-source/junk-status witnessed it.

The `Y`-side reuses the `X`-side computation directly: `yPseqAtomState`'s inner `xSubStep` call at
bit `bx = 1` is *definitionally* `xPseqAtomState` (identical packed arguments), so the `D₁`-side
value already computed for `XPseqCode`'s zero fact doubles as the "`B`"-input the `Y`-sub-step's
own split (`hSplitY`) needs — only the `D₀`-direct-refine companion value (`xPseqAtomIdx0_eq`, the
`stateIdx0` twin of `xPseqAtomIdx_eq`) is new content. -/

section XYPseqCodeZero

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

/-- **The depth-`0` state is never junk**, for any bit-source `k`: `atomPairCodeState`'s own base
clause (`stateBase2`) hardcodes junk `0`, regardless of `k`. -/
theorem atomPairJunk_zero (k : ℕ) :
    atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 k = 0 := by
  unfold atomPairJunk
  simp [atomPairCodeState, atomPairBase, stateBase2]

/-- **The half-step atom's `D₀`-direct-refine index, in closed form, when non-junk**: the
`D₀`-side twin of `xPseqAtomIdx_eq`, reading off `xSubStep`'s *other* output (`stateIdx0`, the
direct `∩`/`\` refinement against `P₀.X n`, rather than `stateIdx1`'s split branch). -/
theorem xPseqAtomIdx0_eq {n i : ℕ}
    (h : xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0) :
    stateIdx0 (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) =
      P₀.inter (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) n := by
  have h' : stateJunk (xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair 1
      (packState2 (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
        (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
        (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i))))) = 0 := h
  rw [xSubStep_junk_eq] at h'
  unfold xPseqAtomState
  rw [xSubStep_idx0_eq (h := h'), stateIdx0_packState2, selectFn_one]

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hX0 in
/-- **8.12(d)(5)(a), `X`-side.** `P₁.X (XPseqCode … 0) = D₁.master`. -/
theorem XPseqCode_zero :
    P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 0) = D₁.master := by
  have hjunk0 := atomPairJunk_zero P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0
  have hcs := atomPairCodeState_correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne 0 0 hjunk0
  have hA0 : P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) =
      D₀.master := hcs.1
  have hB0 : P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) =
      D₁.master := hcs.2
  have hxjunk0 : xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0 = 0 := by
    rw [xPseqAtomJunk_eq, hjunk0, selectFn_zero]
    by_contra hcon
    have hle := emptyInterDec_le_one P₀ (Nat.pair
      (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0)
    have h1 : emptyInterDec P₀ (Nat.pair
        (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0) = 1 := by omega
    have hempty := (emptyInterDec_eq_one_iff P₀ hD₀pos hD₀nomin _ _).mp h1
    rw [hA0, hX0, Set.inter_self] at hempty
    exact hD₀mne.ne_empty hempty
  have hidxeq : xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0 =
      hSplitX.posIdx (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0)
        (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0 :=
    xPseqAtomIdx_eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hxjunk0
  have hAB1 : D₀.master = ∅ ↔ D₁.master = ∅ :=
    ⟨fun h => absurd h hD₀mne.ne_empty, fun h => absurd h hD₁mne.ne_empty⟩
  have hBE1 : D₁.master = ∅ ∨ D₁.mem D₁.master := Or.inr D₁.master_mem
  have hspec1 := hxSplit hAB1 hBE1 D₀.master
  have hdiff1 : D₀.master \ D₀.master = ∅ := Set.sdiff_self
  have h2empty1 : (splitX D₀.master D₁.master D₀.master).2 = ∅ := hspec1.2.2.2.1.mp hdiff1
  have hunion1 : (splitX D₀.master D₁.master D₀.master).1 = D₁.master := by
    have hu := hspec1.2.2.2.2.1
    rwa [h2empty1, Set.union_empty] at hu
  have hne1 : (splitX (P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0))
      (P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0))
      (P₀.X 0)).1 ≠ ∅ := by rw [hA0, hB0, hX0, hunion1]; exact hD₁mne.ne_empty
  have hposspec := hSplitX.posIdx_spec
    (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0)
    (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0 hne1
  rw [hA0, hB0, hX0] at hposspec
  have hzeroeq : P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) =
      D₁.master := by rw [hidxeq, ← hposspec]; exact hunion1
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨i, -, -, hzi⟩ := (mem_XPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX
      splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
      hUnion1 0 z).mp hz
    exact D₁.sub_master (xPseqAtomIdx_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 i) hzi
  · intro z hz
    refine (mem_XPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 0
      z).mpr ⟨0, by norm_num, hxjunk0, ?_⟩
    rwa [hzeroeq]

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hX0 hY0 in
/-- **8.12(d)(5)(a), `Y`-side.** `P₀.X (YPseqCode … 0) = D₀.master`. -/
theorem YPseqCode_zero :
    P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 0) = D₀.master := by
  have hjunk0 := atomPairJunk_zero P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0
  have hcs := atomPairCodeState_correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne 0 0 hjunk0
  have hA0 : P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) =
      D₀.master := hcs.1
  have hB0 : P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) =
      D₁.master := hcs.2
  have hxjunk0 : xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0 = 0 := by
    rw [xPseqAtomJunk_eq, hjunk0, selectFn_zero]
    by_contra hcon
    have hle := emptyInterDec_le_one P₀ (Nat.pair
      (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0)
    have h1 : emptyInterDec P₀ (Nat.pair
        (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0) = 1 := by omega
    have hempty := (emptyInterDec_eq_one_iff P₀ hD₀pos hD₀nomin _ _).mp h1
    rw [hA0, hX0, Set.inter_self] at hempty
    exact hD₀mne.ne_empty hempty
  have hidxeq : xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0 =
      hSplitX.posIdx (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0)
        (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0 :=
    xPseqAtomIdx_eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hxjunk0
  have hAB1 : D₀.master = ∅ ↔ D₁.master = ∅ :=
    ⟨fun h => absurd h hD₀mne.ne_empty, fun h => absurd h hD₁mne.ne_empty⟩
  have hBE1 : D₁.master = ∅ ∨ D₁.mem D₁.master := Or.inr D₁.master_mem
  have hspec1 := hxSplit hAB1 hBE1 D₀.master
  have hdiff1 : D₀.master \ D₀.master = ∅ := Set.sdiff_self
  have h2empty1 : (splitX D₀.master D₁.master D₀.master).2 = ∅ := hspec1.2.2.2.1.mp hdiff1
  have hunion1 : (splitX D₀.master D₁.master D₀.master).1 = D₁.master := by
    have hu := hspec1.2.2.2.2.1
    rwa [h2empty1, Set.union_empty] at hu
  have hne1 : (splitX (P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0))
      (P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0))
      (P₀.X 0)).1 ≠ ∅ := by rw [hA0, hB0, hX0, hunion1]; exact hD₁mne.ne_empty
  have hposspec := hSplitX.posIdx_spec
    (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0)
    (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0 hne1
  rw [hA0, hB0, hX0] at hposspec
  have hzeroeq : P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) =
      D₁.master := by rw [hidxeq, ← hposspec]; exact hunion1
  -- The `D₀`-direct-refine companion value at the same depth/bit-source is also the full master.
  have hidx0eq : stateIdx0 (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) =
      P₀.inter (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0 :=
    xPseqAtomIdx0_eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hxjunk0
  have hinterex : ∃ k, P₀.X k ⊆
      P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) ∩ P₀.X 0 :=
    ⟨atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0, by
      rw [hA0, hX0, Set.inter_self]⟩
  have hidx0set : P₀.X (stateIdx0 (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
      hSplitY 0 0)) = D₀.master := by
    rw [hidx0eq, P₀.inter_spec hinterex, hA0, hX0, Set.inter_self]
  -- `stateIdx1` of the incoming `X`-sub-step state is definitionally `xPseqAtomIdx`.
  have hstateIdx1 : stateIdx1 (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      0 0) = xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0 := rfl
  -- `yPseqAtomState`'s inner `X`-sub-step call at `bx = 1` is definitionally `xPseqAtomState`, so
  -- its own "found" condition reduces to the already-established `hxjunk0`/`hzeroeq`.
  have hraw : selectFn (stateJunk (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
      hSplitY 0 0)) 1 (selectFn 1
        (emptyInterDec P₁ (Nat.pair (stateIdx1 (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX
          splitY hSplitY 0 0)) 0))
        (emptyDiffDec P₁ hDiff1 (Nat.pair (stateIdx1 (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX
          hSplitX splitY hSplitY 0 0)) 0))) = 0 := by
    have hxjunk0' : stateJunk (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        0 0) = 0 := hxjunk0
    rw [hxjunk0', selectFn_zero, selectFn_one, hstateIdx1]
    by_contra hcon
    have hle := emptyInterDec_le_one P₁ (Nat.pair
      (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0)
    have h1 : emptyInterDec P₁ (Nat.pair
        (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0) = 1 := by omega
    have hempty := (emptyInterDec_eq_one_iff P₁ hD₁pos hD₁nomin _ _).mp h1
    rw [hzeroeq, hY0, Set.inter_self] at hempty
    exact hD₁mne.ne_empty hempty
  have hyidx0raw := ySubStep_idx0_eq P₀ P₁ hDiff1 splitY hSplitY (h := hraw)
  rw [selectFn_one, hstateIdx1] at hyidx0raw
  have hyidxeq : yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0 1 =
      hSplitY.posIdx (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0)
        (stateIdx0 (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0)) 0 :=
    hyidx0raw
  have hyjunkeq : yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0 1 = 0 := by
    show stateJunk (ySubStep P₀ P₁ hDiff1 splitY hSplitY (Nat.pair 0 (Nat.pair 1
      (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0)))) = 0
    rw [ySubStep_junk_eq]; exact hraw
  have hAB2 : D₁.master = ∅ ↔ D₀.master = ∅ := hAB1.symm
  have hBE2 : D₀.master = ∅ ∨ D₀.mem D₀.master := Or.inr D₀.master_mem
  have hspec2 := hySplit hAB2 hBE2 D₁.master
  have hdiff2 : D₁.master \ D₁.master = ∅ := Set.sdiff_self
  have h2empty2 : (splitY D₁.master D₀.master D₁.master).2 = ∅ := hspec2.2.2.2.1.mp hdiff2
  have hunion2 : (splitY D₁.master D₀.master D₁.master).1 = D₀.master := by
    have hu := hspec2.2.2.2.2.1
    rwa [h2empty2, Set.union_empty] at hu
  have hne2 : (splitY
      (P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0))
      (P₀.X (stateIdx0 (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0)))
      (P₁.X 0)).1 ≠ ∅ := by rw [hzeroeq, hidx0set, hY0, hunion2]; exact hD₀mne.ne_empty
  have hposspec2 := hSplitY.posIdx_spec
    (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0)
    (stateIdx0 (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0)) 0 hne2
  rw [hzeroeq, hidx0set, hY0] at hposspec2
  have hyzeroeq : P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0 1) =
      D₀.master := by rw [hyidxeq, ← hposspec2]; exact hunion2
  apply Set.Subset.antisymm
  · intro z hz
    rcases (mem_YPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 0
      z).mp hz with ⟨i, -, -, hzi⟩ | ⟨i, -, -, hzi⟩
    · exact D₀.sub_master
        (yPseqAtomIdx_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 i 0) hzi
    · exact D₀.sub_master
        (yPseqAtomIdx_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 i 1) hzi
  · intro z hz
    refine (mem_YPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 0
      z).mpr (Or.inr ⟨0, by norm_num, hyjunkeq, ?_⟩)
    rwa [hyzeroeq]

end XYPseqCodeZero

/-! ## 8.12(d)(5)(b)(i): the `X`-side I-formula for `XPseqCode`

**Design decision (resolved, after a bounded search per `(d)(5)`'s own flagged decision):** `(d)(5)(b)`'s
order/intersection transfer facts (`X_subset_iff_XPseqCode_subset` etc.) compare `P₀.X i`/`P₀.X j` —
*raw*, mutually unrelated enumeration indices, not outputs of any `atomPairG` recursion — so no
shortcut bypassing `Exercise812c.lean`'s `combinedX`/`combinedY`/`genAtom`-interleaving apparatus
(**Route 1**) was found: relating two *arbitrary* indices intrinsically needs the "embed both families
into one recursive tree" trick that apparatus provides, exactly as `(d)(5)`'s finding 2 anticipated.
**However, a genuine, non-trivial simplification survives** in the one piece of that apparatus that
*is* code-native: the "I-formula" identities (`xStep_snd_eq_inter_XPseq`/`yStep_fst_eq_inter_YPseq`,
`Exercise812c.lean` lines 899–1172, ~270 lines total) needed to seed the interleaved family's odd-depth
half-steps. Classically these need heavy case analysis because `XPseq`/`YPseq` are unions over the
*uncountable* `δ' : ℕ → Bool × Bool`. At the code level, `XPseqCode`/`YPseqCode` are already unions
over *at most `4 ⁿ` literally distinct* bit-sources (`mem_XPseqCode_iff_unconditional`/
`mem_YPseqCode_iff_unconditional`, `(d)(4)`, already `Pass`), and any two distinct bit-sources both
`< 4 ⁿ` are *automatically* distinguished by some `deltaPair`-digit `< n`
(`exists_deltaPair_ne_of_lt_of_ne` above) — no "history agrees through `n`" case ever arises, so the
`⊇` direction collapses to a single disjointness appeal (`atomPairCodeState_disjoint`) instead of a
δ'-indexed case split. This sub-part builds the `X`-side instance of that shortened I-formula;
`(d)(5)(b)(ii)` will build the (structurally harder, extra-`bx`) `Y`-side instance, then `(d)(5)(b)(iii)`
assembles the generalized `combinedXCode`/`combinedYCode`/`hcore` machinery these feed, reusing
`Theorem88.lean`'s `transfer_dir`/`genAtom` apparatus (already fully generic, no changes needed) for
the final headline theorems. -/

section XPseqCodeIFormula

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
set_option maxHeartbeats 800000 in
/-- **The `X`-side I-formula, generic in the bit-source**: a genuine (non-junk) half-step atom's
`hSplitX.posIdx` value is always `⊆` its own `D₁`-side companion `atomPairIdx1`. Factored out of
`xPseqAtomIdx_eq_inter_XPseqCode`'s proof so it can be reused verbatim at the *other* bit-source `k'`
arising from `mem_XPseqCode_iff_unconditional`'s existential witness. -/
theorem xPseqAtomIdx_subset_atomPairIdx1 {n m : ℕ}
    (hjunk : xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n m = 0) :
    P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n m) ⊆
      P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n m) := by
  have hraw := hjunk
  rw [xPseqAtomJunk_eq] at hraw
  obtain ⟨hAjunk, hempty0⟩ := selectFn_one_eq_zero_iff.mp hraw
  have hidxeq := xPseqAtomIdx_eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hjunk
  have hcs := atomPairCodeState_correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne m n hAjunk
  have hinv := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff splitX hxSplit
    P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair m) n
  have hspec := hxSplit hinv.1 hinv.2.2 (P₀.X n)
  have hne : (splitX (P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n m))
      (P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n m)) (P₀.X n)).1 ≠
      ∅ := by
    rw [hcs.1, hcs.2]
    have hempty' : P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n m) ∩
        P₀.X n ≠ ∅ := (emptyInterDec_eq_one_iff P₀ hD₀pos hD₀nomin _ _).not.mp (by omega)
    rw [hcs.1] at hempty'
    exact hspec.2.2.1.not.mp hempty'
  have hposspec := hSplitX.posIdx_spec
    (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n m)
    (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n m) n hne
  rw [hcs.1, hcs.2] at hposspec
  rw [hidxeq, ← hposspec, hcs.2]
  calc (splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair m) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair m) n).2 (P₀.X n)).1
      ⊆ (splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair m) n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair m) n).2 (P₀.X n)).1 ∪
        (splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair m) n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair m) n).2 (P₀.X n)).2 :=
        Set.subset_union_left
    _ = (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair m) n).2 := hspec.2.2.2.2.1

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
set_option maxHeartbeats 800000 in
/-- **8.12(d)(5)(b)(i): the `X`-side I-formula for `XPseqCode`**, the code-level, bounded-existential
analogue of `Exercise812c.lean`'s `xStep_snd_eq_inter_XPseq`. See the section docstring above for why
the `⊇` direction needs no δ'-agreement case split, unlike the classical proof. -/
theorem xPseqAtomIdx_eq_inter_XPseqCode {n k : ℕ} (hk : k < 4 ^ n)
    (hjunk : xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 0) :
    P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) =
      P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) ∩
        P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n) := by
  apply Set.Subset.antisymm
  · intro z hz
    refine ⟨xPseqAtomIdx_subset_atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hjunk hz, ?_⟩
    exact (mem_XPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
      hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 n z).mpr
      ⟨k, hk, hjunk, hz⟩
  · rintro z ⟨hzB, hzXP⟩
    obtain ⟨k', hk', hjunk', hz'⟩ := (mem_XPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1 splitX
      hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne
      hD₁mne hUnion1 n z).mp hzXP
    by_cases hkk' : k' = k
    · rwa [hkk'] at hz'
    · exfalso
      have hAjunk : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 0 := by
        have h := hjunk
        rw [xPseqAtomJunk_eq] at h
        exact junk_eq_zero_of_selectFn_eq_zero h
      have hAjunk' : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k' = 0 := by
        have h := hjunk'
        rw [xPseqAtomJunk_eq] at h
        exact junk_eq_zero_of_selectFn_eq_zero h
      obtain ⟨i, hi, hne⟩ := exists_deltaPair_ne_of_lt_of_ne hk' hk hkk'
      have hdisj := (atomPairCodeState_disjoint P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
        (n := n) (k := k') (k' := k) hAjunk' hAjunk ⟨i, hi, hne⟩).2
      have hz'' : z ∈ P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k') :=
        xPseqAtomIdx_subset_atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
          hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hjunk' hz'
      exact absurd (Set.mem_inter hz'' hzB) (by rw [hdisj]; simp)

end XPseqCodeIFormula

/-! ## 8.12(d)(5)(b)(ii): the `Y`-side I-formula for `YPseqCode`

The code-level analogue of `Exercise812c.lean`'s `yStep_fst_eq_inter_YPseq`, needed to seed
`(b)(iii)`'s `combinedXCode`'s odd-depth half-step. Structurally harder than `(b)(i)` exactly as
anticipated: `yPseqAtomIdx n i bx` carries a *free* extra bit `bx`, so both the closed form and the
disjointness argument need an extra case split on `bx` in addition to `i`. -/

section YPseqCodeIFormula

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀)

/-- **The half-step-`bx` atom's junk flag propagates back to `atomPairJunk`** (any `bx`, any
`b`-choice at the outer `y`-sub-step, which is always forced to `1` inside `yPseqAtomState`): the
`Y`-side twin of the chase already inlined inside `yPseqAtomJunk_eq_zero_of_bit`, factored out here
since the I-formula below needs it independently at *two* different bit-sources. Needs no
`SplitSpec'`/`IsPositive`-style hypotheses at all — purely a `selectFn`-unfolding fact. -/
theorem atomPairJunk_eq_zero_of_yPseqAtomJunk {n i : ℕ} (b : Bool)
    (hjunk : yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i
      (if b then 1 else 0) = 0) :
    atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 := by
  set s0 := packState2
      (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
      (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
      (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) with hs0def
  set s1 := xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair (if b then 1 else 0) s0))
    with hs1def
  have h : stateJunk (ySubStep P₀ P₁ hDiff1 splitY hSplitY (Nat.pair n (Nat.pair 1 s1))) = 0 := by
    have h' := hjunk
    unfold yPseqAtomJunk yPseqAtomState at h'
    rwa [← hs0def, ← hs1def] at h'
  have hxnonjunk : stateJunk s1 = 0 := by
    have h2 := h
    rw [ySubStep_junk_eq, selectFn_one] at h2
    exact junk_eq_zero_of_selectFn_eq_zero h2
  have h3 := hxnonjunk
  rw [hs1def, xSubStep_junk_eq, hs0def, stateJunk_packState2] at h3
  exact junk_eq_zero_of_selectFn_eq_zero h3

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
set_option maxHeartbeats 800000 in
/-- **The `Y`-side atom's `D₀`-index, subset of the depth-`n`-plus-half-step `X`-sub-step output.**
The `Y`-side twin of `(b)(i)`'s `xPseqAtomIdx_subset_atomPairIdx1`, but one half-step deeper:
`yPseqAtomIdx`'s genuine value is always `⊆` the `xStepG`-level set the inner (free-`bx`) `X`-sub-step
produces at depth `n`, via `hySplit`'s unconditional `∪ = A1`-field applied to that inner
`xSubStep_correct`/`ySubStep_correct` identification. -/
theorem yPseqAtomIdx_subset_xStepGFst {n i : ℕ} (b : Bool)
    (hjunk : yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i
      (if b then 1 else 0) = 0) :
    P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i (if b then 1 else 0)) ⊆
      (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b).1 := by
  set s0 := packState2
      (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
      (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
      (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) with hs0def
  set s1 := xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair (if b then 1 else 0) s0))
    with hs1def
  have h : stateJunk (ySubStep P₀ P₁ hDiff1 splitY hSplitY (Nat.pair n (Nat.pair 1 s1))) = 0 := by
    have h' := hjunk
    unfold yPseqAtomJunk yPseqAtomState at h'
    rwa [← hs0def, ← hs1def] at h'
  have hxnonjunk : stateJunk s1 = 0 := by
    have h2 := h
    rw [ySubStep_junk_eq, selectFn_one] at h2
    exact junk_eq_zero_of_selectFn_eq_zero h2
  have hAjunk : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 :=
    atomPairJunk_eq_zero_of_yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY b hjunk
  obtain ⟨hidx0, hidx1⟩ := atomPairCodeState_correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
    hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne i n
    hAjunk
  have hidx0' : P₀.X (stateIdx0 s0) =
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1 := by
    rw [hs0def, stateIdx0_packState2]; exact hidx0
  have hidx1' : P₁.X (stateIdx1 s0) =
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 := by
    rw [hs0def, stateIdx1_packState2]; exact hidx1
  obtain ⟨ihAB, -, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n
  obtain ⟨hxc0, hxc1⟩ := xSubStep_correct P₀ P₁ hDiff0 splitX hSplitX hD₀pos hD₀diff hD₀nomin
    hxSplit hidx0' hidx1' ihAB ihB b hxnonjunk
  rw [← hs1def] at hxc0 hxc1
  have hAmem : (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b).1 = ∅ ∨
      D₀.mem (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b).1 :=
    Or.inr (hxc0 ▸ P₀.mem_X _)
  have hBA : (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b).2 = ∅ ↔
      (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b).1 = ∅ := by
    have hspec1 := hxSplit ihAB ihB (P₀.X n)
    by_cases hb : b = true
    · simp only [xStepG, xyStep, hb, if_true]; exact hspec1.2.2.1.symm
    · simp only [xStepG, xyStep, hb]; exact hspec1.2.2.2.1.symm
  obtain ⟨hyc0, -⟩ := ySubStep_correct P₀ P₁ hDiff1 splitY hSplitY hD₁pos hD₁diff hD₁nomin hySplit
    hxc0 hxc1 hBA hAmem true h
  have hgoaleq : P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i
      (if b then 1 else 0)) =
      (yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b).2
        (P₁.X n) true).1 := by
    show P₀.X (stateIdx0 (yPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i
      (if b then 1 else 0))) = _
    unfold yPseqAtomState
    rw [← hs0def, ← hs1def]
    exact hyc0
  rw [hgoaleq]
  exact yStepG_fst_subset hySplit hBA hAmem (P₁.X n) true

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
/-- **Widening to the depth-`n` parent's own `D₀`-piece**: composing `yPseqAtomIdx_subset_xStepGFst`
with `xStepG_fst_subset` and `atomPairCodeState_correct`'s forward identification. Needed by the
I-formula's `⊇` direction to compare *two different* bit-sources' atoms, since
`atomPairCodeState_disjoint` only speaks about the parent `atomPairIdx0`-level sets. -/
theorem yPseqAtomIdx_subset_atomPairIdx0 {n i : ℕ} (b : Bool)
    (hjunk : yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i
      (if b then 1 else 0) = 0) :
    P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i (if b then 1 else 0)) ⊆
      P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) := by
  have hAjunk : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 :=
    atomPairJunk_eq_zero_of_yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY b hjunk
  have hidx0 := (atomPairCodeState_correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne i n hAjunk).1
  rw [hidx0]
  exact (yPseqAtomIdx_subset_xStepGFst P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne b hjunk).trans
    (xStepG_fst_subset splitX _ _ (P₀.X n) b)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
/-- **The two-source disjointness dichotomy** feeding the I-formula's `⊇` direction: given a
witness bit-source/bit pair `(i', b')` whose atom contains `z` and a target pair `(i, b)` with `z`
already known to lie in the *classical* `xStepG`-level piece at `(i, b)`, either `(i', b') = (i, b)`
(so the witness atom already *is* the target atom) or the two atoms are disjoint — from either
`atomPairCodeState_disjoint` (if `i' ≠ i`, transported up through
`yPseqAtomIdx_subset_atomPairIdx0`) or `xStepG_disjoint_of_ne` (if `i' = i` but `b' ≠ b`, transported
up through `yPseqAtomIdx_subset_xStepGFst`) — a contradiction with the disjointness in either case. -/
theorem yPseqAtomIdx_eq_of_dichotomy {n i i' : ℕ} {z : α} (b b' : Bool)
    (hi : i < 4 ^ n) (hi' : i' < 4 ^ n)
    (hjunk : yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i
      (if b then 1 else 0) = 0)
    (hjunk' : yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i'
      (if b' then 1 else 0) = 0)
    (hzA1 : z ∈ (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b).1)
    (hz' : z ∈ P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i'
      (if b' then 1 else 0))) :
    z ∈ P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i
      (if b then 1 else 0)) := by
  by_cases hii' : i' = i
  · by_cases hbb' : b' = b
    · rw [hii', hbb'] at hz'
      exact hz'
    · exfalso
      rw [hii'] at hjunk' hz'
      have hz'' : z ∈ (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b').1 :=
        yPseqAtomIdx_subset_xStepGFst P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
          hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne b' hjunk' hz'
      obtain ⟨ihAB, -, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
        hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n
      have hdisj := (xStepG_disjoint_of_ne hxSplit ihAB ihB (P₀.X n) (b := b) (b' := b')
        (Ne.symm hbb')).1
      exact absurd (Set.mem_inter hzA1 hz'') (by rw [hdisj]; simp)
  · exfalso
    have hAjunk : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 :=
      atomPairJunk_eq_zero_of_yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY b
        hjunk
    have hAjunk' : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i' = 0 :=
      atomPairJunk_eq_zero_of_yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY b'
        hjunk'
    obtain ⟨j, hj, hne⟩ := exists_deltaPair_ne_of_lt_of_ne hi' hi hii'
    have hdisj := (atomPairCodeState_disjoint P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne (n := n)
      (k := i') (k' := i) hAjunk' hAjunk ⟨j, hj, hne⟩).1
    have hzA : z ∈ P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) := by
      have hAeq := (atomPairCodeState_correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne i n
        hAjunk).1
      rw [hAeq]
      exact (xStepG_fst_subset splitX _ _ (P₀.X n) b) hzA1
    have hzA' : z ∈ P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i') :=
      yPseqAtomIdx_subset_atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne b' hjunk' hz'
    exact absurd (Set.mem_inter hzA' hzA) (by rw [hdisj]; simp)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 in
set_option maxHeartbeats 800000 in
/-- **8.12(d)(5)(b)(ii): the `Y`-side I-formula for `YPseqCode`**, the code-level analogue of
`Exercise812c.lean`'s `yStep_fst_eq_inter_YPseq`. See the section docstring above for the extra
`bx`-level case split this needs beyond `(b)(i)`'s own `X`-side argument. -/
theorem yPseqAtomIdx_eq_inter_YPseqCode {n i : ℕ} (hi : i < 4 ^ n) (b : Bool)
    (hjunk : yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i
      (if b then 1 else 0) = 0) :
    P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i (if b then 1 else 0)) =
      (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b).1 ∩
        P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) := by
  apply Set.Subset.antisymm
  · intro z hz
    refine ⟨yPseqAtomIdx_subset_xStepGFst P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne b hjunk hz,
      ?_⟩
    refine (mem_YPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 n
      z).mpr ?_
    by_cases hb : b = true
    · subst hb; exact Or.inr ⟨i, hi, hjunk, hz⟩
    · rw [Bool.not_eq_true] at hb; subst hb; exact Or.inl ⟨i, hi, hjunk, hz⟩
  · rintro z ⟨hzA1, hzYP⟩
    obtain (⟨i', hi', hjunk', hz'⟩ | ⟨i', hi', hjunk', hz'⟩) :=
      (mem_YPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 n z).mp hzYP
    · exact yPseqAtomIdx_eq_of_dichotomy P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne b false hi hi'
        hjunk hjunk' hzA1 hz'
    · exact yPseqAtomIdx_eq_of_dichotomy P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne b true hi hi'
        hjunk hjunk' hzA1 hz'

end YPseqCodeIFormula

/-! ## 8.12(d)(5)(b)(iii): `combinedXCode`/`combinedYCode`/`combinedδ`, and `hcore`

The generalized interleaved-family machinery, mirroring `Exercise812c.lean`'s `combinedX`/
`combinedY`/`combinedδ` (lines 1236–1457) with `atomPair → atomPairG`, `splitChoice' → splitX/
splitY`, `XPseq k → P₁.X (XPseqCode … k)`, `YPseq k → P₀.X (YPseqCode … k)`. **`combinedδ`/
`deinterleaveδ` need no code-level replica at all**: both are already pure functions of
`ℕ → Bool × Bool`/`ℕ → Bool` and `ℕ`, with no dependence whatsoever on `X`/`Y`/`D₀`/`D₁`, so
`Exercise812c.lean`'s versions (and their `_even`/`_odd`/`combinedδ_deinterleaveδ` lemmas) are
reused completely verbatim below — only `combinedXCode`/`combinedYCode` themselves are new.

The genuinely new content is the two "two-branch closed form" lemmas
(`xStepG_snd_succ_eq_XPseqCode`/`yStepG_fst_succ_eq_YPseqCode`), generalizing `(b)(i)`/`(b)(ii)`'s
bounded-existential I-formulas (stated only for bit-sources `k < 4 ^ n`) to *arbitrary*
`δ : ℕ → Bool × Bool`, via `encodeDeltaPair δ n` (`(d)(4)(c)(iii)`, already `Pass`) as the bounded
representative. Two genuinely new sub-cases appear along the way that neither `(b)(i)` nor `(b)(ii)`
needed: (1) `(atomPairG … δ n)`'s component may be `∅` for an arbitrary `δ` (impossible for the
`XPseqCode`/`YPseqCode` folds' own witnesses, which are always non-junk by construction) — handled
directly via `SplitSpec'` alone, no code/junk facts needed; (2) even when non-`∅`, the *fresh*
half-step atom itself (`xPseqAtomJunk`/`yPseqAtomJunk`) may independently be junk — handled by a
"junk-mismatch" trick: `mem_XPseqCode_iff_unconditional`/`mem_YPseqCode_iff_unconditional`'s
existential witnesses are *guaranteed* non-junk, so a junk target automatically differs from every
witness, collapsing straight to the same disjointness apparatus `(b)(i)`/`(b)(ii)` already built. -/

section CombinedCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

/-- The interleaved family testing `D₀`'s side, code-level analogue of `combinedX`: at even
positions, `P₀`'s own enumeration; at odd positions, `YPseqCode`'s recovered `D₀`-side pieces. -/
noncomputable def combinedXCode (n : ℕ) : Set α :=
  if n % 2 = 0 then P₀.X (n / 2)
  else P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 (n / 2))

/-- The interleaved family testing `D₁`'s side, code-level analogue of `combinedY`: at even
positions, `XPseqCode`'s recovered `D₁`-side pieces; at odd positions, `P₁`'s own enumeration. -/
noncomputable def combinedYCode (n : ℕ) : Set β :=
  if n % 2 = 0 then
    P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 (n / 2))
  else P₁.X (n / 2)

theorem combinedXCode_even (k : ℕ) :
    combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 (2 * k) = P₀.X k := by
  unfold combinedXCode
  rw [if_pos (by omega : (2 * k) % 2 = 0), show (2 * k) / 2 = k from by omega]

theorem combinedXCode_odd (k : ℕ) :
    combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 (2 * k + 1) =
      P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k) := by
  unfold combinedXCode
  rw [if_neg (by omega : ¬ (2 * k + 1) % 2 = 0), show (2 * k + 1) / 2 = k from by omega]

theorem combinedYCode_even (k : ℕ) :
    combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 (2 * k) =
      P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k) := by
  unfold combinedYCode
  rw [if_pos (by omega : (2 * k) % 2 = 0), show (2 * k) / 2 = k from by omega]

theorem combinedYCode_odd (k : ℕ) :
    combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 (2 * k + 1) =
      P₁.X k := by
  unfold combinedYCode
  rw [if_neg (by omega : ¬ (2 * k + 1) % 2 = 0), show (2 * k + 1) / 2 = k from by omega]

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
set_option maxHeartbeats 1000000 in
/-- **The `X`-side I-formula, generalized to an arbitrary `δ`** (not just a bounded bit-source `k <
4 ^ n`): the `X`-sub-step's own `"+"`/`true` branch, run on `atomPairG`'s depth-`n` component for
*any* history `δ`, is exactly the intersection of that component's `D₁`-side with `XPseqCode n`.
Bridges `(b)(i)`'s bounded-existential `xPseqAtomIdx_eq_inter_XPseqCode` up to the fully general
statement `Exercise812c.lean`'s own `xStep_snd_eq_inter_XPseq` makes, via `encodeDeltaPair δ n` as
the bounded representative: if the represented component is already `∅`, both sides are `∅`
directly from `SplitSpec'`; otherwise `(d)(4)(c)(v)`'s `atomPairJunk_eq_zero_of_snd_ne_empty` gives
a non-junk bit-source to feed `(b)(i)`'s headline, *unless* the fresh half-step atom is itself junk
— handled by the "junk-mismatch" trick documented at the section level. -/
theorem xStepG_snd_eq_inter_XPseqCode (δ : ℕ → Bool × Bool) (n : ℕ) :
    (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) true).2 =
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 ∩
        P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n) := by
  simp only [xStepG, xyStep, if_true]
  set k := encodeDeltaPair δ n with hkdef
  have hklt : k < 4 ^ n := encodeDeltaPair_lt δ n
  have hagree : ∀ i < n, δ i = deltaPair k i := fun i hi =>
    (deltaPair_encodeDeltaPair δ n i hi).symm
  have hcongr : atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n =
      atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair k) n :=
    atomPairG_congr D₀ D₁ splitY splitX P₀.X P₁.X hagree
  rw [hcongr]
  set A := (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair k) n).1 with hAdef
  set B := (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair k) n).2 with hBdef
  obtain ⟨hAB, -, hBmem⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair k) n
  rw [← hAdef] at hAB
  rw [← hBdef] at hAB hBmem
  by_cases hB : B = ∅
  · have hspec := hxSplit hAB (Or.inl hB) (P₀.X n)
    have hunion := hspec.2.2.2.2.1
    have h1empty : (splitX A B (P₀.X n)).1 = ∅ :=
      Set.subset_eq_empty Set.subset_union_left (hunion.trans hB)
    rw [h1empty, hB]; simp
  · have hAjunk : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 0 :=
      atomPairJunk_eq_zero_of_snd_ne_empty P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hB
    have hcs := atomPairCodeState_correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
      hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne k n hAjunk
    by_cases hxj : xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 0
    · have hIF := xPseqAtomIdx_eq_inter_XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 hklt
        hxj
      have hidxeq := xPseqAtomIdx_eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hxj
      have hraw' := hxj
      rw [xPseqAtomJunk_eq] at hraw'
      obtain ⟨-, hempty0'⟩ := selectFn_one_eq_zero_iff.mp hraw'
      have hAeq : A = P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) :=
        hAdef.trans hcs.1.symm
      have hempty'' : A ∩ P₀.X n ≠ ∅ := by
        rw [hAeq]
        exact (emptyInterDec_eq_one_iff P₀ hD₀pos hD₀nomin _ _).not.mp (by omega)
      have hne : (splitX A B (P₀.X n)).1 ≠ ∅ := by
        have hspecAB := hxSplit hAB hBmem (P₀.X n)
        exact hspecAB.2.2.1.not.mp hempty''
      have hposspec := hSplitX.posIdx_spec
        (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k)
        (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) n
        (by rw [hcs.1, hcs.2]; exact hne)
      rw [hcs.1, hcs.2] at hposspec
      have hgoal2 : P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) =
          (splitX A B (P₀.X n)).1 := by rw [hidxeq]; exact hposspec.symm
      rw [← hgoal2, hIF, hcs.2]
    · have hxj1 : xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 1 := by
        have := xPseqAtomJunk_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k
        omega
      have h2empty : (splitX A B (P₀.X n)).1 = ∅ := by
        have h := hxj1
        rw [xPseqAtomJunk_eq, hAjunk, selectFn_zero] at h
        have hempty := (emptyInterDec_eq_one_iff P₀ hD₀pos hD₀nomin _ _).mp h
        rw [hcs.1] at hempty
        have hspec := hxSplit hAB hBmem (P₀.X n)
        exact hspec.2.2.1.mp hempty
      have hdisjXP : B ∩
          P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z ⟨hzB, hzXP⟩
        obtain ⟨k', hk'lt, hjunk', hz'⟩ := (mem_XPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1
          splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin
          hySplit hD₀mne hD₁mne hUnion1 n z).mp hzXP
        have hkk' : k' ≠ k := by rintro rfl; omega
        have hAjunk' : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k' = 0 := by
          have h := hjunk'
          rw [xPseqAtomJunk_eq] at h
          exact junk_eq_zero_of_selectFn_eq_zero h
        have hz'' : z ∈ P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k') :=
          xPseqAtomIdx_subset_atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
            hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hjunk' hz'
        have hzB' : z ∈ P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) :=
          hcs.2 ▸ hzB
        obtain ⟨i, hi, hne⟩ := exists_deltaPair_ne_of_lt_of_ne hklt hk'lt hkk'.symm
        have hdisj := (atomPairCodeState_disjoint P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
          hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
          (n := n) (k := k) (k' := k') hAjunk hAjunk' ⟨i, hi, hne⟩).2
        exact absurd (Set.mem_inter hzB' hz'') (by rw [hdisj]; simp)
      rw [h2empty, hdisjXP]

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
/-- **Two-branch closed form, generalized to an arbitrary `δ`**: completes
`xStepG_snd_eq_inter_XPseqCode`'s `true`-only fact into a full `genAtom`-shaped closed step at
*either* sign, exactly mirroring `Exercise812c.lean`'s `xStep_snd_succ_eq` — the `false` branch is
derived algebraically from the `true` branch plus `SplitSpec'`'s `I ∪ J = B`/`I ∩ J = ∅`, with no
new disjointness content. -/
theorem xStepG_snd_succ_eq_XPseqCode (δ : ℕ → Bool × Bool) (n : ℕ) (b : Bool) :
    (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) b).2 =
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 ∩
        (if b then P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n)
          else D₁.master \
            P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n)) := by
  obtain ⟨hAB, -, hBmem⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne δ n
  set A := (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1 with hAdef
  set B := (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 with hBdef
  set XP := P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n) with hXPdef
  have hspec := hxSplit hAB hBmem (P₀.X n)
  have hIeq : (xStepG splitX A B (P₀.X n) true).2 = B ∩ XP :=
    xStepG_snd_eq_inter_XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 δ n
  by_cases hb : b = true
  · rw [hb, if_pos rfl]; exact hIeq
  · rw [Bool.not_eq_true] at hb; subst hb
    rw [if_neg (by simp)]
    have hJeq : (xStepG splitX A B (P₀.X n) false).2 = B \ XP := by
      have hunion :
          (xStepG splitX A B (P₀.X n) true).2 ∪ (xStepG splitX A B (P₀.X n) false).2 = B := by
        simp only [xStepG, xyStep]; exact hspec.2.2.2.2.1
      have hinter :
          (xStepG splitX A B (P₀.X n) true).2 ∩ (xStepG splitX A B (P₀.X n) false).2 = ∅ := by
        simp only [xStepG, xyStep]; exact hspec.2.2.2.2.2
      ext x
      constructor
      · intro hxJ
        have hxB : x ∈ B := hunion ▸ Or.inr hxJ
        refine ⟨hxB, fun hxXP => ?_⟩
        have hxI : x ∈ (xStepG splitX A B (P₀.X n) true).2 := hIeq ▸ Set.mem_inter hxB hxXP
        exact absurd (Set.mem_inter hxI hxJ) (by rw [hinter]; simp)
      · rintro ⟨hxB, hxnXP⟩
        rw [← hunion] at hxB
        rcases hxB with hxI | hxJ
        · exact absurd (hIeq ▸ hxI : x ∈ B ∩ XP).2 hxnXP
        · exact hxJ
    rw [hJeq]
    have hsub := atomPairG_snd_subset_master D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
      splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne δ n
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hsub hx1, hx2⟩
    · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 in
set_option maxHeartbeats 4000000 in
/-- **The `Y`-side I-formula, generalized to an arbitrary `δ`** (not just a bounded bit-source
`k < 4 ^ n`) **and a free `bx : Bool`** (not just the bit `δ n).1` itself, matching
`Exercise812c.lean`'s own `yStep_fst_eq_inter_YPseq`): the `Y`-sub-step's `"+"`/`true` branch, run
on `xStepG`'s own output at *any* bit `bx` and *any* history `δ`, is exactly the intersection of
that output's `D₀`-side with `YPseqCode n`. Same overall strategy as
`xStepG_snd_eq_inter_XPseqCode`: encode `δ`'s depth-`n` prefix as `k := encodeDeltaPair δ n`, handle
`A1 = ∅` directly via `SplitSpec'`, and otherwise split on `yPseqAtomJunk n k (if bx then 1 else 0)`
— zero feeds `(b)(ii)`'s headline (after bridging its `yPseqAtomIdx` back to the `yStepG`-level via
`xSubStep_correct`/`ySubStep_correct`, mirroring `yPseqAtomIdx_subset_xStepGFst`'s own internal
`hgoaleq`); one is "fresh junk" at *this* extra half-step, handled by first showing the `X`-sub-step
itself must still be non-junk (else `A1 = ∅`, contradicting the case hypothesis), so the freshness
must come from the `Y`-sub-step's own direct-refine check, giving `B1 ∩ Yn = ∅` and hence the goal's
`true`-branch output is `∅` directly; the `∩ YPseqCode` side is then `∅` via the same
"junk-mismatch" disjointness trick as the `X`-side, now with an extra case split on the witness's
own `bx'`-bit (`xStepG_disjoint_of_ne` when the bit differs at the same `k`, else
`atomPairCodeState_disjoint` as before). -/
theorem yStepG_fst_eq_inter_YPseqCode (δ : ℕ → Bool × Bool) (n : ℕ) (bx : Bool) :
    (yStepG splitY
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) bx).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) bx).2
        (P₁.X n) true).1 =
      (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) bx).1 ∩
        P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) := by
  set k := encodeDeltaPair δ n with hkdef
  have hklt : k < 4 ^ n := encodeDeltaPair_lt δ n
  have hagree : ∀ i < n, δ i = deltaPair k i := fun i hi =>
    (deltaPair_encodeDeltaPair δ n i hi).symm
  have hcongr : atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n =
      atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair k) n :=
    atomPairG_congr D₀ D₁ splitY splitX P₀.X P₁.X hagree
  rw [hcongr]
  obtain ⟨ihAB, ihA, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair k) n
  set A := (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair k) n).1 with hAdef
  set B := (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair k) n).2 with hBdef
  set A1 := (xStepG splitX A B (P₀.X n) bx).1 with hA1def
  set B1 := (xStepG splitX A B (P₀.X n) bx).2 with hB1def
  have hspec1 := hxSplit ihAB ihB (P₀.X n)
  have hA1B1 : A1 = ∅ ↔ B1 = ∅ := by
    rw [hA1def, hB1def]
    by_cases hbx : bx = true
    · simp only [xStepG, xyStep, hbx, if_true]; exact hspec1.2.2.1
    · simp only [xStepG, xyStep, hbx, Bool.false_eq_true, if_false]; exact hspec1.2.2.2.1
  have hA1mem : A1 = ∅ ∨ D₀.mem A1 := by
    rw [hA1def]
    by_cases hbx : bx = true
    · simp only [xStepG, xyStep, hbx, if_true]; exact inter_mem_or_empty hD₀pos ihA (P₀.mem_X n)
    · simp only [xStepG, xyStep, hbx, Bool.false_eq_true, if_false]
      exact diff_mem_or_empty hD₀diff ihA (P₀.mem_X n)
  by_cases hA1 : A1 = ∅
  · have hB1e : B1 = ∅ := hA1B1.mp hA1
    have hspec2 := hySplit hA1B1.symm (Or.inl hA1) (P₁.X n)
    have hunion2 := hspec2.2.2.2.2.1
    have h1empty : (yStepG splitY A1 B1 (P₁.X n) true).1 = ∅ := by
      show (splitY B1 A1 (P₁.X n)).1 = ∅
      exact Set.subset_eq_empty Set.subset_union_left (hunion2.trans hA1)
    rw [h1empty, hA1]; simp
  · have hAne : A ≠ ∅ := by
      intro h
      apply hA1
      rw [hA1def]
      exact Set.subset_eq_empty (xStepG_fst_subset splitX A B (P₀.X n) bx) h
    have hAjunk : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 0 :=
      atomPairJunk_eq_zero_of_ne_empty P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne (hAdef ▸ hAne)
    have hcs := atomPairCodeState_correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
      hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne k n hAjunk
    set s0 := packState2
        (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k)
        (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k)
        (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) with hs0def
    set s1 := xSubStep P₀ P₁ hDiff0 splitX hSplitX
        (Nat.pair n (Nat.pair (if bx then 1 else 0) s0)) with hs1def
    have hidx0' : P₀.X (stateIdx0 s0) = A := by rw [hs0def, stateIdx0_packState2]; exact hcs.1
    have hidx1' : P₁.X (stateIdx1 s0) = B := by rw [hs0def, stateIdx1_packState2]; exact hcs.2
    by_cases hyj : yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k
        (if bx then 1 else 0) = 0
    · have hxnonjunk : stateJunk s1 = 0 := by
        have h' := hyj
        unfold yPseqAtomJunk yPseqAtomState at h'
        rw [← hs0def, ← hs1def] at h'
        rw [ySubStep_junk_eq, selectFn_one] at h'
        exact junk_eq_zero_of_selectFn_eq_zero h'
      obtain ⟨hxc0, hxc1⟩ := xSubStep_correct P₀ P₁ hDiff0 splitX hSplitX hD₀pos hD₀diff hD₀nomin
        hxSplit hidx0' hidx1' ihAB ihB bx hxnonjunk
      rw [← hs1def] at hxc0 hxc1
      rw [← hA1def] at hxc0
      rw [← hB1def] at hxc1
      have h : stateJunk (ySubStep P₀ P₁ hDiff1 splitY hSplitY (Nat.pair n (Nat.pair 1 s1))) = 0 := by
        have h' := hyj
        unfold yPseqAtomJunk yPseqAtomState at h'
        rwa [← hs0def, ← hs1def] at h'
      obtain ⟨hyc0, -⟩ := ySubStep_correct P₀ P₁ hDiff1 splitY hSplitY hD₁pos hD₁diff hD₁nomin
        hySplit hxc0 hxc1 hA1B1.symm hA1mem true h
      have hgoaleq : P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k
          (if bx then 1 else 0)) = (yStepG splitY A1 B1 (P₁.X n) true).1 := by
        show P₀.X (stateIdx0 (yPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k
          (if bx then 1 else 0))) = _
        unfold yPseqAtomState
        rw [← hs0def, ← hs1def]
        exact hyc0
      have hIF := yPseqAtomIdx_eq_inter_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hklt
        bx hyj
      rw [← hA1def] at hIF
      rw [← hgoaleq, hIF]
    · have hyj1 : yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k
          (if bx then 1 else 0) = 1 := by
        have := yPseqAtomJunk_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
          (bx := if bx then 1 else 0) (by cases bx <;> simp) n k
        omega
      have hs1junk_eq : stateJunk s1 = selectFn (if bx then 1 else 0)
          (emptyInterDec P₀ (Nat.pair (stateIdx0 s0) n))
          (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 s0) n)) := by
        rw [hs1def, xSubStep_junk_eq, hs0def, stateJunk_packState2, hAjunk, selectFn_zero]
      have hs1le : stateJunk s1 ≤ 1 := by
        rw [hs1junk_eq]
        exact selectFn_le_one (by cases bx <;> simp) (emptyInterDec_le_one P₀ _)
          (emptyDiffDec_le_one P₀ hDiff0 _)
      have hxnonjunk : stateJunk s1 = 0 := by
        by_contra hne
        have h3 : selectFn (if bx then 1 else 0) (emptyInterDec P₀ (Nat.pair (stateIdx0 s0) n))
            (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 s0) n)) = 1 := by
          rw [← hs1junk_eq]; omega
        have hA1e : A1 = ∅ := by
          rw [hA1def]
          by_cases hbx : bx = true
          · simp only [xStepG, xyStep, hbx, if_true]
            simp only [hbx, if_true, selectFn_one] at h3
            rw [← hidx0']
            exact (emptyInterDec_eq_one_iff P₀ hD₀pos hD₀nomin _ _).mp h3
          · simp only [xStepG, xyStep, hbx, Bool.false_eq_true, if_false]
            simp only [hbx, Bool.false_eq_true, if_false, selectFn_zero] at h3
            rw [← hidx0']
            exact (emptyDiffDec_eq_one_iff P₀ hDiff0 hD₀diff hD₀nomin _ _).mp h3
        exact hA1 hA1e
      have h : stateJunk (ySubStep P₀ P₁ hDiff1 splitY hSplitY (Nat.pair n (Nat.pair 1 s1))) = 1 := by
        have h' := hyj1
        unfold yPseqAtomJunk yPseqAtomState at h'
        rwa [← hs0def, ← hs1def] at h'
      have hyInter : emptyInterDec P₁ (Nat.pair (stateIdx1 s1) n) = 1 := by
        have h2 := h
        rw [ySubStep_junk_eq, hxnonjunk, selectFn_zero, selectFn_one] at h2
        exact h2
      obtain ⟨hxc0, hxc1⟩ := xSubStep_correct P₀ P₁ hDiff0 splitX hSplitX hD₀pos hD₀diff hD₀nomin
        hxSplit hidx0' hidx1' ihAB ihB bx hxnonjunk
      rw [← hs1def] at hxc0 hxc1
      rw [← hA1def] at hxc0
      rw [← hB1def] at hxc1
      have hB1Yempty : B1 ∩ (P₁.X n) = ∅ := by
        rw [← hxc1]
        exact (emptyInterDec_eq_one_iff P₁ hD₁pos hD₁nomin _ _).mp hyInter
      have hspec2 := hySplit hA1B1.symm hA1mem (P₁.X n)
      have h1empty : (yStepG splitY A1 B1 (P₁.X n) true).1 = ∅ := by
        show (splitY B1 A1 (P₁.X n)).1 = ∅
        exact hspec2.2.2.1.mp hB1Yempty
      have hdisjYP : A1 ∩ P₀.X
          (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z ⟨hzA1, hzYP⟩
        obtain (⟨k', hk'lt, hjunk', hz'⟩ | ⟨k', hk'lt, hjunk', hz'⟩) :=
          (mem_YPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
            hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 n z).mp
            hzYP
        · rcases eq_or_ne k' k with hkk' | hkk'
          · exfalso
            subst hkk'
            have hbxc : bx ≠ false := by
              intro hbxeq
              have hzero : (if bx then (1 : ℕ) else 0) = 0 := by rw [hbxeq]; simp
              rw [hzero] at hyj1
              omega
            have hz'' : z ∈ (xStepG splitX A B (P₀.X n) false).1 :=
              yPseqAtomIdx_subset_xStepGFst P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
                hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne false
                hjunk' hz'
            have hdisj := (xStepG_disjoint_of_ne hxSplit ihAB ihB (P₀.X n) (b := bx) (b' := false)
              hbxc).1
            rw [← hA1def] at hdisj
            exact absurd (Set.mem_inter hzA1 hz'') (by rw [hdisj]; simp)
          · have hAjunk' : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k' = 0 :=
              atomPairJunk_eq_zero_of_yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
                hSplitY false hjunk'
            obtain ⟨j, hj, hne⟩ := exists_deltaPair_ne_of_lt_of_ne hk'lt hklt hkk'
            have hdisj := (atomPairCodeState_disjoint P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
              hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne
              hD₁mne (n := n) (k := k') (k' := k) hAjunk' hAjunk ⟨j, hj, hne⟩).1
            have hzAk : z ∈ P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n
                k) := by
              rw [hcs.1]
              exact (xStepG_fst_subset splitX A B (P₀.X n) bx) (hA1def ▸ hzA1)
            have hzAk' : z ∈ P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n
                k') :=
              yPseqAtomIdx_subset_atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
                hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne false
                hjunk' hz'
            exact absurd (Set.mem_inter hzAk' hzAk) (by rw [hdisj]; simp)
        · rcases eq_or_ne k' k with hkk' | hkk'
          · exfalso
            subst hkk'
            have hbxc : bx ≠ true := by
              intro hbxeq
              have hone : (if bx then (1 : ℕ) else 0) = 1 := by rw [hbxeq]; simp
              rw [hone] at hyj1
              omega
            have hz'' : z ∈ (xStepG splitX A B (P₀.X n) true).1 :=
              yPseqAtomIdx_subset_xStepGFst P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
                hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne true
                hjunk' hz'
            have hdisj := (xStepG_disjoint_of_ne hxSplit ihAB ihB (P₀.X n) (b := bx) (b' := true)
              hbxc).1
            rw [← hA1def] at hdisj
            exact absurd (Set.mem_inter hzA1 hz'') (by rw [hdisj]; simp)
          · have hAjunk' : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k' = 0 :=
              atomPairJunk_eq_zero_of_yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
                hSplitY true hjunk'
            obtain ⟨j, hj, hne⟩ := exists_deltaPair_ne_of_lt_of_ne hk'lt hklt hkk'
            have hdisj := (atomPairCodeState_disjoint P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
              hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne
              hD₁mne (n := n) (k := k') (k' := k) hAjunk' hAjunk ⟨j, hj, hne⟩).1
            have hzAk : z ∈ P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n
                k) := by
              rw [hcs.1]
              exact (xStepG_fst_subset splitX A B (P₀.X n) bx) (hA1def ▸ hzA1)
            have hzAk' : z ∈ P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n
                k') :=
              yPseqAtomIdx_subset_atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
                hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne true
                hjunk' hz'
            exact absurd (Set.mem_inter hzAk' hzAk) (by rw [hdisj]; simp)
      rw [h1empty, hdisjYP]

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 in
/-- **Two-branch closed form, generalized to an arbitrary `δ`** (not just a bounded bit-source `k <
4 ^ n`): completes `yStepG_fst_eq_inter_YPseqCode`'s `true`-only fact (specialized to the `X`-side
bit `(δ n).1`, exactly as `Exercise812c.lean`'s `yStep_fst_succ_eq` fixes it) into a full
`genAtom`-shaped closed step at *either* sign of the `Y`-sub-step — the `false` branch is derived
algebraically from the `true` branch plus `SplitSpec'`'s `I ∪ J = A1`/`I ∩ J = ∅`, mirroring
`xStepG_snd_succ_eq_XPseqCode` exactly (with the roles of `hySplit`/`hxSplit` swapped). -/
theorem yStepG_fst_succ_eq_YPseqCode (δ : ℕ → Bool × Bool) (n : ℕ) (b : Bool) :
    (yStepG splitY
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) (δ n).1).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) (δ n).1).2
        (P₁.X n) b).1 =
      (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) (δ n).1).1 ∩
        (if b then P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n)
          else D₀.master \
            P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n)) := by
  obtain ⟨ihAB, ihA, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne δ n
  set A := (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1 with hAdef
  set B := (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 with hBdef
  set A1 := (xStepG splitX A B (P₀.X n) (δ n).1).1 with hA1def
  set B1 := (xStepG splitX A B (P₀.X n) (δ n).1).2 with hB1def
  set YP := P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) with hYPdef
  have hspec1 := hxSplit ihAB ihB (P₀.X n)
  have hA1B1 : A1 = ∅ ↔ B1 = ∅ := by
    rw [hA1def, hB1def]
    by_cases hbx : (δ n).1 = true
    · simp only [xStepG, xyStep, hbx, if_true]; exact hspec1.2.2.1
    · simp only [xStepG, xyStep, hbx, Bool.false_eq_true, if_false]; exact hspec1.2.2.2.1
  have hA1mem : A1 = ∅ ∨ D₀.mem A1 := by
    rw [hA1def]
    by_cases hbx : (δ n).1 = true
    · simp only [xStepG, xyStep, hbx, if_true]; exact inter_mem_or_empty hD₀pos ihA (P₀.mem_X n)
    · simp only [xStepG, xyStep, hbx, Bool.false_eq_true, if_false]
      exact diff_mem_or_empty hD₀diff ihA (P₀.mem_X n)
  have hspec := hySplit hA1B1.symm hA1mem (P₁.X n)
  have hJeqTrue : (yStepG splitY A1 B1 (P₁.X n) true).1 = A1 ∩ YP :=
    yStepG_fst_eq_inter_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 δ n (δ n).1
  by_cases hb : b = true
  · rw [hb, if_pos rfl]; exact hJeqTrue
  · rw [Bool.not_eq_true] at hb; subst hb
    rw [if_neg (by simp)]
    have hJeq : (yStepG splitY A1 B1 (P₁.X n) false).1 = A1 \ YP := by
      have hunion :
          (yStepG splitY A1 B1 (P₁.X n) true).1 ∪ (yStepG splitY A1 B1 (P₁.X n) false).1 = A1 := by
        simp only [yStepG, xyStep, Prod.swap]; exact hspec.2.2.2.2.1
      have hinter :
          (yStepG splitY A1 B1 (P₁.X n) true).1 ∩ (yStepG splitY A1 B1 (P₁.X n) false).1 = ∅ := by
        simp only [yStepG, xyStep, Prod.swap]; exact hspec.2.2.2.2.2
      ext x
      constructor
      · intro hxJ
        have hxA1 : x ∈ A1 := hunion ▸ Or.inr hxJ
        refine ⟨hxA1, fun hxYP => ?_⟩
        have hxI : x ∈ (yStepG splitY A1 B1 (P₁.X n) true).1 := hJeqTrue ▸ Set.mem_inter hxA1 hxYP
        exact absurd (Set.mem_inter hxI hxJ) (by rw [hinter]; simp)
      · rintro ⟨hxA1, hxnYP⟩
        rw [← hunion] at hxA1
        rcases hxA1 with hxI | hxJ
        · exact absurd (hJeqTrue ▸ hxI : x ∈ A1 ∩ YP).2 hxnYP
        · exact hxJ
    rw [hJeq]
    have hsub : A1 ⊆ D₀.master := (xStepG_fst_subset splitX A B (P₀.X n) (δ n).1).trans
      (atomPairG_fst_subset_master D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff splitX hxSplit
        P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne δ n)
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hsub hx1, hx2⟩
    · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩

include hD₀pos hD₀diff hxSplit hD₁pos hD₁diff hySplit hD₀mne hD₁mne in
/-- **The odd-depth half-step identity for `combinedXCode`**, code-level analogue of
`Exercise812c.lean`'s `genAtom_combinedX_succ_eq`: given `atomPairG δ n`'s `α`-side agrees with
`genAtom combinedXCode` at the even depth `2 * n`, it also agrees at the odd depth `2 * n + 1` with
the `X`-sub-step's own split-side output — elementary algebra plus `atomPairG_fst_subset_master`,
no new disjointness content (the `Y`-sub-step closed form `yStepG_fst_succ_eq_YPseqCode` is what
supplies the genuinely new content, used one level up in `atomPairG_fst_eq_genAtomCode`). -/
theorem genAtom_combinedXCode_succ_eq (δ : ℕ → Bool × Bool) (n : ℕ)
    (hn : (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1 =
      genAtom (combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0) D₀.master
        (combinedδ δ) (2 * n)) :
    genAtom (combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0) D₀.master
        (combinedδ δ) (2 * n + 1) =
      (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) (δ n).1).1 := by
  rw [genAtom_succ', ← hn, combinedδ_even, combinedXCode_even]
  have hAsub : (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1 ⊆ D₀.master :=
    atomPairG_fst_subset_master D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff splitX hxSplit
      P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne δ n
  simp only [xStepG, xyStep]
  rcases Bool.eq_false_or_eq_true (δ n).1 with hb | hb
  · simp only [hb, if_true]
  · simp only [hb, Bool.false_eq_true, if_false]
    exact inter_diff_eq_diff_of_subset hAsub

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 in
/-- **The odd-depth half-step identity for `combinedYCode`**, code-level analogue of
`Exercise812c.lean`'s `genAtom_combinedY_succ_eq`: given `atomPairG δ n`'s `β`-side agrees with
`genAtom combinedYCode` at the even depth `2 * n`, it also agrees at the odd depth `2 * n + 1` with
the `X`-sub-step's own direct-refine `β`-side output, via `xStepG_snd_succ_eq_XPseqCode`. -/
theorem genAtom_combinedYCode_succ_eq (δ : ℕ → Bool × Bool) (n : ℕ)
    (hn : (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 =
      genAtom (combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1) D₁.master
        (combinedδ δ) (2 * n)) :
    genAtom (combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1) D₁.master
        (combinedδ δ) (2 * n + 1) =
      (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) (δ n).1).2 := by
  rw [genAtom_succ', ← hn, combinedδ_even, combinedYCode_even]
  exact (xStepG_snd_succ_eq_XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 δ n (δ n).1).symm

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 in
/-- **Headline closed form, `α`-side** (code-level analogue of `Exercise812c.lean`'s
`atomPair_fst_eq_genAtom`): `atomPairG δ n`'s `α`-side coincides with `genAtom` over the interleaved
family `combinedXCode` at the doubled depth `2 * n`. Proved by induction, each step performing the
`X`-sub-step half-step rewrite (`genAtom_combinedXCode_succ_eq`, elementary) then the `Y`-sub-step's
closed form (`yStepG_fst_succ_eq_YPseqCode`). -/
theorem atomPairG_fst_eq_genAtomCode (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1 =
      genAtom (combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0) D₀.master
        (combinedδ δ) (2 * n) := by
  induction n with
  | zero => rfl
  | succ n hIH =>
      have hodd := genAtom_combinedXCode_succ_eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hxSplit hD₁pos hD₁diff hySplit hD₀mne hD₁mne hUnion0 δ n hIH
      have hstep := yStepG_fst_succ_eq_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 δ n
        (δ n).2
      have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      rw [atomPairG_succ_eq, hstep, h2, genAtom_succ', combinedδ_odd, combinedXCode_odd, hodd]

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 in
/-- **Headline closed form, `β`-side** (code-level analogue of `Exercise812c.lean`'s
`atomPair_snd_eq_genAtom`): `atomPairG δ n`'s `β`-side coincides with `genAtom` over the interleaved
family `combinedYCode` at depth `2 * n`, via `genAtom_combinedYCode_succ_eq` then the `Y`-sub-step's
elementary direct `β`-side output. -/
theorem atomPairG_snd_eq_genAtomCode (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 =
      genAtom (combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1) D₁.master
        (combinedδ δ) (2 * n) := by
  induction n with
  | zero => rfl
  | succ n hIH =>
      have hodd := genAtom_combinedYCode_succ_eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 δ n
        hIH
      have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      rw [atomPairG_succ_eq, h2, genAtom_succ', combinedδ_odd, combinedYCode_odd, hodd]
      obtain ⟨ihAB, -, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
        hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne δ n
      have hB1sub := (xStepG_snd_subset hxSplit ihAB ihB (P₀.X n) (δ n).1).trans
        (atomPairG_snd_subset_master D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff splitX
          hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne δ n)
      simp only [yStepG, xyStep, Prod.swap]
      rcases Bool.eq_false_or_eq_true (δ n).2 with hb | hb
      · simp only [hb, if_true]
      · simp only [hb, Bool.false_eq_true, if_false]
        exact (inter_diff_eq_diff_of_subset hB1sub).symm

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
/-- **The even-index case of `hcore`**, code-level analogue of `Exercise812c.lean`'s `hcore_even`:
for any `δ' : ℕ → Bool` and any `n`, `genAtom combinedXCode δ' (2*n) = ∅ ↔
genAtom combinedYCode δ' (2*n) = ∅`. De-interleave `δ'`, rewrite both `genAtom`s back to
`atomPairG (deinterleaveδ δ') n`'s two sides via `atomPairG_fst_eq_genAtomCode`/
`atomPairG_snd_eq_genAtomCode`, then close with `atomPairG_invariant`'s clause (a). -/
theorem hcoreCode_even (δ' : ℕ → Bool) (n : ℕ) :
    genAtom (combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0) D₀.master δ'
        (2 * n) = ∅ ↔
      genAtom (combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1) D₁.master
        δ' (2 * n) = ∅ := by
  rw [← combinedδ_deinterleaveδ δ',
    ← atomPairG_fst_eq_genAtomCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 (deinterleaveδ δ') n,
    ← atomPairG_snd_eq_genAtomCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 (deinterleaveδ δ') n]
  exact (atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff splitX hxSplit P₀.X
    P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deinterleaveδ δ') n).1

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
/-- **The odd-index case of `hcore`**, code-level analogue of `Exercise812c.lean`'s `hcore_odd`:
de-interleave `δ'`, rewrite both `genAtom`s at the odd depth `2 * n + 1` down to the `X`-sub-step's
own two sides via the odd-depth half-step identities (fed by the even-depth closed forms for their
`hn` hypotheses), then close directly with `xStepG_spec`'s matching-emptiness clause. -/
theorem hcoreCode_odd (δ' : ℕ → Bool) (n : ℕ) :
    genAtom (combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0) D₀.master δ'
        (2 * n + 1) = ∅ ↔
      genAtom (combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1) D₁.master
        δ' (2 * n + 1) = ∅ := by
  rw [← combinedδ_deinterleaveδ δ',
    genAtom_combinedXCode_succ_eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hxSplit hD₁pos hD₁diff hySplit hD₀mne hD₁mne hUnion0 (deinterleaveδ δ') n
      (atomPairG_fst_eq_genAtomCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
        (deinterleaveδ δ') n),
    genAtom_combinedYCode_succ_eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 (deinterleaveδ δ') n
      (atomPairG_snd_eq_genAtomCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1
        (deinterleaveδ δ') n)]
  exact (xStepG_spec D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff splitX hxSplit P₀.X P₁.X
    P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deinterleaveδ δ') n).1.symm

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
/-- **`hcore`**, code-level analogue of `Exercise812c.lean`'s `hcore`, final assembly: for any
`δ' : ℕ → Bool` and any `n`, `genAtom combinedXCode δ' n = ∅ ↔ genAtom combinedYCode δ' n = ∅` — the
`hcore` hypothesis `Theorem88.lean`'s `transfer_dir` needs for the interleaved code families
`combinedXCode`/`combinedYCode`. Pure glue: a parity case split on `n` matching `hcore_even`/
`hcore_odd`. -/
theorem hcoreCode (δ' : ℕ → Bool) (n : ℕ) :
    genAtom (combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0) D₀.master δ'
        n = ∅ ↔
      genAtom (combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1) D₁.master
        δ' n = ∅ := by
  rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hn | hn
  · rw [show n = 2 * (n / 2) from by omega]
    exact hcoreCode_even P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin
      hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 δ' (n / 2)
  · rw [show n = 2 * (n / 2) + 1 from by omega]
    exact hcoreCode_odd P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin
      hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 δ' (n / 2)

end CombinedCode

/-! ### Exercise 8.12(d)(5)(b)(iv): the headline transfer theorems

Instantiates `Theorem88.lean`'s fully generic `transfer_dir` with `Z1 := combinedXCode`,
`M1 := D₀.master`, `Z2 := combinedYCode`, `M2 := D₁.master`, and `(b)(iii)`'s `hcoreCode`,
transcribing `Exercise812c.lean`'s own `transfer_empty_combined`/`transfer_subset_combined`/
`transfer_double_subset_combined`/`transfer_inter_eq_combined` wrappers one-for-one with
`combinedX ↦ combinedXCode`, `combinedY ↦ combinedYCode`, `hcore ↦ hcoreCode`. The headline
deliverable then specializes each even/even and odd/odd index pair back down to plain statements
about `P₀.X`/`XPseqCode` and `YPseqCode`/`P₁.X`, discharging the `∩ master` bookkeeping with
`D₀.sub_master`/`D₁.sub_master` applied to `P₀.mem_X`/`P₁.mem_X` directly — a genuine
simplification over `Exercise812c.lean`'s own proof: since every value of `combinedXCode`/
`combinedYCode` is literally `P₀.X _`/`P₁.X _` for some index, no separate `XPseq_subset_master`/
`YPseq_subset_master`-style theorem is needed, `ComputablePresentation.mem_X` already covers every
case (even or odd) uniformly. -/

section CombinedCodeTransfer

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

/-- `combinedXCode i` is always `⊆ D₀.master`: every value, at either parity, is literally
`P₀.X _` for some index, so `D₀.sub_master`/`P₀.mem_X` closes both branches uniformly (unlike
`Exercise812c.lean`'s `combinedX_subset_master`, no case split on parity or `hXmem`/`YPseq_subset_
master`-style helper theorem is needed). -/
theorem combinedXCode_subset_master (i : ℕ) :
    combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i ⊆ D₀.master := by
  unfold combinedXCode
  split <;> exact D₀.sub_master (P₀.mem_X _)

/-- `combinedYCode i` is always `⊆ D₁.master`, symmetric to `combinedXCode_subset_master`. -/
theorem combinedYCode_subset_master (i : ℕ) :
    combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i ⊆ D₁.master := by
  unfold combinedYCode
  split <;> exact D₁.sub_master (P₁.mem_X _)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
theorem transfer_empty_combinedCode {cs : List (ℕ × Bool)} {n : ℕ} (hn : ∀ p ∈ cs, p.1 < n) :
    {x ∈ D₀.master | ∀ p ∈ cs,
        (p.2 = true ↔ x ∈ combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
          p.1)}.Nonempty ↔
      {y ∈ D₁.master | ∀ p ∈ cs,
        (p.2 = true ↔ y ∈ combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
          p.1)}.Nonempty := by
  have hc := hcoreCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin
    hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
  have hc' : ∀ δ n,
      genAtom (combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1) D₁.master
          δ n = ∅ ↔
        genAtom (combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0) D₀.master
          δ n = ∅ :=
    fun δ n => (hc δ n).symm
  exact ⟨transfer_dir (combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0)
      D₀.master (combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1) D₁.master
      hc hn,
    transfer_dir (combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1)
      D₁.master (combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0) D₀.master
      hc' hn⟩

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
theorem transfer_subset_combinedCode (i j : ℕ) :
    D₀.master ∩ combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i ⊆
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j ↔
      D₁.master ∩ combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i ⊆
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j := by
  have key := transfer_empty_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
    (cs := [(i, true), (j, false)]) (n := max i j + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) <;> simp)
  have hLHS : {x ∈ D₀.master | ∀ p ∈ [(i, true), (j, false)],
      (p.2 = true ↔ x ∈ combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
        p.1)}
      = (D₀.master ∩ combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i) \
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ D₁.master | ∀ p ∈ [(i, true), (j, false)],
      (p.2 = true ↔ y ∈ combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
        p.1)}
      = (D₁.master ∩ combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i) \
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j := by
    ext y
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [hLHS, hRHS] at key
  rw [← Set.sdiff_eq_empty, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
theorem transfer_double_subset_combinedCode (i j k : ℕ) :
    D₀.master ∩ combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i ∩
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j ⊆
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ↔
      D₁.master ∩ combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i ∩
          combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j ⊆
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k := by
  have key := transfer_empty_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
    (cs := [(i, true), (j, true), (k, false)]) (n := max i (max j k) + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl) <;>
          simp [(Nat.le_max_left j k).trans (Nat.le_max_right i (max j k)),
            (Nat.le_max_right j k).trans (Nat.le_max_right i (max j k))])
  have hLHS : {x ∈ D₀.master | ∀ p ∈ [(i, true), (j, true), (k, false)],
      (p.2 = true ↔ x ∈ combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
        p.1)}
      = (D₀.master ∩ combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i ∩
          combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j) \
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ D₁.master | ∀ p ∈ [(i, true), (j, true), (k, false)],
      (p.2 = true ↔ y ∈ combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
        p.1)}
      = (D₁.master ∩ combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i ∩
          combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j) \
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k := by
    ext y
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [hLHS, hRHS] at key
  rw [← Set.sdiff_eq_empty, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
theorem transfer_inter_eq_combinedCode (i j k : ℕ)
    (hi : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i ⊆ D₀.master)
    (hk : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ⊆ D₀.master) :
    combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i ∩
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j =
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ↔
      combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i ∩
          combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j =
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k := by
  have h1 : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ⊆
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i ↔
      combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k ⊆
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i := by
    have := transfer_subset_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
      hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 k i
    rwa [Set.inter_eq_self_of_subset_right hk,
      Set.inter_eq_self_of_subset_right
        (combinedYCode_subset_master P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
          k)] at this
  have h2 : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ⊆
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j ↔
      combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k ⊆
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j := by
    have := transfer_subset_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
      hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 k j
    rwa [Set.inter_eq_self_of_subset_right hk,
      Set.inter_eq_self_of_subset_right
        (combinedYCode_subset_master P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
          k)] at this
  have h3 : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i ∩
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j ⊆
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ↔
      combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i ∩
          combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j ⊆
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k := by
    have := transfer_double_subset_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
      i j k
    rwa [Set.inter_eq_self_of_subset_right hi,
      Set.inter_eq_self_of_subset_right
        (combinedYCode_subset_master P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
          i)] at this
  constructor
  · intro heq
    have hki : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ⊆
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i :=
      heq ▸ Set.inter_subset_left
    have hkj : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ⊆
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j :=
      heq ▸ Set.inter_subset_right
    have hijk : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i ∩
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j ⊆
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k := heq ▸ subset_rfl
    exact Set.Subset.antisymm (h3.mp hijk) (Set.subset_inter (h1.mp hki) (h2.mp hkj))
  · intro heq
    have hki : combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k ⊆
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i :=
      heq ▸ Set.inter_subset_left
    have hkj : combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k ⊆
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j :=
      heq ▸ Set.inter_subset_right
    have hijk : combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i ∩
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j ⊆
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k := heq ▸ subset_rfl
    exact Set.Subset.antisymm (h3.mpr hijk) (Set.subset_inter (h1.mpr hki) (h2.mpr hkj))

/-! ### The headline facts: specializing `transfer_*_combinedCode` to even/even and odd/odd
indices

The actual deliverable of Exercise 8.12(d)(5)(b): plain statements about `P₀.X`/`XPseqCode` (from
the even-index specialization) and `YPseqCode`/`P₁.X` (from the odd-index specialization), needed
for `(d)(5)(c)`–`(e)`'s `DomainIsoCode` assembly. -/

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
theorem X_subset_iff_XPseqCode_subset (i j : ℕ) :
    P₀.X i ⊆ P₀.X j ↔
      P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i) ⊆
        P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j) := by
  have key := transfer_subset_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 (2 * i)
    (2 * j)
  rw [combinedXCode_even, combinedXCode_even, combinedYCode_even, combinedYCode_even,
    Set.inter_eq_self_of_subset_right (D₀.sub_master (P₀.mem_X i)),
    Set.inter_eq_self_of_subset_right
      (D₁.sub_master (P₁.mem_X
        (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i)))] at key
  exact key

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
theorem YPseqCode_subset_iff_Y_subset (i j : ℕ) :
    P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i) ⊆
        P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j) ↔
      P₁.X i ⊆ P₁.X j := by
  have key := transfer_subset_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
    (2 * i + 1) (2 * j + 1)
  rw [combinedXCode_odd, combinedXCode_odd, combinedYCode_odd, combinedYCode_odd,
    Set.inter_eq_self_of_subset_right
      (D₀.sub_master (P₀.mem_X
        (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i))),
    Set.inter_eq_self_of_subset_right (D₁.sub_master (P₁.mem_X i))] at key
  exact key

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
theorem X_inter_eq_iff_XPseqCode_inter_eq (i j k : ℕ) :
    P₀.X i ∩ P₀.X j = P₀.X k ↔
      P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i) ∩
          P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j) =
        P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k) := by
  have key := transfer_inter_eq_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
    (2 * i) (2 * j) (2 * k)
    (combinedXCode_subset_master P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 (2 * i))
    (combinedXCode_subset_master P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 (2 * k))
  rw [combinedXCode_even, combinedXCode_even, combinedXCode_even, combinedYCode_even,
    combinedYCode_even, combinedYCode_even] at key
  exact key

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
theorem YPseqCode_inter_eq_iff_Y_inter_eq (i j k : ℕ) :
    P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i) ∩
        P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j) =
        P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k) ↔
      P₁.X i ∩ P₁.X j = P₁.X k := by
  have key := transfer_inter_eq_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
    (2 * i + 1) (2 * j + 1) (2 * k + 1)
    (combinedXCode_subset_master P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
      (2 * i + 1))
    (combinedXCode_subset_master P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
      (2 * k + 1))
  rw [combinedXCode_odd, combinedXCode_odd, combinedXCode_odd, combinedYCode_odd,
    combinedYCode_odd, combinedYCode_odd] at key
  exact key

end CombinedCodeTransfer

/-! ### Exercise 8.12(d)(5)(c): cross-family order and equality facts

Generalizes `Exercise812c.lean`'s `X_subset_YPseq_iff_XPseq_subset_Y`/
`YPseq_subset_X_iff_Y_subset_XPseq`/`XPseq_eq_Y_iff_X_eq_YPseq` ((c)(vii)(3)/(4)) to the code
level. Needs no new proof machinery beyond `(d)(5)(b)`'s transfer facts — each is a direct
specialization of `transfer_subset_combinedCode` at *mixed* even/odd (resp. odd/even) index
pairs. -/

section CombinedCodeCrossFamily

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
/-- **Exercise 8.12(d)(5)(c)(i), cross-parity order fact (`even`/`odd` mix).** `P₀.X i ⊆ P₀.X
(YPseqCode … j) ↔ P₁.X (XPseqCode … i) ⊆ P₁.X j`: code-level analogue of `Exercise812c.lean`'s
`X_subset_YPseq_iff_XPseq_subset_Y` — a direct specialization of `transfer_subset_combinedCode` at
the mixed indices `(2i, 2j+1)` (`combinedXCode`/`combinedYCode` at an even and an odd index
respectively), simplified by the same `Set.inter_eq_self_of_subset_right` bookkeeping as
`(d)(5)(b)(iv)`'s same-parity headline facts. No new proof machinery —
`transfer_subset_combinedCode` already holds for arbitrary index pairs. -/
theorem X_subset_YPseqCode_iff_XPseqCode_subset_Y (i j : ℕ) :
    P₀.X i ⊆ P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j) ↔
      P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i) ⊆ P₁.X j := by
  have key := transfer_subset_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 (2 * i)
    (2 * j + 1)
  rw [combinedXCode_even, combinedXCode_odd, combinedYCode_even, combinedYCode_odd,
    Set.inter_eq_self_of_subset_right (D₀.sub_master (P₀.mem_X i)),
    Set.inter_eq_self_of_subset_right
      (D₁.sub_master (P₁.mem_X
        (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i)))] at key
  exact key

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
/-- **Exercise 8.12(d)(5)(c)(ii), cross-parity order fact, other mix.** `P₀.X (YPseqCode … i) ⊆
P₀.X j ↔ P₁.X i ⊆ P₁.X (XPseqCode … j)`: code-level analogue of `Exercise812c.lean`'s
`YPseq_subset_X_iff_Y_subset_XPseq` — the symmetric specialization of
`transfer_subset_combinedCode` at `(2i + 1, 2j)`. -/
theorem YPseqCode_subset_X_iff_Y_subset_XPseqCode (i j : ℕ) :
    P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i) ⊆ P₀.X j ↔
      P₁.X i ⊆ P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j) := by
  have key := transfer_subset_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
    (2 * i + 1) (2 * j)
  rw [combinedXCode_odd, combinedXCode_even, combinedYCode_odd, combinedYCode_even,
    Set.inter_eq_self_of_subset_right
      (D₀.sub_master (P₀.mem_X
        (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i))),
    Set.inter_eq_self_of_subset_right (D₁.sub_master (P₁.mem_X i))] at key
  exact key

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
/-- **Exercise 8.12(d)(5)(c)(iii), the cross-parity `embed_eq_iff` analogue.** `P₁.X (XPseqCode …
j) = P₁.X k ↔ P₀.X j = P₀.X (YPseqCode … k)`: code-level analogue of `Exercise812c.lean`'s
`XPseq_eq_Y_iff_X_eq_YPseq` — pure packaging of `(c)(i)`/`(c)(ii)` via `Set.Subset.antisymm` in
each direction, no new mathematical content. Needed because `(d)(5)(d)`'s `toD1Code`/`toD0Code`
`up_mem` case must rename a covering witness produced by `P₀.surj`/`P₁.surj` back into the
`XPseqCode`/`YPseqCode` "coordinates" that the filter `x`/`y` actually testifies about. -/
theorem XPseqCode_eq_Y_iff_X_eq_YPseqCode (j k : ℕ) :
    P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j) = P₁.X k ↔
      P₀.X j = P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k) := by
  constructor
  · intro h
    exact Set.Subset.antisymm
      ((X_subset_YPseqCode_iff_XPseqCode_subset_Y P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
        hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
        hUnion0 hUnion1 j k).mpr h.subset)
      ((YPseqCode_subset_X_iff_Y_subset_XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
        hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
        hUnion0 hUnion1 k j).mpr h.symm.subset)
  · intro h
    exact Set.Subset.antisymm
      ((X_subset_YPseqCode_iff_XPseqCode_subset_Y P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
        hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
        hUnion0 hUnion1 j k).mp h.subset)
      ((YPseqCode_subset_X_iff_Y_subset_XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
        hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
        hUnion0 hUnion1 k j).mp h.symm.subset)

end CombinedCodeCrossFamily

/-! ### Exercise 8.12(d)(5)(d): `toD1Code`/`toD0Code`, the generalized elementwise maps

Generalizes `Exercise812c.lean`'s `toD1`/`toD0` ((c)(vii)(4)/(5)) to the code level. Split into the
`up_mem` helper lemmas (the only genuinely two-sided step) and the full assembly `def`s, one pair
per direction. -/

section ToD1CodeUpMem

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
/-- **Exercise 8.12(d)(5)(d)(i).** The standalone `up_mem` obligation for `toD1Code`'s membership
predicate `fun T => ∃ n, T = P₁.X (XPseqCode … n) ∧ x.mem (P₀.X n)`, stated at the exact type
`Element.up_mem` needs so it plugs directly into the final structure literal. Code-level analogue
of `Exercise812c.lean`'s `toD1.up_mem`, but needing only **one** `surj` call (not two): `P₁.surj`
names the arbitrary target `T2` as some `P₁.X k`; `(d)(5)(c)(i)`'s cross-parity order fact then
transports `x.mem (P₀.X i)` across to `x.mem (P₀.X (YPseqCode … k))` — already literally
`x.mem (P₀.X j)` for the explicit witness `j := YPseqCode … k`, no further covering search needed;
`(d)(5)(c)(iii)`'s `XPseqCode_eq_Y_iff_X_eq_YPseqCode`, applied at the self-referential pair
`(YPseqCode … k, k)` whose "other side" is `rfl`, supplies the closing index equation for free. -/
theorem toD1Code_up_mem (x : D₀.Element) {T1 T2 : Set β}
    (h1 : ∃ n, T1 = P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n) ∧
      x.mem (P₀.X n))
    (hD1T2 : D₁.mem T2) (hT1T2 : T1 ⊆ T2) :
    ∃ n, T2 = P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n) ∧
      x.mem (P₀.X n) := by
  obtain ⟨i, rfl, hxi⟩ := h1
  obtain ⟨k, hk⟩ := P₁.surj hD1T2
  subst hk
  have hsub : P₀.X i ⊆
      P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k) :=
    (X_subset_YPseqCode_iff_XPseqCode_subset_Y P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
      i k).mpr hT1T2
  have hxYk :
      x.mem (P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k)) :=
    x.up_mem hxi
      (YPseqCode_mem_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 k)
      hsub
  refine ⟨YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k, ?_, hxYk⟩
  exact ((XPseqCode_eq_Y_iff_X_eq_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
    (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k) k).mpr rfl).symm

end ToD1CodeUpMem

section ToD1Code

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 in
/-- **Exercise 8.12(d)(5)(d)(ii).** `toD1Code : D₀.Element → D₁.Element`, the code-level pushforward
filter `{T | ∃ n, T = P₁.X (XPseqCode … n) ∧ x.mem (P₀.X n)}` — generalizes `Exercise812c.lean`'s
`toD1` ((c)(vii)(4)). `sub` cites `(d)(4)`'s `XPseqCode_mem_unconditional` directly; `master_mem`
cites `(d)(5)(a)`'s `XPseqCode_zero` at the witness `n = 0`, using `hX0` to identify `P₀.X 0` with
`D₀.master`. `inter_mem` needs **no** covering search (unlike `toD1`'s `exists_inter_index_X`):
given `hxi : x.mem (P₀.X i)`/`hxj : x.mem (P₀.X j)`, `x.inter_mem hxi hxj`/`x.sub` shows
`P₀.X i ∩ P₀.X j` is already `D₀`-genuine, so `P₀.surj` names it as some `P₀.X m` outright,
`P₀.inter_spec` reads this off as the closed-form index equation `P₀.X (P₀.inter i j) = P₀.X i ∩
P₀.X j`, and `(d)(5)(b)(iv)`'s `X_inter_eq_iff_XPseqCode_inter_eq` transports the same equation
across to `XPseqCode`, so `P₀.inter i j` is directly the witness index needed. `up_mem` is exactly
`(d)(5)(d)(i)`'s `toD1Code_up_mem`. -/
def toD1Code (x : D₀.Element) : D₁.Element where
  mem T := ∃ n, T = P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n) ∧
    x.mem (P₀.X n)
  sub := fun ⟨n, hn, _⟩ =>
    hn ▸ XPseqCode_mem_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
      hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 n
  master_mem := ⟨0, (XPseqCode_zero P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 hX0).symm,
    by rw [hX0]; exact x.master_mem⟩
  inter_mem := by
    rintro T1 T2 ⟨i, rfl, hxi⟩ ⟨j, rfl, hxj⟩
    have hDmem : D₀.mem (P₀.X i ∩ P₀.X j) := x.sub (x.inter_mem hxi hxj)
    obtain ⟨m, hm⟩ := P₀.surj hDmem
    have hcons : ∃ k, P₀.X k ⊆ P₀.X i ∩ P₀.X j := ⟨m, hm.le⟩
    have hinterEq : P₀.X (P₀.inter i j) = P₀.X i ∩ P₀.X j := P₀.inter_spec hcons
    refine ⟨P₀.inter i j, ?_, ?_⟩
    · exact (X_inter_eq_iff_XPseqCode_inter_eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
        hUnion1 i j (P₀.inter i j)).mp hinterEq.symm
    · rw [hinterEq]; exact x.inter_mem hxi hxj
  up_mem := toD1Code_up_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
    hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 x

end ToD1Code

section ToD0CodeUpMem

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
/-- **Exercise 8.12(d)(5)(d)(iii).** The standalone `up_mem` obligation for `toD0Code`'s membership
predicate `fun S => ∃ n, S = P₀.X (YPseqCode … n) ∧ y.mem (P₁.X n)`, the exact mirror of
`(d)(5)(d)(i)`'s `toD1Code_up_mem` for the `D₁ → D₀` direction: destructure `h1` as `⟨i, rfl, hyi⟩`;
`P₀.surj` names the arbitrary target `S2` as some `P₀.X k`; `(d)(5)(c)(ii)`'s
`YPseqCode_subset_X_iff_Y_subset_XPseqCode` turns `hS1S2 : P₀.X (YPseqCode … i) ⊆ P₀.X k` into
`P₁.X i ⊆ P₁.X (XPseqCode … k)`; `y.up_mem hyi (XPseqCode_mem_unconditional k) this` gives
`y.mem (P₁.X (XPseqCode … k))` — already literally `y.mem (P₁.X j)` for the explicit witness
`j := XPseqCode … k`, no covering search needed; `(d)(5)(c)(iii)`'s
`XPseqCode_eq_Y_iff_X_eq_YPseqCode`, applied at the self-referential pair `(k, XPseqCode … k)`
whose "other side" is `rfl`, supplies the closing index equation `P₀.X k = P₀.X (YPseqCode …
(XPseqCode … k))` for free — note no `.symm` is needed here, unlike `toD1Code_up_mem`, since the
goal orientation already matches `XPseqCode_eq_Y_iff_X_eq_YPseqCode`'s `.mp` output directly. -/
theorem toD0Code_up_mem (y : D₁.Element) {S1 S2 : Set α}
    (h1 : ∃ n, S1 = P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) ∧
      y.mem (P₁.X n))
    (hD0S2 : D₀.mem S2) (hS1S2 : S1 ⊆ S2) :
    ∃ n, S2 = P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) ∧
      y.mem (P₁.X n) := by
  obtain ⟨i, rfl, hyi⟩ := h1
  obtain ⟨k, hk⟩ := P₀.surj hD0S2
  subst hk
  have hsub : P₁.X i ⊆
      P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k) :=
    (YPseqCode_subset_X_iff_Y_subset_XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
      i k).mp hS1S2
  have hyXk :
      y.mem (P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k)) :=
    y.up_mem hyi
      (XPseqCode_mem_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 k)
      hsub
  refine ⟨XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k, ?_, hyXk⟩
  exact (XPseqCode_eq_Y_iff_X_eq_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
    k (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k)).mp rfl

end ToD0CodeUpMem

section ToD0Code

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in
/-- **Exercise 8.12(d)(5)(d)(iv).** `toD0Code : D₁.Element → D₀.Element`, the code-level pullback
filter `{S | ∃ n, S = P₀.X (YPseqCode … n) ∧ y.mem (P₁.X n)}` — exact mirror of `(d)(5)(d)(ii)`'s
`toD1Code` for the `D₁ → D₀` direction. `sub` cites `(d)(4)`'s `YPseqCode_mem_unconditional`
directly; `master_mem` cites `(d)(5)(a)`'s `YPseqCode_zero` at the witness `n = 0`, using `hY0` to
identify `P₁.X 0` with `D₁.master`. `inter_mem` mirrors `toD1Code`'s corrected version exactly, with
the roles of `P₀`/`P₁` swapped: given `hyi : y.mem (P₁.X i)`/`hyj : y.mem (P₁.X j)`, `y.inter_mem`/
`y.sub` shows `P₁.X i ∩ P₁.X j` is already `D₁`-genuine, so `P₁.surj` names it as some `P₁.X m`
outright, `P₁.inter_spec` reads this off as the closed-form index equation `P₁.X (P₁.inter i j) =
P₁.X i ∩ P₁.X j`, and `(d)(5)(b)(iv)`'s `YPseqCode_inter_eq_iff_Y_inter_eq` transports the same
equation across to `YPseqCode`, so `P₁.inter i j` is directly the witness index needed (**note the
iff's orientation is reversed relative to `X_inter_eq_iff_XPseqCode_inter_eq`**: `YPseqCode`-stuff is
on the *left*, so this uses `.mpr` with `hinterEq.symm`, not `.mp` with `hinterEq` as `toD1Code`
did). `up_mem` is exactly `(d)(5)(d)(iii)`'s `toD0Code_up_mem`. -/
def toD0Code (y : D₁.Element) : D₀.Element where
  mem S := ∃ n, S = P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) ∧
    y.mem (P₁.X n)
  sub := fun ⟨n, hn, _⟩ =>
    hn ▸ YPseqCode_mem_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
      hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 n
  master_mem := ⟨0, (YPseqCode_zero P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hX0 hY0).symm,
    by rw [hY0]; exact y.master_mem⟩
  inter_mem := by
    rintro S1 S2 ⟨i, rfl, hyi⟩ ⟨j, rfl, hyj⟩
    have hDmem : D₁.mem (P₁.X i ∩ P₁.X j) := y.sub (y.inter_mem hyi hyj)
    obtain ⟨m, hm⟩ := P₁.surj hDmem
    have hcons : ∃ k, P₁.X k ⊆ P₁.X i ∩ P₁.X j := ⟨m, hm.le⟩
    have hinterEq : P₁.X (P₁.inter i j) = P₁.X i ∩ P₁.X j := P₁.inter_spec hcons
    refine ⟨P₁.inter i j, ?_, ?_⟩
    · exact (YPseqCode_inter_eq_iff_Y_inter_eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
        hUnion1 i j (P₁.inter i j)).mpr hinterEq.symm
    · rw [hinterEq]; exact y.inter_mem hyi hyj
  up_mem := toD0Code_up_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
    hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 y

end ToD0Code

section XEqIffXPseqCodeEq

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
/-- **Exercise 8.12(d)(5)(e)(i).** The same-family `embed_eq_iff` companion, generalizing
`Exercise812c.lean`'s `X_eq_iff_XPseq_eq` to the code level: `P₀.X i = P₀.X j ↔ P₁.X (XPseqCode
… i) = P₁.X (XPseqCode … j)`, needed by `(e)(iv)`'s `domainIsoCode812d.map_rel_iff'`. Pure
packaging, no new mathematical content: each direction is `Set.Subset.antisymm` of
`(d)(5)(b)(iv)`'s `X_subset_iff_XPseqCode_subset` applied at `(i, j)` and `(j, i)`, exactly
mirroring `X_eq_iff_XPseq_eq`'s proof line-for-line. -/
theorem X_eq_iff_XPseqCode_eq (i j : ℕ) :
    P₀.X i = P₀.X j ↔
      P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i) =
        P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j) := by
  constructor
  · intro h
    exact Set.Subset.antisymm
      ((X_subset_iff_XPseqCode_subset P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 i
        j).mp h.subset)
      ((X_subset_iff_XPseqCode_subset P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 j
        i).mp h.symm.subset)
  · intro h
    exact Set.Subset.antisymm
      ((X_subset_iff_XPseqCode_subset P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 i
        j).mpr h.subset)
      ((X_subset_iff_XPseqCode_subset P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 j
        i).mpr h.symm.subset)

end XEqIffXPseqCodeEq

section ToD0CodeToD1Code

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in
/-- **Exercise 8.12(d)(5)(e)(ii).** The `left_inv` content feeding `domainIsoCode812d`:
`toD0Code (toD1Code x) = x`. Via `Element.ext`, unfolds to `∀ S, (∃ m n, S = P₀.X (YPseqCode …
m) ∧ P₁.X m = P₁.X (XPseqCode … n) ∧ x.mem (P₀.X n)) ↔ x.mem S`. Forward (`mp`): given the witness
`⟨m, hS, n, hmn, hxn⟩`, `(d)(5)(c)(iii)`'s `XPseqCode_eq_Y_iff_X_eq_YPseqCode n m` transports
`hmn.symm` into `hXeq : P₀.X n = P₀.X (YPseqCode … m)`; `rw [hS, ← hXeq]` reduces the goal `x.mem
S` to `x.mem (P₀.X n)`, closed by `hxn`. Backward (`mpr`): given `hxS : x.mem S`, `x.sub`/`P₀.surj`
names `S` as some `P₀.X n` outright (`subst`); take `m := XPseqCode … n` (handed over for free, no
search — `P₁.X m = P₁.X (XPseqCode … n)` is `rfl`); the closing equation `P₀.X n = P₀.X (YPseqCode
… m)` is `XPseqCode_eq_Y_iff_X_eq_YPseqCode n (XPseqCode … n) |>.mp rfl` applied at the
self-referential pair `(n, XPseqCode … n)`, exactly `toD1Code_up_mem`'s pattern — no
`hXcover`/`hYcover`-style double search needed, unlike `domainIso812c.left_inv`'s own proof. -/
theorem toD0Code_toD1Code (x : D₀.Element) :
    toD0Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit
      hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0
      (toD1Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit
        hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 x) = x := by
  apply Element.ext
  intro S
  constructor
  · rintro ⟨m, hS, n, hmn, hxn⟩
    have hXeq : P₀.X n =
        P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 m) :=
      (XPseqCode_eq_Y_iff_X_eq_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 n
        m).mp hmn.symm
    rw [hS, ← hXeq]
    exact hxn
  · intro hxS
    obtain ⟨n, hn⟩ := P₀.surj (x.sub hxS)
    subst hn
    exact ⟨XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n,
      (XPseqCode_eq_Y_iff_X_eq_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 n
        (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n)).mp rfl,
      n, rfl, hxS⟩

end ToD0CodeToD1Code

section ToD1CodeToD0Code

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in
/-- **Exercise 8.12(d)(5)(e)(iii).** The `right_inv` content feeding `domainIsoCode812d`:
`toD1Code (toD0Code y) = y`, the exact mirror of `(e)(ii)`'s `toD0Code_toD1Code` with `P₀`/`P₁`,
`XPseqCode`/`YPseqCode` swapped throughout. Via `Element.ext`, unfolds to `∀ T, (∃ m n, T = P₁.X
(XPseqCode … m) ∧ P₀.X m = P₀.X (YPseqCode … n) ∧ y.mem (P₁.X n)) ↔ y.mem T`. Forward (`mp`, given
`⟨m, hT, n, hmn, hyn⟩`): `(d)(5)(c)(iii)`'s `XPseqCode_eq_Y_iff_X_eq_YPseqCode m n` applied
directly to `hmn` (no `.symm` needed here, unlike `toD0Code_toD1Code`'s forward direction — `hmn`'s
orientation already matches the lemma's RHS) gives `hYeq : P₁.X (XPseqCode … m) = P₁.X n`; `rw [hT,
hYeq]; exact hyn` closes it. Backward (`intro hyT`): `y.sub`/`P₁.surj` names `T` as some `P₁.X n`
(`subst`); witness `m := YPseqCode … n` handed over for free (`P₀.X m = P₀.X (YPseqCode … n)` is
`rfl`); the closing equation `T = P₁.X (XPseqCode … m)` (post-`subst`, `P₁.X n = P₁.X (XPseqCode …
(YPseqCode … n))`) needs `XPseqCode_eq_Y_iff_X_eq_YPseqCode (YPseqCode … n) n |>.mpr rfl`, then
**`.symm`** (unlike `toD0Code_toD1Code`'s backward direction, whose analogous closing equation
needed no `.symm` — the orientation asymmetry mirrors `toD1Code_up_mem`/`toD0Code_up_mem`'s own
`.symm`/no-`.symm` split). -/
theorem toD1Code_toD0Code (y : D₁.Element) :
    toD1Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit
      hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      (toD0Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit
        hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0 y) = y := by
  apply Element.ext
  intro T
  constructor
  · rintro ⟨m, hT, n, hmn, hyn⟩
    have hYeq : P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 m) =
        P₁.X n :=
      (XPseqCode_eq_Y_iff_X_eq_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 m
        n).mpr hmn
    rw [hT, hYeq]
    exact hyn
  · intro hyT
    obtain ⟨n, hn⟩ := P₁.surj (y.sub hyT)
    subst hn
    exact ⟨YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n,
      ((XPseqCode_eq_Y_iff_X_eq_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
        (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) n).mpr rfl).symm,
      n, rfl, hyT⟩

end ToD1CodeToD0Code

section DomainIsoCode812d

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in
/-- **Exercise 8.12(d)(5)(e)(iv), final assembly.** The order isomorphism `D₀.Element ≃o
D₁.Element`, generalizing `Exercise812c.lean`'s `domainIso812c` ((c)(vii)(6)) to the code level.
`toFun`/`invFun`/`left_inv`/`right_inv` are direct citations of `(d)(5)(d)`'s `toD1Code`/`toD0Code`
and `(e)(ii)`/`(e)(iii)`'s `toD0Code_toD1Code`/`toD1Code_toD0Code`. `map_rel_iff'` is a direct
transcription of `domainIso812c.map_rel_iff'` (lines 2094–2108), substituting the code-level
apparatus throughout: the easy `mpr` direction (`x ≤ x2 → toD1Code x ≤ toD1Code x2`) is pure
unfolding, no search; the harder `mp` direction (`toD1Code x ≤ toD1Code x2 → x ≤ x2`) needs only
*one* `P₀.surj` call (replacing `hXcover`, `subst`-ing the target `S` as some `P₀.X n` directly)
plus `(e)(i)`'s `X_eq_iff_XPseqCode_eq` to transport the resulting `XPseqCode`-index equality back
to `P₀.X`-coordinates — confirming the same "no covering search" simplification found throughout
`(d)(5)`. -/
noncomputable def domainIsoCode812d : DomainIso D₀ D₁ where
  toFun := toD1Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin
    hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
  invFun := toD0Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin
    hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0
  left_inv := toD0Code_toD1Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
    hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0
  right_inv := toD1Code_toD0Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
    hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0
  map_rel_iff' := by
    intro x x2
    constructor
    · intro hle S hxS
      obtain ⟨n, hn⟩ := P₀.surj (x.sub hxS)
      subst hn
      obtain ⟨k, hk, hx2k⟩ := hle _
        (⟨n, rfl, hxS⟩ : (toD1Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
          hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
          hX0 x).mem
          (P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n)))
      rw [(X_eq_iff_XPseqCode_eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
        hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 n k).mpr hk]
      exact hx2k
    · intro hle T hT
      obtain ⟨n, hn, hxn⟩ := hT
      exact ⟨n, hn, hle _ hxn⟩

include hDiff0 hDiff1 hSplitX hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin
  hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0 in
/-- **Exercise 8.12(d)(5)(e)(iv), headline.** `D₀ ≅ᴰ D₁`, generalizing `isomorphic_812c` to the
code level; completes `8.12(d)(5)(e)` in full. -/
theorem isomorphic_812d : D₀ ≅ᴰ D₁ :=
  ⟨domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin
    hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0⟩

end DomainIsoCode812d

section ToD1CodeRelIff

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in
/-- **Exercise 8.12(d)(5)(f)(i).** `(ofIso domainIsoCode812d).rel` at raw indices reduces to a
single reindexed inclusion, exactly mirroring `Theorem88n.lean`'s `isoInj_rel_iff_incl`:
`ofIso`'s relation is `∃ _ : D₀.mem X, (e (D₀.principal ‹_›)).mem Y`; since `domainIsoCode812d`'s
`toFun` is literally `toD1Code …`, `(e (D₀.principal (P₀.mem_X n))).mem T` unfolds (via `toD1Code`'s
`mem` field and `mem_principal`) to `∃ k, T = P₁.X (XPseqCode … k) ∧ D₀.mem (P₀.X k) ∧ P₀.X n ⊆
P₀.X k`, and `D₀.mem (P₀.X k)` is always true (`P₀.mem_X k`), so it drops. -/
theorem toD1Code_rel_iff (n m : ℕ) :
    (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)).rel
      (P₀.X n) (P₁.X m) ↔
    ∃ k, P₁.X m = P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k) ∧
      P₀.X n ⊆ P₀.X k := by
  show (∃ _ : D₀.mem (P₀.X n),
      (toD1Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit
        hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
        (D₀.principal (P₀.mem_X n))).mem (P₁.X m)) ↔ _
  simp only [toD1Code, mem_principal]
  constructor
  · rintro ⟨-, k, hk, -, hsub⟩
    exact ⟨k, hk, hsub⟩
  · rintro ⟨k, hk, hsub⟩
    exact ⟨P₀.mem_X n, k, hk, P₀.mem_X k, hsub⟩

end ToD1CodeRelIff

section DomainIsoCode812dIsComputableMap

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in
/-- **Exercise 8.12(d)(5)(f)(ii).** `ofIso domainIsoCode812d` is computable relative to `P₀`/`P₁`:
via `(f)(i)`'s `toD1Code_rel_iff`, `IsComputableMap P₀ P₁ (ofIso domainIsoCode812d)` reduces to
`REPred₂ (fun n m => ∃ k, P₁.X m = P₁.X (XPseqCode … k) ∧ P₀.X n ⊆ P₀.X k)`. Unlike
`Theorem88n.lean`'s `isoInj_isComputableMap` (whose `eIdx` supplies a *unique* witness, no genuine
existential), the `∃ k` here is unbounded, so this mirrors `Definition72.lean`'s
`comp_isComputable`/`apply_isComputableElement` existential-closure recipe instead: the two
conjuncts are separately `RecDecidable` (`P₁.eq_computable` reindexed along the primitive-recursive
`XPseqCode` in the first coordinate; `P₀.incl_computable` reindexed directly), conjoined
(`RecDecidable.and`), lifted to `REPred` (`.re`), and closed by `REPred.proj` over the outer `∃ k`. -/
theorem domainIsoCode812d_isComputableMap :
    IsComputableMap P₀ P₁ (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
      hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
      hUnion1 hX0 hY0)) := by
  have hg : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.2.unpair.2
      (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 w.unpair.1)) :=
    Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right)
      ((primrec_XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1).comp
        Nat.Primrec.left)
  have hh : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.2.unpair.1 w.unpair.1) :=
    Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.right) Nat.Primrec.left
  have hA : RecDecidable (fun w : ℕ => P₁.X w.unpair.2.unpair.2 =
      P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 w.unpair.1)) := by
    refine RecDecidable.of_iff (fun w => ?_) (P₁.eq_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hB : RecDecidable (fun w : ℕ => P₀.X w.unpair.2.unpair.1 ⊆ P₀.X w.unpair.1) := by
    refine RecDecidable.of_iff (fun w => ?_) (P₀.incl_computable.comp hh)
    simp only [unpair_pair_fst, unpair_pair_snd]
  refine REPred.of_iff (fun t => ?_) (hA.and hB).re.proj
  show (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)).rel
      (P₀.X t.unpair.1) (P₁.X t.unpair.2) ↔ _
  rw [toD1Code_rel_iff]
  constructor
  · rintro ⟨k, hk, hsub⟩
    exact ⟨k, by simp only [unpair_pair_fst, unpair_pair_snd]; exact ⟨hk, hsub⟩⟩
  · rintro ⟨k, hk⟩
    simp only [unpair_pair_fst, unpair_pair_snd] at hk
    exact ⟨k, hk.1, hk.2⟩

end DomainIsoCode812dIsComputableMap

section ToD0CodeRelIff

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in
/-- **Exercise 8.12(d)(5)(f)(iii).** `(ofIso domainIsoCode812d.symm).rel` at raw indices reduces to
a single reindexed inclusion, the exact mirror of `(f)(i)`'s `toD1Code_rel_iff` (`P₀`/`P₁`,
`D₀`/`D₁`, `toD1Code`/`toD0Code`, `XPseqCode`/`YPseqCode` swapped throughout): since
`domainIsoCode812d.symm.toFun = domainIsoCode812d.invFun = toD0Code …`, the same `ofIso`/
`mem_principal` unfolding applies verbatim, mirroring `Theorem88n.lean`'s `isoProj_rel_iff_incl`. -/
theorem toD0Code_rel_iff (m n : ℕ) :
    (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0).symm).rel (P₁.X m) (P₀.X n) ↔
    ∃ k, P₀.X n = P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k) ∧
      P₁.X m ⊆ P₁.X k := by
  show (∃ _ : D₁.mem (P₁.X m),
      (toD0Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit
        hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0
        (D₁.principal (P₁.mem_X m))).mem (P₀.X n)) ↔ _
  simp only [toD0Code, mem_principal]
  constructor
  · rintro ⟨-, k, hk, -, hsub⟩
    exact ⟨k, hk, hsub⟩
  · rintro ⟨k, hk, hsub⟩
    exact ⟨P₁.mem_X m, k, hk, P₁.mem_X k, hsub⟩

end ToD0CodeRelIff

section DomainIsoCode812dSymmIsComputableMap

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in
/-- **Exercise 8.12(d)(5)(f)(iv), the last of the four `(f)` sub-parts.** `ofIso
domainIsoCode812d.symm` is computable relative to `P₁`/`P₀`, the exact mirror of `(f)(ii)`'s
`domainIsoCode812d_isComputableMap` via `(f)(iii)`'s `toD0Code_rel_iff`, swapping `P₀`↔`P₁` and
`XPseqCode`↔`YPseqCode`/`primrec_YPseqCode` throughout: `P₀.eq_computable` reindexed along the
primitive-recursive `YPseqCode` supplies the equality conjunct, `P₁.incl_computable` reindexed
directly supplies the inclusion conjunct, `RecDecidable.and`/`.re`/`REPred.proj` close the outer
`∃ k`, and `REPred.of_iff` matches the exact `IsComputableMap P₁ P₀` shape via `toD0Code_rel_iff`.
Completes `8.12(d)(5)(f)` — hence `8.12(d)(5)` — in full. -/
theorem domainIsoCode812d_symm_isComputableMap :
    IsComputableMap P₁ P₀ (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
      hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
      hUnion1 hX0 hY0).symm) := by
  have hg : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.2.unpair.2
      (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 w.unpair.1)) :=
    Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right)
      ((primrec_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0).comp
        Nat.Primrec.left)
  have hh : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.2.unpair.1 w.unpair.1) :=
    Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.right) Nat.Primrec.left
  have hA : RecDecidable (fun w : ℕ => P₀.X w.unpair.2.unpair.2 =
      P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 w.unpair.1)) := by
    refine RecDecidable.of_iff (fun w => ?_) (P₀.eq_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hB : RecDecidable (fun w : ℕ => P₁.X w.unpair.2.unpair.1 ⊆ P₁.X w.unpair.1) := by
    refine RecDecidable.of_iff (fun w => ?_) (P₁.incl_computable.comp hh)
    simp only [unpair_pair_fst, unpair_pair_snd]
  refine REPred.of_iff (fun t => ?_) (hA.and hB).re.proj
  show (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0).symm).rel (P₁.X t.unpair.1) (P₀.X t.unpair.2) ↔ _
  rw [toD0Code_rel_iff]
  constructor
  · rintro ⟨k, hk, hsub⟩
    exact ⟨k, by simp only [unpair_pair_fst, unpair_pair_snd]; exact ⟨hk, hsub⟩⟩
  · rintro ⟨k, hk⟩
    simp only [unpair_pair_fst, unpair_pair_snd] at hk
    exact ⟨k, hk.1, hk.2⟩

end DomainIsoCode812dSymmIsComputableMap

section InvMapComp812d

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in
/-- **Exercise 8.12(d)(6)(a).** The `left_inv` content for `EffectiveIso P₀ P₁`: `ofIso
domainIsoCode812d.symm` is a left inverse of `ofIso domainIsoCode812d`, at the `ApproximableMap`
level. Direct transcription of `Theorem88n.lean`'s `isoProj_comp_isoInj` for the arbitrary
`OrderIso` `e := domainIsoCode812d …` (no case split, no search, needs nothing about
`domainIsoCode812d` beyond its bare `OrderIso` structure): `ext_of_toElementMap` reduces map
equality to a pointwise `Element` equality, `toElementMap_comp` unfolds the composite,
`toElementMap_ofIso` identifies each side with plain `OrderIso` application, and
`OrderIso.symm_apply_apply` closes it. -/
theorem invMap_comp_toMap :
    (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0).symm).comp
    (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)) =
    idMap D₀ := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp]
  show (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0).symm).toElementMap
    ((ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0)).toElementMap x) = _
  rw [toElementMap_ofIso, toElementMap_ofIso, OrderIso.symm_apply_apply, toElementMap_idMap]

end InvMapComp812d

section ToMapComp812d

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in
/-- **Exercise 8.12(d)(6)(b).** The `right_inv` content for `EffectiveIso P₀ P₁`: `ofIso
domainIsoCode812d` is a left inverse of `ofIso domainIsoCode812d.symm`, at the `ApproximableMap`
level — the exact mirror of `(a)`'s `invMap_comp_toMap`, independent of it. Direct transcription
of `Theorem88n.lean`'s `isoInj_comp_isoProj` for `e := domainIsoCode812d …`: same shape as `(a)`
with `e`/`e.symm` swapped and `OrderIso.apply_symm_apply` in place of
`OrderIso.symm_apply_apply`. -/
theorem toMap_comp_invMap :
    (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)).comp
    (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0).symm) =
    idMap D₁ := by
  apply ext_of_toElementMap
  intro y
  rw [toElementMap_comp]
  show (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0)).toElementMap
    ((ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0).symm).toElementMap y) = _
  rw [toElementMap_ofIso, toElementMap_ofIso, OrderIso.apply_symm_apply, toElementMap_idMap]

end ToMapComp812d

section EffectiveIso812d

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in
/-- **Exercise 8.12(d)(6)(c), final assembly.** The effective isomorphism `P₀ ≅ᵉ P₁` (in the sense
of `Exercise718.lean`'s `EffectiveIso`), completing `8.12(d)(6)` — hence `8.12(d)` as a whole.
Every field is a direct citation: `toMap`/`invMap` from `(d)(5)(e)(iv)`'s `domainIsoCode812d`
(via `ofIso`/`.symm`), `toMap_computable`/`invMap_computable` from `(d)(5)(f)`'s
`domainIsoCode812d_isComputableMap`/`domainIsoCode812d_symm_isComputableMap`, and
`left_inv`/`right_inv` from `(a)`/`(b)`'s `invMap_comp_toMap`/`toMap_comp_invMap` — exactly
mirroring `(d)(5)(e)(iv)`'s `domainIsoCode812d` assembly pattern, and `Exercise718.lean`'s own
`iterIterEffectiveIso`. -/
noncomputable def effectiveIso812d : EffectiveIso P₀ P₁ where
  toMap := ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)
  invMap := ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
    hY0).symm
  toMap_computable := domainIsoCode812d_isComputableMap P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
    hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
    hUnion1 hX0 hY0
  invMap_computable := domainIsoCode812d_symm_isComputableMap P₀ P₁ hDiff0 hDiff1 splitX hSplitX
    splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
    hUnion0 hUnion1 hX0 hY0
  left_inv := invMap_comp_toMap P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
    hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0
  right_inv := toMap_comp_invMap P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
    hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0

include hDiff0 hDiff1 hSplitX hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin
  hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0 in
/-- **Exercise 8.12(d)(6)(c), headline.** `P₀`/`P₁` are effectively isomorphic; completes
`8.12(d)(6)` — hence `8.12(d)` in full. -/
theorem effectivelyIsomorphic_812d : EffectivelyIsomorphic P₀ P₁ :=
  ⟨effectiveIso812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin
    hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0⟩

end EffectiveIso812d

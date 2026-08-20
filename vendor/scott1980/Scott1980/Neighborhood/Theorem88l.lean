/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Theorem88k

/-!
# Theorem 8.8(c), Part 5 of 6 — a primitive-recursive `.inter` for `D_X`, and its `inter_spec`

Following Theorem 8.8(c)'s 6-part plan (`arxiv.md`): Parts 1–4 built the enumeration `D_X qChar
cons c := P.X (myFoldCode qChar cons c)`, showed it is onto `fixedNbhd a`, and showed its
`interEq`/`cons` relations are recursively decidable. This file supplies the last data field
`ComputablePresentation` needs: a primitive-recursive `D_inter : ℕ → ℕ → ℕ` with `D_X (D_inter c₁
c₂) = D_X c₁ ∩ D_X c₂` whenever the two are `D`-consistent.

## The construction: `D_inter c₁ c₂ := appendListCode c₁ c₂`

Concatenating the two list-codes (`Recursive.lean`'s Exercise 7.22 `appendListCode`/
`primrec_appendListCode`/`appendListCode_eq`, reused outright) is exactly right because
`myFoldCode` is a *left* fold from `P.masterIdx`, so folding the concatenated list decomposes
(`List.foldl_append`) as folding `c₂`'s list *starting from* `myFoldCode c₁` instead of from
`P.masterIdx`:

```
myFoldCode (appendListCode c₁ c₂) = (decodeList c₂).foldl myStep (myFoldCode c₁)
```

## The one genuine lemma: refolding from a smaller start intersects

`myFoldl_inter_of_le` is the mathematical content: for a list `l`, refolding it from a
`DiagFixed`-irrelevant starting point `n ⊆ r` (in `P.X`) reproduces `P.X n ∩ P.X (fold from r)`,
**provided** the two are already known `V`-consistent at the *end* of the fold. The key subtlety
is that `myStep`'s gate (`cons (Nat.pair r e.unpair.2) = 1`) is *accumulator-dependent*, so
refolding the same list from a smaller start could in principle skip steps the original fold took.
The induction shows this never happens: any step that *succeeds* from `r` also succeeds from `n`,
because the global witness (consistency of `n` with the *final* fold value) is inherited by every
intermediate accumulator via the fold's monotone-shrinking property (`myFoldl_subset`); and any
step that *fails* from `r` also fails from `n`, since success from the (⊆-smaller) `n` would imply
success from `r` too (monotonicity of `cons`'s witness in the ⊆ direction).

Given this, Part 5's `D_X_inter_spec` is immediate: unfold both sides via `appendListCode_eq`/
`List.foldl_append`, apply `myFoldl_inter_of_le` with `n := myFoldCode c₁`, `r := P.masterIdx`
(using `V.sub_master` for `n ⊆ r`), and the hypothesis (already `V`-side, since `D_X`'s codomain
*is* `P.X` of some raw index — no reindexing needed, unlike Part 4's `cons_iff`).

Everything here is **choice-free** (`⊆ {propext, Quot.sound}`): `Recursive.lean`'s
`list_eq_of_getD`/`appendListTabFn_eq`/`primrec_appendListTabFn`/`primrec_appendListCode` were
tightened in this session (dropping a stray `by_contra`/lemma-set `simp` that pulled in
`Classical.choice`) to be choice-free outright, so no new taint is introduced here.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)

variable {P qChar cons}

/-! ### The one genuine lemma: refolding from a smaller, globally-consistent start -/

/-- **One step of `myStep` only shrinks the presented set.** -/
theorem myStep_subset
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (r e : ℕ) :
    P.X (myStep P qChar cons r e) ⊆ P.X r := by
  unfold myStep
  rcases Nat.decEq (qChar e) 1 with hq | hq
  · rw [isOne_of_ne_one hq, Nat.zero_mul, selectFn_zero]
  · rw [(isOne_eq_one_iff _).mpr hq, Nat.one_mul]
    rcases Nat.decEq (cons (Nat.pair r e.unpair.2)) 1 with hc | hc
    · rw [isOne_of_ne_one hc, selectFn_zero]
    · rw [(isOne_eq_one_iff _).mpr hc, selectFn_one, P.inter_spec ((hcons r e.unpair.2).mp hc)]
      exact Set.inter_subset_left

/-- **Folding only ever shrinks the presented set.** -/
theorem myFoldl_subset
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) :
    ∀ (l : List ℕ) (r : ℕ), P.X (l.foldl (myStep P qChar cons) r) ⊆ P.X r := by
  intro l
  induction l with
  | nil => intro r; simp only [List.foldl_nil]; exact subset_rfl
  | cons e rest ih =>
    intro r
    rw [List.foldl_cons]
    exact (ih (myStep P qChar cons r e)).trans (myStep_subset hcons r e)

/-- **The key lemma.** Refolding a list `l` from a start `n` that is `⊆` (in `P.X`) another start
`r`, reproduces `P.X n ∩ P.X (fold of l from r)` — *provided* this is already known to be
`V`-consistent at the end (i.e. `∃ k, P.X k ⊆ P.X n ∩ P.X (l.foldl … r)`). No `a`/`DiagFixed`
apparatus is needed: this is a purely structural fact about `myStep`'s consistency gate. -/
theorem myFoldl_inter_of_le
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) :
    ∀ (l : List ℕ) {n r : ℕ}, P.X n ⊆ P.X r →
      (∃ k, P.X k ⊆ P.X n ∩ P.X (l.foldl (myStep P qChar cons) r)) →
      P.X (l.foldl (myStep P qChar cons) n) = P.X n ∩ P.X (l.foldl (myStep P qChar cons) r) := by
  intro l
  induction l with
  | nil =>
    intro n r hnr _
    simp only [List.foldl_nil]
    exact (Set.inter_eq_left.mpr hnr).symm
  | cons e rest ih =>
    intro n r hnr hk
    simp only [List.foldl_cons] at hk ⊢
    rcases Nat.decEq (qChar e) 1 with hq | hq
    · have hstepR : myStep P qChar cons r e = r := by
        unfold myStep; rw [isOne_of_ne_one hq, Nat.zero_mul, selectFn_zero]
      have hstepN : myStep P qChar cons n e = n := by
        unfold myStep; rw [isOne_of_ne_one hq, Nat.zero_mul, selectFn_zero]
      rw [hstepR] at hk ⊢
      rw [hstepN]
      exact ih hnr hk
    · rcases Nat.decEq (cons (Nat.pair r e.unpair.2)) 1 with hc | hc
      · have hstepR : myStep P qChar cons r e = r := by
          unfold myStep
          rw [(isOne_eq_one_iff _).mpr hq, Nat.one_mul, isOne_of_ne_one hc, selectFn_zero]
        have hcN : cons (Nat.pair n e.unpair.2) ≠ 1 := by
          intro hcn
          obtain ⟨w, hw⟩ := (hcons n e.unpair.2).mp hcn
          exact hc ((hcons r e.unpair.2).mpr
            ⟨w, hw.trans (Set.inter_subset_inter_left _ hnr)⟩)
        have hstepN : myStep P qChar cons n e = n := by
          unfold myStep
          rw [(isOne_eq_one_iff _).mpr hq, Nat.one_mul, isOne_of_ne_one hcN, selectFn_zero]
        rw [hstepR] at hk ⊢
        rw [hstepN]
        exact ih hnr hk
      · obtain ⟨w0, hw0⟩ := (hcons r e.unpair.2).mp hc
        have hstepR : myStep P qChar cons r e = P.inter r e.unpair.2 := by
          unfold myStep
          rw [(isOne_eq_one_iff _).mpr hq, Nat.one_mul, (isOne_eq_one_iff _).mpr hc, selectFn_one]
        rw [hstepR] at hk ⊢
        obtain ⟨k, hkk⟩ := hk
        have hYsub : P.X (rest.foldl (myStep P qChar cons) (P.inter r e.unpair.2))
            ⊆ P.X e.unpair.2 := by
          refine (myFoldl_subset hcons rest (P.inter r e.unpair.2)).trans ?_
          rw [P.inter_spec ⟨w0, hw0⟩]
          exact Set.inter_subset_right
        have hkR : P.X k ⊆ P.X n := hkk.trans Set.inter_subset_left
        have hkY : P.X k ⊆ P.X (rest.foldl (myStep P qChar cons) (P.inter r e.unpair.2)) :=
          hkk.trans Set.inter_subset_right
        have hkne : P.X k ⊆ P.X e.unpair.2 := hkY.trans hYsub
        have hwitN : ∃ k, P.X k ⊆ P.X n ∩ P.X e.unpair.2 := ⟨k, Set.subset_inter hkR hkne⟩
        have hcN : cons (Nat.pair n e.unpair.2) = 1 := (hcons n e.unpair.2).mpr hwitN
        have hstepN : myStep P qChar cons n e = P.inter n e.unpair.2 := by
          unfold myStep
          rw [(isOne_eq_one_iff _).mpr hq, Nat.one_mul, (isOne_eq_one_iff _).mpr hcN, selectFn_one]
        rw [hstepN]
        have hnr' : P.X (P.inter n e.unpair.2) ⊆ P.X (P.inter r e.unpair.2) := by
          rw [P.inter_spec hwitN, P.inter_spec ⟨w0, hw0⟩]
          exact Set.inter_subset_inter_left _ hnr
        have hk' : ∃ k', P.X k' ⊆ P.X (P.inter n e.unpair.2) ∩
            P.X (rest.foldl (myStep P qChar cons) (P.inter r e.unpair.2)) := by
          refine ⟨k, ?_⟩
          rw [P.inter_spec hwitN]
          exact Set.subset_inter (Set.subset_inter hkR hkne) hkY
        rw [ih hnr' hk', P.inter_spec hwitN, Set.inter_assoc, Set.inter_eq_right.mpr hYsub]

/-! ### `D_inter`, its primitive-recursiveness, and `inter_spec` -/

/-- **The `.inter` field for `D_X`**: concatenate the two list-codes (`Recursive.lean`'s
Exercise 7.22 `appendListCode`), reusing that this is exactly `myFoldCode`'s left-fold-from-
`P.masterIdx` restarted at `myFoldCode c₁` (via `List.foldl_append`). -/
def D_inter (c₁ c₂ : ℕ) : ℕ := appendListCode c₁ c₂

variable (P qChar cons)

theorem D_inter_primrec : Nat.Primrec (fun t => D_inter t.unpair.1 t.unpair.2) :=
  primrec_appendListCode

variable {P qChar cons}

theorem D_X_inter_eq (c₁ c₂ : ℕ) :
    D_X P qChar cons (D_inter c₁ c₂) =
      P.X ((decodeList c₂).foldl (myStep P qChar cons) (myFoldCode P qChar cons c₁)) := by
  have h1 : D_X P qChar cons (D_inter c₁ c₂) =
      P.X ((decodeList c₁ ++ decodeList c₂).foldl (myStep P qChar cons) P.masterIdx) := by
    show P.X (myFoldCode P qChar cons (appendListCode c₁ c₂)) = _
    rw [myFoldCode_eq, appendListCode_eq]
    rfl
  have heq1 : (decodeList c₁).foldl (myStep P qChar cons) P.masterIdx =
      myFoldCode P qChar cons c₁ := (myFoldCode_eq P qChar cons c₁).symm
  rw [h1, List.foldl_append, heq1]

/-- **Theorem 8.8(c), Part 5 of 6, headline.** Given `D`-consistency of `c₁`, `c₂`,
`D_X (D_inter c₁ c₂) = D_X c₁ ∩ D_X c₂`. The hypothesis is already stated at the `V`-side (`D_X`'s
codomain *is* `P.X` of a raw index), so `myFoldl_inter_of_le` applies directly with `n :=
myFoldCode c₁`, `r := P.masterIdx`. -/
theorem D_X_inter_spec
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) {c₁ c₂ : ℕ}
    (h : ∃ k, D_X P qChar cons k ⊆ D_X P qChar cons c₁ ∩ D_X P qChar cons c₂) :
    D_X P qChar cons (D_inter c₁ c₂) = D_X P qChar cons c₁ ∩ D_X P qChar cons c₂ := by
  have heq2 : D_X P qChar cons c₂ =
      P.X ((decodeList c₂).foldl (myStep P qChar cons) P.masterIdx) := by
    show P.X (myFoldCode P qChar cons c₂) = _
    rw [myFoldCode_eq]
    rfl
  have hnr : P.X (myFoldCode P qChar cons c₁) ⊆ P.X P.masterIdx := by
    rw [P.masterIdx_spec]
    exact V.sub_master (P.mem_X _)
  have hk : ∃ k, P.X k ⊆ P.X (myFoldCode P qChar cons c₁) ∩
      P.X ((decodeList c₂).foldl (myStep P qChar cons) P.masterIdx) := by
    obtain ⟨k, hk0⟩ := h
    refine ⟨myFoldCode P qChar cons k, ?_⟩
    rw [← heq2]
    exact hk0
  rw [D_X_inter_eq, myFoldl_inter_of_le hcons (decodeList c₂) hnr hk, ← heq2]
  rfl

end Scott1980.Neighborhood

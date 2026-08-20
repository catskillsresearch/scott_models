/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Exercise812e
import Scott1980.Neighborhood.SplitV
import Scott1980.Neighborhood.UComputablePresentation

/-!
# Exercise 8.12(e)(d)(iii) (Scott 1981, PRG-19, Lecture VIII) — package as `ComputableBisection`;
instantiate for `U` ↔ `V`

The exercise's literal target, given `(e)(d)(i)`–`(ii)`: a concrete `splitX812e : Set ℚ → Set ℕ →
Set ℚ → Set ℕ × Set ℕ` satisfying `IsComputableSplit UComputablePresentation
VComputablePresentation splitX812e`.

## A gap found while assembling this (not present in the earlier scoping): `U`'s missing
`IsComputableDiff` witness

`(e)(d)`'s own `arxiv.md` draft signature — `splitFromBisection UComputablePresentation (U's
`IsComputableDiff`) B812e` — assumed an `IsComputableDiff UComputablePresentation` instance already
existed somewhere in the codebase. It does not: grep-confirmed, `IsComputableDiff` (`Exercise812d.lean`,
`(d)(3)(a)`) has never been instantiated for either `U` or `V`. Building it is, however, genuinely
mechanical — not a new mathematical gap like `(e)(d)(i)`/`(ii)`'s — since `IntervalPrimrec.lean`
already supplies **every** raw piece unconditionally: `diffCode`/`primrec_diffCode` (the code-level
set-difference primitive) and `presentedIntervals_decodeQPairList_diffCode` (its correctness,
unconditional — no case split on emptiness needed, unlike `combineCode`'s consistency side of the
story). `Udiff`/`Udiff_primrec`/`Udiff_spec`/`U_diff_computable` below are a direct structural mirror
of `UComputablePresentation.lean`'s own `Uinter`/`Uinter_primrec`/`Uinter_spec`/`U_cons_computable`,
substituting `diffCode` for `combineCode` and `U_diff_mem` (`Exercise812c.lean`, already `Pass`) for
`U`'s `IsPositive` as the "always mem-or-∅" fact driving the decidability reduction.
-/

namespace Scott1980.Neighborhood

open Domain.Recursive NeighborhoodSystem

/-! ## `U_isComputableDiff` -/

/-- The difference index: `diffCode` on canonicalized codes (`UX` re-canonicalizes on lookup, so no
further canonicalization is needed here — mirrors `Uinter`). -/
def Udiff (n m : ℕ) : ℕ := diffCode (canonCode n) (canonCode m)

theorem Udiff_primrec : Nat.Primrec (fun t : ℕ => Udiff t.unpair.1 t.unpair.2) := by
  unfold Udiff
  exact (primrec_diffCode.comp ((primrec_canonCode.comp Nat.Primrec.left).pair
    (primrec_canonCode.comp Nat.Primrec.right))).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]

/-- **`Udiff` realizes set difference at the raw (uncanonicalized) `presentedIntervals` level**,
unconditionally — the one respect in which `\` is *simpler* than `∩` here (no consistency case
split needed at this stage). -/
theorem Udiff_eq_diff (n m : ℕ) :
    presentedIntervals (decodeQPairList (Udiff n m)) = UX n \ UX m := by
  unfold Udiff
  exact presentedIntervals_decodeQPairList_diffCode (canonCode n) (canonCode m)

/-- **Scott's consistency condition for `\` reduces to non-emptiness**, exactly mirroring
`U_cons_iff_nonempty_inter`: `U_diff_mem` (`Exercise812c.lean`) shows `UX n \ UX m` is always either
empty or a genuine `U`-neighbourhood, and every `UX k` is non-empty (`U.mem` forces
`Set.Nonempty`), so "presentable" and "non-empty" coincide. -/
theorem U_diff_iff_nonempty (n m : ℕ) :
    (∃ k, UX k = UX n \ UX m) ↔ (UX n \ UX m).Nonempty := by
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk]; exact (U_mem_UX k).2.1
  · intro hne
    rcases U_diff_mem (U_mem_UX n) (U_mem_UX m) with hempty | hmem
    · exact absurd hempty hne.ne_empty
    · exact U_surj_UX hmem

/-- **`Udiff n m` genuinely indexes `UX n \ UX m` whenever that difference is a genuine
neighbourhood** — mirrors `Uinter_spec` exactly: the raw `diffCode` output is already a genuine
`U`-neighbourhood (by hypothesis via `Udiff_eq_diff`), so re-canonicalizing it (`canonCode`'s own
lookup, `UX`'s definition) is a no-op (`canonList_fixed`). -/
theorem Udiff_spec {n m : ℕ} (h : ∃ k, UX k = UX n \ UX m) : UX (Udiff n m) = UX n \ UX m := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (Udiff n m))) := by
    rw [Udiff_eq_diff]
    obtain ⟨k, hk⟩ := h
    rw [← hk]; exact U_mem_UX k
  show presentedIntervals (decodeQPairList (canonCode (Udiff n m))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL, Udiff_eq_diff]

/-- **7.1(i)-for-`\`, for `𝒰`**: `Xₙ \ Xₘ = X_k` for some `k` is recursively decidable — mirrors
`U_cons_computable` exactly, substituting `Udiff` for the raw `combineCode` composite. -/
theorem U_diff_computable : RecDecidable₂ (fun n m => ∃ k, UX k = UX n \ UX m) := by
  unfold RecDecidable₂
  refine RecDecidable.of_iff (fun t => ?_)
    (recDecidable_presentedIntervals_nonempty.comp Udiff_primrec)
  show (∃ k, UX k = UX t.unpair.1 \ UX t.unpair.2) ↔ _
  rw [U_diff_iff_nonempty, ← Udiff_eq_diff]

/-- **`U` has a computable `\`**, completing the missing prerequisite this section opened with. -/
def U_isComputableDiff : IsComputableDiff UComputablePresentation where
  diffIdx := Udiff
  diffIdx_primrec := Udiff_primrec
  diffIdx_spec := Udiff_spec
  diff_computable := U_diff_computable

/-! ## `B812e`, `splitX812e`, `isComputableSplit_812e` — the exercise's literal target

Mechanical given `(e)(d)(i)`–`(ii)` and `U_isComputableDiff` above: `B812e` is a direct
field-by-field assembly from `SplitV.lean`'s already-`Pass` declarations; `splitX812e`/
`isComputableSplit_812e` are one-line instantiations of `Exercise812e.lean`'s generic
`splitFromBisection`/`isComputableSplit_ofBisection`, fed `U`'s already-`Pass`
`IsPositive`/`NoMinimal`/`DiffClosed` facts (`Exercise812c.lean`). -/

/-- **`B812e`: `V`'s computable canonical bisection, packaged as a `ComputableBisection`.** -/
def B812e : ComputableBisection VComputablePresentation where
  left := splitVLeft
  right := splitVRight
  left_primrec := primrec_splitVLeft
  right_primrec := primrec_splitVRight
  disjoint := splitV_disjoint
  union := splitV_union
  left_congr := fun _ _ h => splitVLeft_congr h
  right_congr := fun _ _ h => splitVRight_congr h

/-- **`splitX812e`: the exercise's literal target split**, `U` as prober against `V`'s canonical
bisection. -/
noncomputable def splitX812e : Set ℚ → Set ℕ → Set ℚ → Set ℕ × Set ℕ :=
  ComputableBisection.splitFromBisection UComputablePresentation U_isComputableDiff B812e
    V_noMinimal

/-- **Exercise 8.12(e), completed in full**: `splitX812e` satisfies `IsComputableSplit`.
`noncomputable def`, not `theorem` — `IsComputableSplit` is a data-carrying structure (its
`posIdx`/`negIdx` fields are `ℕ`-valued functions), mirroring `isComputableSplit_ofBisection`
itself (`(e)(c)(ii)`). -/
noncomputable def isComputableSplit_812e :
    IsComputableSplit UComputablePresentation VComputablePresentation splitX812e :=
  ComputableBisection.isComputableSplit_ofBisection UComputablePresentation U_isComputableDiff
    B812e V_noMinimal U_isPositive U_noMinimal U_diffClosed

/-- **`8.12(g)(3)`, `U`-as-prober half**: `splitX812e` also satisfies `SplitSpec'` — completing the
concrete-construction half of `8.12(g)(3)` left open by `Exercise812e.lean`'s generic
`splitFromBisection_isSplitSpec'`. The extra hypothesis it needs, `∀ j, VX j ≠ ∅`, is immediate:
every `VX j` is `V.mem`-genuine (`VComputablePresentation.mem_X`) and `V.mem` structurally excludes
`∅` (`V.mem X := ∃ k m, X = levelSet k m ∧ X.Nonempty`, `Exercise812.lean` line 199). -/
theorem hxSplit812e : SplitSpec' V splitX812e :=
  ComputableBisection.splitFromBisection_isSplitSpec' UComputablePresentation U_isComputableDiff
    B812e V_noMinimal U_isPositive U_noMinimal U_diffClosed (fun j => (VX_nonempty j).ne_empty)

end Scott1980.Neighborhood

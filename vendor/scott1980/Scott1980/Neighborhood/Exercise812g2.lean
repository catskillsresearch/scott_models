/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Exercise812d
import Scott1980.Neighborhood.UComputablePresentation
import Scott1980.Neighborhood.LevelSetPrimrec

/-!
# Exercise 8.12(g)(2) — `IsComputableUnion` for `U` and `V`

`Exercise812d.lean`'s `(d)(4)(a)` defines `IsComputableUnion` (mirroring `IsComputableDiff`'s shape
for `∪` instead of `\`) but never instantiates it for either concrete system. Both instances turn
out **unconditional**: unlike `IsComputableDiff`'s `diffIdx_spec`, whose hypothesis is genuinely
needed (a difference can be empty), a union of two genuine, non-empty neighbourhoods is *always*
again a genuine neighbourhood for both `U` and `V` — so `unionIdx_spec`'s hypothesis, while still
accepted (to match the structure's shape), is never actually used, and `union_computable` reduces
to the trivial always-`1` decider.

* **`U`-side** (`Uunion`): mirrors `Exercise812eD.lean`'s `Udiff`, substituting the raw list-`++`
  primitive `appendListCode` (`Recursive.lean`) for `diffCode` — concatenation trivially witnesses
  `presentedIntervals`'s own closure under `∪` (`presentedIntervals_append`, `Definition87.lean`).
* **`V`-side** (`Vunion`): mirrors `LevelSetPrimrec.lean`'s `VinterRaw`/`Vinter`, substituting the
  bitwise-OR primitive `myLor` for `myLand` (`levelSet_myUnion`, the computable version of
  `Exercise812.lean`'s inlined union identity already used in `V_union_mem`).
-/

namespace Scott1980.Neighborhood

open Domain.Recursive NeighborhoodSystem

/-! ## `U_isComputableUnion` -/

/-- The union index: list-concatenate the two canonicalized presenting lists. `UX` re-canonicalizes
on lookup, so no further canonicalization of the inputs is needed here (mirrors `Udiff`). -/
def Uunion (n m : ℕ) : ℕ := appendListCode (canonCode n) (canonCode m)

theorem Uunion_primrec : Nat.Primrec (fun t : ℕ => Uunion t.unpair.1 t.unpair.2) := by
  unfold Uunion
  exact (primrec_appendListCode.comp ((primrec_canonCode.comp Nat.Primrec.left).pair
    (primrec_canonCode.comp Nat.Primrec.right))).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]

/-- `decodeQPairList` commutes with `appendListCode` (it is just `decodeList` followed by a fixed
`map`, and `List.map` commutes with `++`). -/
theorem decodeQPairList_appendListCode (c1 c2 : ℕ) :
    decodeQPairList (appendListCode c1 c2) = decodeQPairList c1 ++ decodeQPairList c2 := by
  unfold decodeQPairList
  rw [appendListCode_eq, List.map_append]

/-- **`Uunion` realizes set union at the raw (uncanonicalized) `presentedIntervals` level**,
unconditionally — concatenating presenting lists always presents the union, no consistency case
split needed (the one respect in which `∪` is even simpler than `\`'s `Udiff_eq_diff`). -/
theorem Uunion_eq_union (n m : ℕ) :
    presentedIntervals (decodeQPairList (Uunion n m)) = UX n ∪ UX m := by
  unfold Uunion
  rw [decodeQPairList_appendListCode, presentedIntervals_append]
  rfl

/-- **A union of two genuine `U`-neighbourhoods is again genuine, unconditionally** — no
`NoMinimal`/`DiffClosed` detour needed for `U` specifically: `U.mem`'s three conjuncts (presentable,
non-empty, `⊆ [0,1)`) each transfer directly across `∪` (presentability via list `++`; non-emptiness
since one side alone is already non-empty; the subset bound is monotone in `∪`). -/
theorem U_union_UX_mem (n m : ℕ) : U.mem (UX n ∪ UX m) := by
  obtain ⟨⟨L1, hL1⟩, hne1, hsub1⟩ := U_mem_UX n
  obtain ⟨⟨L2, hL2⟩, -, hsub2⟩ := U_mem_UX m
  exact ⟨⟨L1 ++ L2, by rw [presentedIntervals_append, hL1, hL2]⟩,
    hne1.mono Set.subset_union_left, Set.union_subset hsub1 hsub2⟩

/-- **`Uunion n m` genuinely indexes `UX n ∪ UX m`** — mirrors `Udiff_spec`'s shape exactly, but the
hypothesis is never used (the union is already unconditionally genuine, `U_union_mem`): the raw
`appendListCode` output is already a genuine `U`-neighbourhood, so re-canonicalizing it (`canonCode`'s
own lookup, `UX`'s definition) is a no-op (`canonList_fixed`). -/
theorem Uunion_spec {n m : ℕ} (_ : ∃ k, UX k = UX n ∪ UX m) : UX (Uunion n m) = UX n ∪ UX m := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (Uunion n m))) := by
    rw [Uunion_eq_union]; exact U_union_UX_mem n m
  show presentedIntervals (decodeQPairList (canonCode (Uunion n m))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL, Uunion_eq_union]

/-- **`Xₙ ∪ Xₘ` is always presentable as some `X_k`**, for `𝒰` — via `U_surj_UX` on
`U_union_UX_mem` (mirroring `U_diff_iff_nonempty`'s use of `U_surj_UX`, but unconditional). -/
theorem U_union_exists (n m : ℕ) : ∃ k, UX k = UX n ∪ UX m := U_surj_UX (U_union_UX_mem n m)

/-- **7.1(i)-for-`∪`, for `𝒰`**: trivially recursively decidable (the always-`1` constant), since
`U_union_exists` shows the underlying predicate is unconditionally `True`. -/
theorem U_union_computable : RecDecidable₂ (fun n m => ∃ k, UX k = UX n ∪ UX m) :=
  ⟨fun _ => 1, Nat.Primrec.const 1, fun t => iff_of_true (U_union_exists t.unpair.1 t.unpair.2) rfl⟩

/-- **`U` has a computable `∪`.** -/
def U_isComputableUnion : IsComputableUnion UComputablePresentation where
  unionIdx := Uunion
  unionIdx_primrec := Uunion_primrec
  unionIdx_spec := Uunion_spec
  union_computable := U_union_computable

/-! ## `V_isComputableUnion` -/

/-- **Computable version of `levelSet_union_same_level` at differing levels** — the bitwise-`OR`
analogue of `levelSet_myInter`, mirroring its proof verbatim with `myLor`/`Nat.testBit_or` in place
of `myLand`/`Nat.testBit_and`. -/
theorem levelSet_myUnion (k1 m1 k2 m2 : ℕ) :
    levelSet k1 m1 ∪ levelSet k2 m2
      = levelSet (max k1 k2) (myLor (myUpsample k1 (max k1 k2) m1) (myUpsample k2 (max k1 k2) m2)) := by
  conv_lhs => rw [← levelSet_myUpsample (Nat.le_max_left k1 k2) m1,
    ← levelSet_myUpsample (Nat.le_max_right k1 k2) m2]
  rw [levelSet_union_same_level, myLor_eq_lor]

/-- The **raw** `(level, mask)` code for `VX n ∪ VX m`, before re-canonicalization: upsample both
`canonIdx`-normalized masks to the common level `max k₁ k₂` and take `myLor`. Mirrors `VinterRaw`
verbatim, substituting `myLor` for `myLand`. -/
def VunionRaw (n m : ℕ) : ℕ :=
  Nat.pair (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
    (myLor
      (myUpsample (canonIdx n).unpair.1 (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
        (canonIdx n).unpair.2)
      (myUpsample (canonIdx m).unpair.1 (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
        (canonIdx m).unpair.2))

theorem primrec_VunionRaw : Nat.Primrec (fun t => VunionRaw t.unpair.1 t.unpair.2) := by
  have hcn : Nat.Primrec (fun t : ℕ => canonIdx t.unpair.1) := primrec_canonIdx.comp Nat.Primrec.left
  have hcm : Nat.Primrec (fun t : ℕ => canonIdx t.unpair.2) := primrec_canonIdx.comp Nat.Primrec.right
  have hk1 : Nat.Primrec (fun t : ℕ => (canonIdx t.unpair.1).unpair.1) := Nat.Primrec.left.comp hcn
  have hm1 : Nat.Primrec (fun t : ℕ => (canonIdx t.unpair.1).unpair.2) := Nat.Primrec.right.comp hcn
  have hk2 : Nat.Primrec (fun t : ℕ => (canonIdx t.unpair.2).unpair.1) := Nat.Primrec.left.comp hcm
  have hm2 : Nat.Primrec (fun t : ℕ => (canonIdx t.unpair.2).unpair.2) := Nat.Primrec.right.comp hcm
  have hkJ : Nat.Primrec (fun t : ℕ => max (canonIdx t.unpair.1).unpair.1 (canonIdx t.unpair.2).unpair.1) :=
    primrec_max hk1 hk2
  have hup1 : Nat.Primrec (fun t : ℕ => myUpsample (canonIdx t.unpair.1).unpair.1
      (max (canonIdx t.unpair.1).unpair.1 (canonIdx t.unpair.2).unpair.1)
      (canonIdx t.unpair.1).unpair.2) :=
    (primrec_myUpsample.comp (hk1.pair (hkJ.pair hm1))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hup2 : Nat.Primrec (fun t : ℕ => myUpsample (canonIdx t.unpair.2).unpair.1
      (max (canonIdx t.unpair.1).unpair.1 (canonIdx t.unpair.2).unpair.1)
      (canonIdx t.unpair.2).unpair.2) :=
    (primrec_myUpsample.comp (hk2.pair (hkJ.pair hm2))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hlor : Nat.Primrec (fun t : ℕ => myLor
      (myUpsample (canonIdx t.unpair.1).unpair.1
        (max (canonIdx t.unpair.1).unpair.1 (canonIdx t.unpair.2).unpair.1) (canonIdx t.unpair.1).unpair.2)
      (myUpsample (canonIdx t.unpair.2).unpair.1
        (max (canonIdx t.unpair.1).unpair.1 (canonIdx t.unpair.2).unpair.1) (canonIdx t.unpair.2).unpair.2)) :=
    (primrec_myLor.comp (hup1.pair hup2)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (hkJ.pair hlor).of_eq fun _ => rfl

/-- **`VunionRaw` realizes `VX n ∪ VX m`** at the `levelSet` level (unconditionally). -/
theorem levelSet_VunionRaw (n m : ℕ) :
    levelSet (VunionRaw n m).unpair.1 (VunionRaw n m).unpair.2 = VX n ∪ VX m := by
  unfold VunionRaw
  rw [unpair_pair_fst, unpair_pair_snd]
  exact (levelSet_myUnion (canonIdx n).unpair.1 (canonIdx n).unpair.2
    (canonIdx m).unpair.1 (canonIdx m).unpair.2).symm

/-- The union index: `canonIdx` of the raw union code `VunionRaw`. -/
def Vunion (n m : ℕ) : ℕ := canonIdx (VunionRaw n m)

theorem primrec_Vunion : Nat.Primrec (fun t => Vunion t.unpair.1 t.unpair.2) :=
  (primrec_canonIdx.comp primrec_VunionRaw).of_eq fun _ => rfl

/-- **`Vunion n m` genuinely indexes `VX n ∪ VX m`**, unconditionally — `VunionRaw n m` is already
non-empty (both `VX n`, `VX m` are non-empty, `VX_nonempty`, and a union of a non-empty set with
anything is non-empty), so `canonIdx` is a no-op on it (`canonIdx_eq_self_of_nonempty`), mirroring
`Vinter_spec`'s shape but with the hypothesis discharged internally rather than assumed. -/
theorem Vunion_spec (n m : ℕ) : VX (Vunion n m) = VX n ∪ VX m := by
  have hne : (levelSet (VunionRaw n m).unpair.1 (VunionRaw n m).unpair.2).Nonempty := by
    rw [levelSet_VunionRaw]; exact (VX_nonempty n).mono Set.subset_union_left
  unfold Vunion
  rw [VX_canonIdx]
  show levelSet (canonIdx (VunionRaw n m)).unpair.1 (canonIdx (VunionRaw n m)).unpair.2 = VX n ∪ VX m
  rw [canonIdx_eq_self_of_nonempty hne, levelSet_VunionRaw]

/-- **`Xₙ ∪ Xₘ` is always presentable as some `X_k`**, for `V` — witnessed directly by `Vunion`. -/
theorem V_union_exists (n m : ℕ) : ∃ k, VX k = VX n ∪ VX m := ⟨Vunion n m, Vunion_spec n m⟩

/-- **7.1(i)-for-`∪`, for `V`**: trivially recursively decidable (the always-`1` constant). -/
theorem V_union_computable : RecDecidable₂ (fun n m => ∃ k, VX k = VX n ∪ VX m) :=
  ⟨fun _ => 1, Nat.Primrec.const 1, fun t => iff_of_true (V_union_exists t.unpair.1 t.unpair.2) rfl⟩

/-- `Vunion_spec`, repackaged to accept (and discard) `IsComputableUnion`'s hypothesis. -/
theorem Vunion_spec' {n m : ℕ} (_ : ∃ k, VX k = VX n ∪ VX m) : VX (Vunion n m) = VX n ∪ VX m :=
  Vunion_spec n m

/-- **`V` has a computable `∪`.** -/
def V_isComputableUnion : IsComputableUnion VComputablePresentation where
  unionIdx := Vunion
  unionIdx_primrec := primrec_Vunion
  unionIdx_spec := Vunion_spec'
  union_computable := V_union_computable

end Scott1980.Neighborhood

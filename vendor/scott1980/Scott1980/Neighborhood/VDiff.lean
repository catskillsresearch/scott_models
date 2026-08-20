/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.LevelSetPrimrec
import Scott1980.Neighborhood.Exercise812c
import Scott1980.Neighborhood.Exercise812d

/-!
# Exercise 8.12(f), prerequisite — `V` has a computable set-difference (`IsComputableDiff`)

`Exercise812d.lean`'s `IsComputableDiff` (`(d)(3)(a)`) has so far only been instantiated for `U`
(`Exercise812eD.lean`'s `U_isComputableDiff`/`Udiff`). This file supplies the missing `V`-side
instance, `V_isComputableDiff`, needed by `8.12(f)`'s `splitFromBisection VComputablePresentation
… UComputableBisection` (`V` is the *prober* for `(f)`, symmetric to `U` being the prober for
`(e)`).

## Design

Mirrors `LevelSetPrimrec.lean`'s `VinterRaw`/`Vinter` exactly, substituting `Exercise812c.lean`'s
`levelSet_diff` for `levelSet_myInter` as the driving mathematical fact. `levelSet_diff`'s formula
combines two upsampled masks via the bitwise "and-not" identity `a ^^^ (a &&& b)`
(`testBit_xor_and_self`) instead of plain `&&&` — so the one new piece of `Nat.Primrec`
infrastructure needed is a computable version of that combinator. Rather than re-deriving the
"and-not" identity arithmetically, we build a fresh choice-free primitive-recursive bitwise XOR
(`myXor`), mirroring `myLand`/`myLor` bit-for-bit (`lowXor`/`xorStep`, `Nat.testBit_xor` in place of
`Nat.testBit_and`/`Nat.testBit_lor`), and simply compose it with the already-`Pass` `myLand`:
`myAndNot a b := myXor a (myLand a b)` realizes `a ^^^ (a &&& b)` for free from
`myXor_eq_xor`/`myLand_eq_land`, no new arithmetic identity needed.
-/

namespace Scott1980.Neighborhood

open Domain.Recursive NeighborhoodSystem

/-! ## A choice-free primitive-recursive bitwise XOR (`myXor`)

Mirrors `myLand` (`LevelSetPrimrec.lean`) bit-for-bit: `lowXor`/`xorStep` in place of
`lowAnd`/`landStep`, `Nat.testBit_xor` in place of `Nat.testBit_and`. -/

/-- The low-bit XOR `(x ^^^ y) % 2`, in arithmetic `{0,1}`-valued form: the sum of the low bits,
mod `2`. -/
def lowXor (x y : ℕ) : ℕ := (x % 2 + y % 2) % 2

theorem primrec_lowXor : Nat.Primrec (fun t => lowXor t.unpair.1 t.unpair.2) :=
  (primrec_mod2.comp
    (primrec_add₂ (primrec_mod2.comp Nat.Primrec.left) (primrec_mod2.comp Nat.Primrec.right))).of_eq
    fun _ => rfl

/-- `lowXor x y = (x ^^^ y) % 2`. -/
theorem lowXor_eq_mod (x y : ℕ) : lowXor x y = (x ^^^ y) % 2 := by
  unfold lowXor
  rw [Nat.xor_mod_two_eq]
  exact (Nat.add_mod x y 2).symm

/-- Packed iteration state `pair (pair curA curB) (pair weight acc)` for the bitwise-XOR fold. -/
def xorStep (s : ℕ) : ℕ :=
  Nat.pair (Nat.pair (s.unpair.1.unpair.1 / 2) (s.unpair.1.unpair.2 / 2))
    (Nat.pair (2 * s.unpair.2.unpair.1)
      (s.unpair.2.unpair.2 + s.unpair.2.unpair.1 * lowXor s.unpair.1.unpair.1 s.unpair.1.unpair.2))

theorem primrec_xorStep : Nat.Primrec xorStep := by
  have hA : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have hB : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.left
  have hW : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hAcc : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hlow : Nat.Primrec (fun s : ℕ => lowXor s.unpair.1.unpair.1 s.unpair.1.unpair.2) :=
    (primrec_lowXor.comp (hA.pair hB)).of_eq fun s => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (((primrec_div2.comp hA).pair (primrec_div2.comp hB)).pair
    ((primrec_mul₂ (Nat.Primrec.const 2) hW).pair
      (primrec_add₂ hAcc (primrec_mul₂ hW hlow)))).of_eq fun _ => rfl

/-- The iterative bitwise XOR: iterate `xorStep` `a + b` times from the initial state, and read off
the accumulator. -/
def myXor (a b : ℕ) : ℕ :=
  (xorStep^[a + b] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2

theorem primrec_myXor : Nat.Primrec (fun t => myXor t.unpair.1 t.unpair.2) := by
  have hbase : Nat.Primrec
      (fun z => Nat.pair (Nat.pair z.unpair.1 z.unpair.2) (Nat.pair 1 0)) :=
    (Nat.Primrec.left.pair Nat.Primrec.right).pair
      ((Nat.Primrec.const 1).pair (Nat.Primrec.const 0))
  have hstep : Nat.Primrec (fun w => xorStep w.unpair.2.unpair.2) :=
    primrec_xorStep.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hprec := Nat.Primrec.prec hbase hstep
  have hcount : Nat.Primrec (fun t => t.unpair.1 + t.unpair.2) :=
    primrec_add₂ Nat.Primrec.left Nat.Primrec.right
  refine ((Nat.Primrec.right.comp Nat.Primrec.right).comp
    (hprec.comp (primrec_id.pair hcount))).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rw [rec_const_iterate]
  rfl

/-- One recursion step for `Nat.xor` on the low bit: `x ^^^ y = 2 (x/2 ^^^ y/2) + lowXor x y`. -/
theorem xor_low_rec (x y : ℕ) : x ^^^ y = 2 * (x / 2 ^^^ y / 2) + lowXor x y := by
  have hdiv : (x ^^^ y) / 2 = x / 2 ^^^ y / 2 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [← Nat.testBit_add_one, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_add_one,
      Nat.testBit_add_one]
  have hmod := lowXor_eq_mod x y
  conv_lhs => rw [← Nat.div_add_mod (x ^^^ y) 2]
  rw [hdiv, hmod]

/-- **Invariant of the bitwise-XOR iteration.** After `k` steps the two running arguments are
`a / 2^k`, `b / 2^k`, the weight is `2^k`, and `acc + 2^k · (a/2^k ^^^ b/2^k) = a ^^^ b`. -/
theorem xorStep_iter_spec (a b : ℕ) : ∀ k,
    (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1 = a / 2 ^ k ∧
    (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 = b / 2 ^ k ∧
    (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1 = 2 ^ k ∧
    (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2 +
        2 ^ k * (a / 2 ^ k ^^^ b / 2 ^ k) = a ^^^ b := by
  intro k
  induction k with
  | zero =>
    simp only [Function.iterate_zero_apply, unpair_pair_fst, unpair_pair_snd, pow_zero,
      Nat.div_one, Nat.one_mul, Nat.zero_add, true_and]
  | succ k ih =>
    obtain ⟨hA, hB, hW, hAcc⟩ := ih
    rw [Function.iterate_succ_apply']
    have hdd : a / 2 ^ (k + 1) = (a / 2 ^ k) / 2 := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have hdd' : b / 2 ^ (k + 1) = (b / 2 ^ k) / 2 := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have p11 : (xorStep (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.1.unpair.1
        = (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1 / 2 := by
      unfold xorStep; rw [unpair_pair_fst, unpair_pair_fst]
    have p12 : (xorStep (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.1.unpair.2
        = (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 / 2 := by
      unfold xorStep; rw [unpair_pair_fst, unpair_pair_snd]
    have p21 : (xorStep (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.2.unpair.1
        = 2 * (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1 := by
      unfold xorStep; rw [unpair_pair_snd, unpair_pair_fst]
    have p22 : (xorStep (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.2.unpair.2
        = (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2
          + (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1
            * lowXor (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1
                (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 := by
      unfold xorStep; rw [unpair_pair_snd, unpair_pair_snd]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [p11, hA, Nat.div_div_eq_div_mul, ← pow_succ]
    · rw [p12, hB, Nat.div_div_eq_div_mul, ← pow_succ]
    · rw [p21, hW, ← pow_succ']
    · rw [p22, hA, hB, hW, hdd, hdd', pow_succ, ← hAcc, xor_low_rec (a / 2 ^ k) (b / 2 ^ k)]
      ring

/-- **Correctness of the iterative bitwise XOR.** `myXor a b = a ^^^ b`. -/
theorem myXor_eq_xor (a b : ℕ) : myXor a b = a ^^^ b := by
  unfold myXor
  obtain ⟨_, _, _, hAcc⟩ := xorStep_iter_spec a b (a + b)
  have ha0 : a / 2 ^ (a + b) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_right a b)))
  have hb0 : b / 2 ^ (a + b) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_left b a)))
  rw [ha0, hb0] at hAcc
  simpa using hAcc

/-! ## The "and-not" combinator `myAndNot a b = a ^^^ (a &&& b)` -/

/-- `a` with `b`'s bits cleared: `a ^^^ (a &&& b)` (`testBit_xor_and_self`), computed via `myXor`
composed with the already-`Pass` `myLand`. -/
def myAndNot (a b : ℕ) : ℕ := myXor a (myLand a b)

theorem primrec_myAndNot : Nat.Primrec (fun t => myAndNot t.unpair.1 t.unpair.2) := by
  have hland : Nat.Primrec (fun t : ℕ => myLand t.unpair.1 t.unpair.2) := primrec_myLand
  exact (primrec_myXor.comp (Nat.Primrec.left.pair hland)).of_eq fun t => by
    simp only [myAndNot, unpair_pair_fst, unpair_pair_snd]

theorem myAndNot_eq (a b : ℕ) : myAndNot a b = a ^^^ (a &&& b) := by
  unfold myAndNot; rw [myXor_eq_xor, myLand_eq_land]

/-! ## `VdiffRaw`/`Vdiff` — `V`'s computable set-difference

Mirrors `VinterRaw`/`Vinter` exactly, substituting `levelSet_diff` (`Exercise812c.lean`) for
`levelSet_myInter` and `myAndNot` for `myLand`. -/

/-- **The "same level" set-difference formula**, mirroring `Exercise812.lean`'s
`levelSet_inter_same_level` exactly (`&&&` becomes the "and-not" combinator `a ^^^ (a &&& b)`,
via `testBit_xor_and_self`). -/
theorem levelSet_diff_same_level (k m₁ m₂ : ℕ) :
    levelSet k m₁ \ levelSet k m₂ = levelSet k (m₁ ^^^ (m₁ &&& m₂)) := by
  ext n; simp [levelSet]

/-- **Computable version of `levelSet_diff_same_level`, upsampled to a common level** — mirrors
`levelSet_myInter` exactly, substituting `myAndNot` for `myLand`. -/
theorem levelSet_myDiff (k1 m1 k2 m2 : ℕ) :
    levelSet k1 m1 \ levelSet k2 m2
      = levelSet (max k1 k2) (myAndNot (myUpsample k1 (max k1 k2) m1) (myUpsample k2 (max k1 k2) m2)) := by
  conv_lhs => rw [← levelSet_myUpsample (Nat.le_max_left k1 k2) (m := m1),
    ← levelSet_myUpsample (Nat.le_max_right k1 k2) (m := m2)]
  rw [levelSet_diff_same_level, myAndNot_eq]

/-- The **raw** `(level, mask)` code for `VX n \ VX m`, before re-canonicalization: upsample both
`canonIdx`-normalized masks to the common level `max k₁ k₂` and take `myAndNot`. -/
def VdiffRaw (n m : ℕ) : ℕ :=
  Nat.pair (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
    (myAndNot
      (myUpsample (canonIdx n).unpair.1 (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
        (canonIdx n).unpair.2)
      (myUpsample (canonIdx m).unpair.1 (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
        (canonIdx m).unpair.2))

theorem primrec_VdiffRaw : Nat.Primrec (fun t => VdiffRaw t.unpair.1 t.unpair.2) := by
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
  have handnot : Nat.Primrec (fun t : ℕ => myAndNot
      (myUpsample (canonIdx t.unpair.1).unpair.1
        (max (canonIdx t.unpair.1).unpair.1 (canonIdx t.unpair.2).unpair.1) (canonIdx t.unpair.1).unpair.2)
      (myUpsample (canonIdx t.unpair.2).unpair.1
        (max (canonIdx t.unpair.1).unpair.1 (canonIdx t.unpair.2).unpair.1) (canonIdx t.unpair.2).unpair.2)) :=
    (primrec_myAndNot.comp (hup1.pair hup2)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (hkJ.pair handnot).of_eq fun _ => rfl

/-- **`VdiffRaw` realizes `VX n \ VX m`** at the `levelSet` level (unconditionally). -/
theorem levelSet_VdiffRaw (n m : ℕ) :
    levelSet (VdiffRaw n m).unpair.1 (VdiffRaw n m).unpair.2 = VX n \ VX m := by
  unfold VdiffRaw
  rw [unpair_pair_fst, unpair_pair_snd]
  exact (levelSet_myDiff (canonIdx n).unpair.1 (canonIdx n).unpair.2
    (canonIdx m).unpair.1 (canonIdx m).unpair.2).symm

/-- **Scott's consistency condition for `\` reduces to non-emptiness**, mirroring
`Vcons_iff_nonempty_inter`. -/
theorem Vdiff_iff_nonempty (n m : ℕ) :
    (∃ k, VX k = VX n \ VX m) ↔ (VX n \ VX m).Nonempty := by
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk]; exact VX_nonempty k
  · intro hne
    rw [← levelSet_VdiffRaw] at hne
    have hVmem : V.mem (VX n \ VX m) := by
      rw [← levelSet_VdiffRaw]
      exact ⟨(VdiffRaw n m).unpair.1, (VdiffRaw n m).unpair.2, rfl, hne⟩
    obtain ⟨k, hk⟩ := V_surj_VX hVmem
    exact ⟨k, hk⟩

/-- **7.1(i)-for-`\`, for `V`**: `Xₙ \ Xₘ = X_k` for some `k` is recursively decidable. -/
theorem V_diff_computable : RecDecidable₂ (fun n m => ∃ k, VX k = VX n \ VX m) := by
  have hvr : Nat.Primrec (fun t : ℕ => VdiffRaw t.unpair.1 t.unpair.2) := primrec_VdiffRaw
  have hfprim : Nat.Primrec (fun t : ℕ => myLevelSetNonempty (VdiffRaw t.unpair.1 t.unpair.2).unpair.1
      (VdiffRaw t.unpair.1 t.unpair.2).unpair.2) :=
    (primrec_myLevelSetNonempty.comp ((Nat.Primrec.left.comp hvr).pair
      (Nat.Primrec.right.comp hvr))).of_eq fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  refine RecDecidable₂.of_paired_zero_one_char hfprim ?_ ?_
  · intro t
    dsimp only
    have := myLevelSetNonempty_le_one (VdiffRaw t.unpair.1 t.unpair.2).unpair.1
      (VdiffRaw t.unpair.1 t.unpair.2).unpair.2
    omega
  · intro n m
    dsimp only
    rw [unpair_pair_fst, unpair_pair_snd, Vdiff_iff_nonempty, ← levelSet_VdiffRaw,
      myLevelSetNonempty_eq_one_iff]

/-- The difference index: `canonIdx` of the raw difference code `VdiffRaw`. -/
def Vdiff (n m : ℕ) : ℕ := canonIdx (VdiffRaw n m)

theorem primrec_Vdiff : Nat.Primrec (fun t => Vdiff t.unpair.1 t.unpair.2) :=
  (primrec_canonIdx.comp primrec_VdiffRaw).of_eq fun _ => rfl

theorem Vdiff_spec {n m : ℕ} (h : ∃ k, VX k = VX n \ VX m) : VX (Vdiff n m) = VX n \ VX m := by
  have hne : (levelSet (VdiffRaw n m).unpair.1 (VdiffRaw n m).unpair.2).Nonempty := by
    rw [levelSet_VdiffRaw]; obtain ⟨k, hk⟩ := h; rw [← hk]; exact VX_nonempty k
  unfold Vdiff
  rw [VX_canonIdx]
  show levelSet (canonIdx (VdiffRaw n m)).unpair.1 (canonIdx (VdiffRaw n m)).unpair.2 = VX n \ VX m
  rw [canonIdx_eq_self_of_nonempty hne, levelSet_VdiffRaw]

/-- **`V` has a computable `\`**, the missing prerequisite for Exercise 8.12(f). -/
def V_isComputableDiff : IsComputableDiff VComputablePresentation where
  diffIdx := Vdiff
  diffIdx_primrec := primrec_Vdiff
  diffIdx_spec := Vdiff_spec
  diff_computable := V_diff_computable

end Scott1980.Neighborhood

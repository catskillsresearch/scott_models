/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Exercise812
import Scott1980.Neighborhood.Definition71

/-!
# Exercise 8.12(b) (Scott 1981, PRG-19, Lecture VIII) — `V`'s computable presentation

Builds the `Nat.Primrec` bit-manipulation infrastructure `Exercise812.lean`'s docstring flagged as
missing ("upsample a bitmask from level `k` to level `k'`, computably"), and assembles it into a
genuine `ComputablePresentation V`, closing Exercise 8.12(b).

## Design

Mirrors `UComputablePresentation.lean`'s two-layer shape (canonicalize an arbitrary code, then wire
Scott's two relations) combined with `Example78.lean`'s choice-free bit-level idiom (`myLor`, built
by hand since mathlib's `Nat.lor`/`Nat.testBit` are not exposed as `Nat.Primrec`):

* **Bit extraction** (`myDivPow2`/`myTestBit`): `Nat.Primrec` versions of `n ↦ n / 2^ℓ` and
  `n ↦ n.testBit ℓ`, built by iterating "halve" `ℓ` times via `Nat.Primrec.prec` (the same
  "iterate a step a data-dependent number of times" idiom `primrec_foldCode`/`myLor` already use).
* **`myLand`** (bitwise AND): a hand-built choice-free primitive-recursive `&&&`, mirroring `myLor`
  bit-for-bit (literally: `lowOr`/`lorStep` become `lowAnd`/`landStep`, `Nat.testBit_lor` becomes
  `Nat.testBit_and`).
* **`myUpsample`** (the missing piece): re-expressing a level-`k` bitmask at level `k' ≥ k`. The key
  realization is that `Exercise812.lean`'s `upsample`'s one-level step is *arithmetic*, not
  bit-by-bit: doubling `m` from level `k` to `k+1` duplicates its low `2^k` bits into a second copy
  shifted up by `2^k` positions, i.e. `m' + m' * 2 ^ (2 ^ k)` where `m' := m % 2 ^ (2 ^ k)` is `m`'s
  low `2^k`-bit truncation (`myModPow2`, itself built from `myDivPow2`). Truncating first avoids any
  addition-carry ambiguity from `m`'s "junk" bits at positions `≥ 2^k` (irrelevant to `levelSet k m`
  as a *set*, but would corrupt a naive `m + m * 2^(2^k)`). Iterating this step `k' - k` times (again
  via `Nat.Primrec.prec`, jointly tracking the current level alongside the mask, exactly as `lorStep`
  jointly tracks two running arguments) gives `myUpsample`.
* **Nonemptiness** (`myLevelSetNonempty`): `(levelSet k m).Nonempty ↔ ∃ ℓ < 2^k, m.testBit ℓ`
  (`levelSet_nonempty_iff`) is a bounded `∃` of a decidable predicate, handled by the existing
  `bExistsFn` combinator with `myTestBit` as the body — no new quantifier infrastructure needed.
* **Canonicalization** (`canonIdx`/`VX`): exactly `UComputablePresentation.lean`'s `canonCode`
  pattern, but simpler (no "clip to `[0,1)`" step is needed — a `(k, m)` pair is always a
  *syntactically* well-formed level/mask pair, only possibly empty): keep a code `n = pair k m`
  unchanged if `levelSet k m` is non-empty, else fall back to the fixed master code `pair 0 1`
  (`levelSet 0 1 = univ`, `levelSet_zero_one`).
* **Scott's two relations reduce to bitmask arithmetic**: `Vinter n m`'s raw intersection is
  `myUpsample`-both-then-`myLand` at the joint level `max k₁ k₂` (mirroring `levelSet_inter`
  exactly), and consistency reduces to that merged mask being non-empty (`myLevelSetNonempty`);
  equality of two canonicalized codes' `levelSet`s reduces to equality of their masks *after*
  upsampling both to a common level (`levelSet` is injective in the mask at any fixed level,
  `levelSet_inj_of_common_level`), decided by `RecDecidable.natEq`.

Everything here is choice-free by construction (`Nat.Primrec` terms built from the seven base
combinators plus already-choice-free helpers); the correctness *lemmas* connecting these to
`Exercise812.lean`'s `Set`-level `levelSet`/`upsample` go through ordinary `Nat` arithmetic
(`Nat.testBit_eq_decide_div_mod_eq`, `Nat.testBit_and`, `Nat.div_add_mod`, …), which — like every
other file in this project touching `ℕ`'s order/decidability API — reports the same inherited
`Classical.choice` footprint documented in `Definition87.lean`/`Exercise812.lean`, not a new choice
introduced here.
-/

namespace Scott1980.Neighborhood

open Domain.Recursive NeighborhoodSystem

/-! ### Bit extraction: `myDivPow2`, `myModPow2`, `myTestBit` -/

/-- `Nat.rec`-based iterate of "halve", i.e. `myDivPow2 m ℓ = m / 2 ^ ℓ`
(`myDivPow2_eq`), built via `Nat.Primrec.prec` on the count `ℓ` (params `m` fixed throughout the
recursion), mirroring `primrec_foldCode`'s "iterate a step a data-dependent number of times" idiom. -/
def myDivPow2 (m ℓ : ℕ) : ℕ := Nat.unpaired (fun z n => n.rec z (fun _ ih => ih / 2)) (Nat.pair m ℓ)

theorem primrec_myDivPow2 : Nat.Primrec (fun t => myDivPow2 t.unpair.1 t.unpair.2) := by
  have hg : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2 / 2) :=
    primrec_div2.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  refine (Nat.Primrec.prec Nat.Primrec.id hg).of_eq fun t => ?_
  unfold myDivPow2
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]

theorem myDivPow2_eq (m ℓ : ℕ) : myDivPow2 m ℓ = m / 2 ^ ℓ := by
  unfold myDivPow2
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    show (ℓ.rec m (fun _ ih => ih / 2)) / 2 = m / 2 ^ (ℓ + 1)
    rw [ih, Nat.div_div_eq_div_mul, ← pow_succ]

/-- `myModPow2 m s = m % 2 ^ s`, derived from `myDivPow2` via `Nat.div_add_mod`
(`myModPow2_eq`): no separate general-purpose primitive-recursive `mod` is needed. -/
def myModPow2 (m s : ℕ) : ℕ := m - myDivPow2 m s * 2 ^ s

theorem primrec_myModPow2 : Nat.Primrec (fun t => myModPow2 t.unpair.1 t.unpair.2) := by
  have hpow : Nat.Primrec (fun t : ℕ => (2:ℕ) ^ t.unpair.2) := primrec_two_pow Nat.Primrec.right
  have hdiv : Nat.Primrec (fun t : ℕ => myDivPow2 t.unpair.1 t.unpair.2) := primrec_myDivPow2
  exact (primrec_sub₂ Nat.Primrec.left (primrec_mul₂ hdiv hpow)).of_eq fun t => rfl

theorem myModPow2_eq (m s : ℕ) : myModPow2 m s = m % 2 ^ s := by
  unfold myModPow2
  rw [myDivPow2_eq]
  have h : m / 2 ^ s * 2 ^ s + m % 2 ^ s = m := by
    rw [mul_comm]; exact Nat.div_add_mod m (2 ^ s)
  omega

theorem myModPow2_lt (m s : ℕ) : myModPow2 m s < 2 ^ s := by
  rw [myModPow2_eq]; exact Nat.mod_lt m (Nat.two_pow_pos s)

/-- `myTestBit m ℓ ∈ {0,1}` is a `Nat.Primrec` version of `m.testBit ℓ`
(`myTestBit_eq_one_iff`), via `myDivPow2` and mathlib's own
`Nat.testBit_eq_decide_div_mod_eq : m.testBit ℓ = decide (m / 2 ^ ℓ % 2 = 1)`. -/
def myTestBit (m ℓ : ℕ) : ℕ := myDivPow2 m ℓ % 2

theorem primrec_myTestBit : Nat.Primrec (fun t => myTestBit t.unpair.1 t.unpair.2) :=
  (primrec_mod2.comp primrec_myDivPow2).of_eq fun _ => rfl

theorem myTestBit_le_one (m ℓ : ℕ) : myTestBit m ℓ ≤ 1 := by
  unfold myTestBit
  rcases Nat.mod_two_eq_zero_or_one (myDivPow2 m ℓ) with h | h <;> omega

theorem myTestBit_eq_one_iff (m ℓ : ℕ) : myTestBit m ℓ = 1 ↔ m.testBit ℓ = true := by
  unfold myTestBit
  rw [myDivPow2_eq, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]

/-! ### Choice-free primitive-recursive bitwise AND (`myLand`)

Mirrors `myLor` (`Recursive.lean`) bit-for-bit, swapping `Nat.testBit_lor`/`lowOr` for
`Nat.testBit_and`/`lowAnd`. Needed because `levelSet_inter`'s formula combines two upsampled masks
with `&&&`, and mathlib's `Nat.land` is (like `Nat.lor`) not itself exposed as `Nat.Primrec`. -/

/-- The low-bit AND `(x &&& y) % 2`, in arithmetic `{0,1}`-valued form: simply the product of the
low bits (`1` iff both are `1`). -/
def lowAnd (x y : ℕ) : ℕ := x % 2 * (y % 2)

theorem primrec_lowAnd : Nat.Primrec (fun t => lowAnd t.unpair.1 t.unpair.2) :=
  (primrec_mul₂ (primrec_mod2.comp Nat.Primrec.left) (primrec_mod2.comp Nat.Primrec.right)).of_eq
    fun _ => rfl

/-- `lowAnd x y = (x &&& y) % 2`. -/
theorem lowAnd_eq_mod (x y : ℕ) : lowAnd x y = (x &&& y) % 2 := by
  have key : ((x &&& y) % 2 = 1) ↔ (x % 2 = 1 ∧ y % 2 = 1) := by
    have hb := Nat.testBit_and x y 0
    rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero] at hb
    rw [← decide_eq_decide, hb, Bool.decide_and]
  unfold lowAnd
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;> rw [hx, hy]
  · have hne : (x &&& y) % 2 ≠ 1 := fun h => by have := key.mp h; omega
    omega
  · have hne : (x &&& y) % 2 ≠ 1 := fun h => by have := key.mp h; omega
    omega
  · have hne : (x &&& y) % 2 ≠ 1 := fun h => by have := key.mp h; omega
    omega
  · exact (key.mpr ⟨hx, hy⟩).symm

/-- Packed iteration state `pair (pair curA curB) (pair weight acc)` for the bitwise-AND fold. -/
def landStep (s : ℕ) : ℕ :=
  Nat.pair (Nat.pair (s.unpair.1.unpair.1 / 2) (s.unpair.1.unpair.2 / 2))
    (Nat.pair (2 * s.unpair.2.unpair.1)
      (s.unpair.2.unpair.2 + s.unpair.2.unpair.1 * lowAnd s.unpair.1.unpair.1 s.unpair.1.unpair.2))

theorem primrec_landStep : Nat.Primrec landStep := by
  have hA : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have hB : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.left
  have hW : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hAcc : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hlow : Nat.Primrec (fun s : ℕ => lowAnd s.unpair.1.unpair.1 s.unpair.1.unpair.2) :=
    (primrec_lowAnd.comp (hA.pair hB)).of_eq fun s => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (((primrec_div2.comp hA).pair (primrec_div2.comp hB)).pair
    ((primrec_mul₂ (Nat.Primrec.const 2) hW).pair
      (primrec_add₂ hAcc (primrec_mul₂ hW hlow)))).of_eq fun _ => rfl

/-- The iterative bitwise AND: iterate `landStep` `a + b` times from the initial state, and read off
the accumulator. -/
def myLand (a b : ℕ) : ℕ :=
  (landStep^[a + b] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2

theorem primrec_myLand : Nat.Primrec (fun t => myLand t.unpair.1 t.unpair.2) := by
  have hbase : Nat.Primrec
      (fun z => Nat.pair (Nat.pair z.unpair.1 z.unpair.2) (Nat.pair 1 0)) :=
    (Nat.Primrec.left.pair Nat.Primrec.right).pair
      ((Nat.Primrec.const 1).pair (Nat.Primrec.const 0))
  have hstep : Nat.Primrec (fun w => landStep w.unpair.2.unpair.2) :=
    primrec_landStep.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hprec := Nat.Primrec.prec hbase hstep
  have hcount : Nat.Primrec (fun t => t.unpair.1 + t.unpair.2) :=
    primrec_add₂ Nat.Primrec.left Nat.Primrec.right
  refine ((Nat.Primrec.right.comp Nat.Primrec.right).comp
    (hprec.comp (primrec_id.pair hcount))).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rw [rec_const_iterate]
  rfl

/-- One recursion step for `Nat.land` on the low bit: `x &&& y = 2 (x/2 &&& y/2) + lowAnd x y`. -/
theorem land_low_rec (x y : ℕ) : x &&& y = 2 * (x / 2 &&& y / 2) + lowAnd x y := by
  have hdiv : (x &&& y) / 2 = x / 2 &&& y / 2 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [← Nat.testBit_add_one, Nat.testBit_and, Nat.testBit_and, Nat.testBit_add_one,
      Nat.testBit_add_one]
  have hmod := lowAnd_eq_mod x y
  conv_lhs => rw [← Nat.div_add_mod (x &&& y) 2]
  rw [hdiv, hmod]

/-- **Invariant of the bitwise-AND iteration.** After `k` steps the two running arguments are
`a / 2^k`, `b / 2^k`, the weight is `2^k`, and `acc + 2^k · (a/2^k &&& b/2^k) = a &&& b`. -/
theorem landStep_iter_spec (a b : ℕ) : ∀ k,
    (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1 = a / 2 ^ k ∧
    (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 = b / 2 ^ k ∧
    (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1 = 2 ^ k ∧
    (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2 +
        2 ^ k * (a / 2 ^ k &&& b / 2 ^ k) = a &&& b := by
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
    have p11 : (landStep (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.1.unpair.1
        = (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1 / 2 := by
      unfold landStep; rw [unpair_pair_fst, unpair_pair_fst]
    have p12 : (landStep (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.1.unpair.2
        = (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 / 2 := by
      unfold landStep; rw [unpair_pair_fst, unpair_pair_snd]
    have p21 : (landStep (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.2.unpair.1
        = 2 * (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1 := by
      unfold landStep; rw [unpair_pair_snd, unpair_pair_fst]
    have p22 : (landStep (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.2.unpair.2
        = (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2
          + (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1
            * lowAnd (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1
                (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 := by
      unfold landStep; rw [unpair_pair_snd, unpair_pair_snd]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [p11, hA, Nat.div_div_eq_div_mul, ← pow_succ]
    · rw [p12, hB, Nat.div_div_eq_div_mul, ← pow_succ]
    · rw [p21, hW, ← pow_succ']
    · rw [p22, hA, hB, hW, hdd, hdd', pow_succ, ← hAcc, land_low_rec (a / 2 ^ k) (b / 2 ^ k)]
      ring

/-- **Correctness of the iterative bitwise AND.** `myLand a b = a &&& b`. -/
theorem myLand_eq_land (a b : ℕ) : myLand a b = a &&& b := by
  unfold myLand
  obtain ⟨_, _, _, hAcc⟩ := landStep_iter_spec a b (a + b)
  have ha0 : a / 2 ^ (a + b) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_right a b)))
  have hb0 : b / 2 ^ (a + b) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_left b a)))
  rw [ha0, hb0] at hAcc
  simpa using hAcc

/-! ### `myUpsample`: a computable version of `Exercise812.lean`'s `upsample`

The one-level step is *arithmetic*: `myUpsampleStep k m := 2 ^ (2 ^ k) * m' + m'` where
`m' := myModPow2 m (2 ^ k)` is `m`'s low-`2^k`-bit truncation. Truncating first is what makes the
formula correct regardless of any "junk" bits `m` may carry at positions `≥ 2^k` (irrelevant to
`levelSet k m` as a set, but would corrupt a naive `m + m * 2^(2^k)`): mathlib's
`Nat.testBit_two_pow_mul_add` handles exactly the "low/high digit" splitting this needs, given the
truncation bound `myModPow2_lt`. -/

/-- One computable upsampling step: re-express a level-`k` mask at level `k + 1` by duplicating its
low `2^k` bits into a second copy shifted up by `2^k` positions. -/
def myUpsampleStep (k m : ℕ) : ℕ :=
  2 ^ (2 ^ k) * myModPow2 m (2 ^ k) + myModPow2 m (2 ^ k)

theorem primrec_myUpsampleStep : Nat.Primrec (fun t => myUpsampleStep t.unpair.1 t.unpair.2) := by
  have hs : Nat.Primrec (fun t : ℕ => (2:ℕ) ^ t.unpair.1) := primrec_two_pow Nat.Primrec.left
  have hm' : Nat.Primrec (fun t : ℕ => myModPow2 t.unpair.2 (2 ^ t.unpair.1)) :=
    (primrec_myModPow2.comp (Nat.Primrec.right.pair hs)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have h2s : Nat.Primrec (fun t : ℕ => (2:ℕ) ^ (2 ^ t.unpair.1)) := primrec_two_pow hs
  exact (primrec_add₂ (primrec_mul₂ h2s hm') hm').of_eq fun t => rfl

/-- `j % s = j - s` when `s ≤ j < 2 * s` (the single-wraparound case of `%`). -/
private theorem mod_eq_sub_of_le_of_lt_two_mul {j s : ℕ} (h1 : s ≤ j) (h2 : j < 2 * s) :
    j % s = j - s := by
  have heq : j = (j - s) + s := by omega
  calc j % s = ((j - s) + s) % s := by rw [← heq]
    _ = (j - s) % s := Nat.add_mod_right _ _
    _ = j - s := Nat.mod_eq_of_lt (by omega)

/-- **The key correctness lemma for `myUpsampleStep`**: it realizes `Exercise812.lean`'s
mathematical `upsample` at the `levelSet` level, one step at a time. -/
theorem levelSet_myUpsampleStep (k m : ℕ) :
    levelSet (k + 1) (myUpsampleStep k m) = levelSet k m := by
  ext n
  simp only [mem_levelSet]
  have hlt : myModPow2 m (2 ^ k) < 2 ^ (2 ^ k) := myModPow2_lt m (2 ^ k)
  have hstep : myUpsampleStep k m
      = 2 ^ (2 ^ k) * myModPow2 m (2 ^ k) + myModPow2 m (2 ^ k) := rfl
  rw [hstep, Nat.testBit_two_pow_mul_add _ hlt]
  have hmm : n % 2 ^ k = n % 2 ^ (k + 1) % 2 ^ k :=
    (Nat.mod_mod_of_dvd n (pow_dvd_pow 2 (Nat.le_succ k))).symm
  have hjlt : n % 2 ^ (k + 1) < 2 ^ (k + 1) := Nat.mod_lt n (Nat.two_pow_pos (k + 1))
  have h2 : (2:ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  by_cases hcase : n % 2 ^ (k + 1) < 2 ^ k
  · rw [if_pos hcase, myModPow2_eq, Nat.testBit_mod_two_pow, decide_eq_true_iff.mpr hcase,
      Bool.true_and, hmm, Nat.mod_eq_of_lt hcase]
  · have hge : 2 ^ k ≤ n % 2 ^ (k + 1) := Nat.le_of_not_lt hcase
    have hsub : n % 2 ^ (k + 1) - 2 ^ k < 2 ^ k := by omega
    rw [if_neg hcase, myModPow2_eq, Nat.testBit_mod_two_pow, decide_eq_true_iff.mpr hsub,
      Bool.true_and, hmm, mod_eq_sub_of_le_of_lt_two_mul hge (h2 ▸ hjlt)]

/-- Joint (level, mask) iteration state for `myUpsample`: `pair level mask`. -/
def myUpsampleJointStep (s : ℕ) : ℕ :=
  Nat.pair (s.unpair.1 + 1) (myUpsampleStep s.unpair.1 s.unpair.2)

theorem primrec_myUpsampleJointStep : Nat.Primrec myUpsampleJointStep := by
  have hstep : Nat.Primrec (fun s : ℕ => myUpsampleStep s.unpair.1 s.unpair.2) :=
    primrec_myUpsampleStep
  exact ((Nat.Primrec.succ.comp Nat.Primrec.left).pair hstep).of_eq fun _ => rfl

/-- Unfolding equation for `myUpsampleJointStep`, stated so `rw` fires on a single (outer)
occurrence rather than `unfold`ing every nested occurrence (in particular, the ones hidden inside
an already-iterated `myUpsampleJointStep^[d]` term). -/
theorem myUpsampleJointStep_eq (s : ℕ) :
    myUpsampleJointStep s = Nat.pair (s.unpair.1 + 1) (myUpsampleStep s.unpair.1 s.unpair.2) := rfl

/-- Iterate `myUpsampleJointStep` `d` times from `pair k m`, and read off the level after `d`
steps and the resulting mask. -/
theorem myUpsampleJointStep_iter_level (k m d : ℕ) :
    (myUpsampleJointStep^[d] (Nat.pair k m)).unpair.1 = k + d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply', myUpsampleJointStep_eq, unpair_pair_fst, ih]
    omega

theorem myUpsampleJointStep_iter_levelSet (k m d : ℕ) :
    levelSet (k + d) ((myUpsampleJointStep^[d] (Nat.pair k m)).unpair.2) = levelSet k m := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply', myUpsampleJointStep_eq, unpair_pair_snd,
      myUpsampleJointStep_iter_level, show k + (d + 1) = (k + d) + 1 from by omega,
      levelSet_myUpsampleStep, ih]

/-- `levelSet k (myModPow2 x (2^k)) = levelSet k x`: truncating a mask to its meaningful low
`2^k` bits never changes the `levelSet` it presents (`levelSet k _` only ever reads bit positions
`< 2^k`). Used to keep `myUpsample`'s output *bounded* (`myUpsample_lt`) even when no genuine
upsampling step occurs (`k = k'`), which the raw iteration alone would not guarantee. -/
theorem levelSet_myModPow2 (k x : ℕ) : levelSet k (myModPow2 x (2 ^ k)) = levelSet k x := by
  ext n
  simp only [mem_levelSet, myModPow2_eq, Nat.testBit_mod_two_pow]
  have : n % 2 ^ k < 2 ^ k := Nat.mod_lt n (Nat.two_pow_pos k)
  simp [this]

/-- **`myUpsample k k' m`**: the computable re-expression of a level-`k` mask `m` at level
`k' ≥ k`, agreeing with `Exercise812.lean`'s (non-computable) `upsample` at the `levelSet` level
(`levelSet_myUpsample`), and always *bounded* (`myUpsample_lt`) — the final `myModPow2` truncation
is a no-op mathematically (`levelSet_myModPow2`) but is essential to guarantee boundedness in the
degenerate `k = k'` case, where the raw iteration runs zero steps and would otherwise return `m`
unchanged (junk bits included). Undefined behaviour (returns junk) when `k' < k`. -/
def myUpsample (k k' m : ℕ) : ℕ :=
  myModPow2 ((myUpsampleJointStep^[k' - k] (Nat.pair k m)).unpair.2) (2 ^ k')

theorem primrec_myUpsample :
    Nat.Primrec (fun t => myUpsample t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) := by
  have hstep : Nat.Primrec (fun w => myUpsampleJointStep w.unpair.2.unpair.2) :=
    primrec_myUpsampleJointStep.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hprec := Nat.Primrec.prec primrec_id hstep
  have hz : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 t.unpair.2.unpair.2) :=
    Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)
  have hn : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1 - t.unpair.1) :=
    primrec_sub₂ (Nat.Primrec.left.comp Nat.Primrec.right) Nat.Primrec.left
  have hmodpow : Nat.Primrec (fun t : ℕ => (2:ℕ) ^ t.unpair.2.unpair.1) :=
    primrec_two_pow (Nat.Primrec.left.comp Nat.Primrec.right)
  refine (primrec_myModPow2.comp ((Nat.Primrec.right.comp (hprec.comp (hz.pair hn))).pair
    hmodpow)).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  unfold myUpsample
  rw [rec_const_iterate]

/-- **`myUpsample` realizes `upsample` at the `levelSet` level.** -/
theorem levelSet_myUpsample {k k' : ℕ} (hk : k ≤ k') (m : ℕ) :
    levelSet k' (myUpsample k k' m) = levelSet k m := by
  unfold myUpsample
  rw [levelSet_myModPow2]
  have := myUpsampleJointStep_iter_levelSet k m (k' - k)
  rwa [show k + (k' - k) = k' from by omega] at this

/-- **`myUpsample` is always bounded** by `2 ^ (2 ^ k')`, regardless of whether a genuine
upsampling step occurs. -/
theorem myUpsample_lt (k k' m : ℕ) : myUpsample k k' m < 2 ^ (2 ^ k') := myModPow2_lt _ _

/-! ### Non-emptiness of `levelSet k m` is recursively decidable

`levelSet_nonempty_iff` phrases `(levelSet k m).Nonempty` as a bounded `∃ ℓ < 2 ^ k, m.testBit ℓ`;
this is exactly what the existing `bExistsFn` combinator (`Recursive.lean`) decides, with
`myTestBit` supplying the (already primitive-recursive) body. -/

/-- The `bExistsFn` body `pair ℓ m ↦ myTestBit m ℓ`. -/
def levelSetNonemptyBody (t : ℕ) : ℕ := myTestBit t.unpair.2 t.unpair.1

theorem primrec_levelSetNonemptyBody : Nat.Primrec levelSetNonemptyBody :=
  (primrec_myTestBit.comp (Nat.Primrec.right.pair Nat.Primrec.left)).of_eq fun t => by
    simp only [levelSetNonemptyBody, unpair_pair_fst, unpair_pair_snd]

/-- **`myLevelSetNonempty k m ∈ {0,1}`** decides `(levelSet k m).Nonempty`
(`myLevelSetNonempty_eq_one_iff`). -/
def myLevelSetNonempty (k m : ℕ) : ℕ := bExistsFn levelSetNonemptyBody m (2 ^ k)

theorem primrec_myLevelSetNonempty :
    Nat.Primrec (fun t => myLevelSetNonempty t.unpair.1 t.unpair.2) := by
  have hbe : Nat.Primrec (fun t : ℕ => bExistsFn levelSetNonemptyBody t.unpair.1 t.unpair.2) :=
    primrec_bExistsFn primrec_levelSetNonemptyBody
  have hpow : Nat.Primrec (fun t : ℕ => (2:ℕ) ^ t.unpair.1) := primrec_two_pow Nat.Primrec.left
  exact (hbe.comp (Nat.Primrec.right.pair hpow)).of_eq fun t => by
    simp only [myLevelSetNonempty, unpair_pair_fst, unpair_pair_snd]

theorem myLevelSetNonempty_le_one (k m : ℕ) : myLevelSetNonempty k m ≤ 1 :=
  bExistsFn_le_one _ _ _

theorem myLevelSetNonempty_eq_one_iff (k m : ℕ) :
    myLevelSetNonempty k m = 1 ↔ (levelSet k m).Nonempty := by
  unfold myLevelSetNonempty
  rw [bExistsFn_eq_one_iff, levelSet_nonempty_iff]
  simp only [levelSetNonemptyBody, unpair_pair_fst, unpair_pair_snd, myTestBit_eq_one_iff]

/-! ### `levelSet k _` is injective on bounded masks

Needed to decide *equality* of two `levelSet`s from their bitmask codes: two bounded masks
(`< 2 ^ (2 ^ k)`, i.e. with no "junk" bits at positions `≥ 2^k`) presenting the same `levelSet k _`
must already be the same natural number. Combined with `myUpsample_lt` (which guarantees
boundedness unconditionally), this reduces `levelSet`-equality-after-upsampling to plain `ℕ`
equality of the upsampled codes. -/

theorem levelSet_inj_of_lt {k a b : ℕ} (ha : a < 2 ^ (2 ^ k)) (hb : b < 2 ^ (2 ^ k))
    (h : levelSet k a = levelSet k b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro ℓ
  by_cases hℓ : ℓ < 2 ^ k
  · have hiff := Set.ext_iff.mp h ℓ
    simp only [mem_levelSet, Nat.mod_eq_of_lt hℓ] at hiff
    cases ha' : a.testBit ℓ <;> cases hb' : b.testBit ℓ <;> simp_all
  · have hpow : (2:ℕ) ^ (2 ^ k) ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hℓ)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hpow),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hpow)]

/-! ### Canonicalizing an arbitrary `(level, mask)` code

Mirrors `UComputablePresentation.lean`'s `canonCode`, but simpler: a `(k, m)` pair is always a
syntactically well-formed `levelSet` presentation, only possibly *empty* — no "clip to `[0,1)`"
pass is needed, just the non-emptiness check `myLevelSetNonempty` already built. -/

/-- Keep a code `c = pair k m` unchanged when `levelSet k m` is non-empty; otherwise fall back to
the fixed master code `pair 0 1` (`levelSet 0 1 = univ`, `levelSet_zero_one`). -/
def canonIdx (c : ℕ) : ℕ :=
  selectFn (myLevelSetNonempty c.unpair.1 c.unpair.2) c (Nat.pair 0 1)

theorem primrec_canonIdx : Nat.Primrec canonIdx := by
  have hne : Nat.Primrec (fun c => myLevelSetNonempty c.unpair.1 c.unpair.2) :=
    primrec_myLevelSetNonempty
  exact (primrec_selectFn hne primrec_id (Nat.Primrec.const (Nat.pair 0 1))).of_eq fun _ => rfl

theorem canonIdx_eq_self_of_nonempty {c : ℕ} (h : (levelSet c.unpair.1 c.unpair.2).Nonempty) :
    canonIdx c = c := by
  unfold canonIdx
  rw [(myLevelSetNonempty_eq_one_iff _ _).mpr h, selectFn_one]

theorem canonIdx_eq_master_of_empty {c : ℕ} (h : levelSet c.unpair.1 c.unpair.2 = ∅) :
    canonIdx c = Nat.pair 0 1 := by
  unfold canonIdx
  have hle := myLevelSetNonempty_le_one c.unpair.1 c.unpair.2
  have hne1 : myLevelSetNonempty c.unpair.1 c.unpair.2 ≠ 1 := fun heq =>
    ((myLevelSetNonempty_eq_one_iff _ _).mp heq).ne_empty h
  have h0 : myLevelSetNonempty c.unpair.1 c.unpair.2 = 0 := by omega
  rw [h0, selectFn_zero]

/-- `canonIdx` always lands on a code presenting a non-empty `levelSet`. -/
theorem levelSet_canonIdx_nonempty (c : ℕ) :
    (levelSet (canonIdx c).unpair.1 (canonIdx c).unpair.2).Nonempty := by
  by_cases h : (levelSet c.unpair.1 c.unpair.2).Nonempty
  · rwa [canonIdx_eq_self_of_nonempty h]
  · rw [canonIdx_eq_master_of_empty (Set.not_nonempty_iff_eq_empty.mp h), unpair_pair_fst,
      unpair_pair_snd, levelSet_zero_one]
    exact Set.univ_nonempty

/-- `canonIdx` is idempotent (a fixed point once applied). -/
theorem canonIdx_idempotent (c : ℕ) : canonIdx (canonIdx c) = canonIdx c :=
  canonIdx_eq_self_of_nonempty (levelSet_canonIdx_nonempty c)

/-! ### `V`'s enumeration `VX` -/

/-- **`V`'s enumeration**: canonicalize the `(level, mask)` pair coded by `n`. -/
def VX (c : ℕ) : Set ℕ := levelSet (canonIdx c).unpair.1 (canonIdx c).unpair.2

/-- `VX` factors through `canonIdx` (canonicalizing twice changes nothing). -/
theorem VX_canonIdx (c : ℕ) : VX (canonIdx c) = VX c := by unfold VX; rw [canonIdx_idempotent]

/-- Every `VX n` is a genuine `V`-neighbourhood. -/
theorem V_mem_VX (c : ℕ) : V.mem (VX c) :=
  ⟨(canonIdx c).unpair.1, (canonIdx c).unpair.2, rfl, levelSet_canonIdx_nonempty c⟩

theorem VX_nonempty (c : ℕ) : (VX c).Nonempty := levelSet_canonIdx_nonempty c

/-- `VX` is onto `V`'s neighbourhoods: every `V`-neighbourhood is already `levelSet k m` for some
non-empty pair `(k, m)`, on which `canonIdx` is a no-op. -/
theorem V_surj_VX : ∀ {Y : Set ℕ}, V.mem Y → ∃ n, VX n = Y := by
  rintro Y ⟨k, m, rfl, hne⟩
  refine ⟨Nat.pair k m, ?_⟩
  have hne' : (levelSet (Nat.pair k m).unpair.1 (Nat.pair k m).unpair.2).Nonempty := by
    rwa [unpair_pair_fst, unpair_pair_snd]
  unfold VX
  rw [canonIdx_eq_self_of_nonempty hne', unpair_pair_fst, unpair_pair_snd]

/-! ### Scott's two relations for `V`

`levelSet_inter` (`Exercise812.lean`) says the *raw* intersection of two `levelSet`s is again a
`levelSet`, unconditionally — mirroring `Example78.lean`'s `PN` rather than `Definition87.lean`'s
`U`. We re-derive it computably: bridge `levelSet_inter_same_level`'s same-level `&&&`-formula
through `myUpsample`/`myLand`. -/

/-- **Computable version of `levelSet_inter`.** -/
theorem levelSet_myInter (k1 m1 k2 m2 : ℕ) :
    levelSet k1 m1 ∩ levelSet k2 m2
      = levelSet (max k1 k2) (myLand (myUpsample k1 (max k1 k2) m1) (myUpsample k2 (max k1 k2) m2)) := by
  conv_lhs => rw [← levelSet_myUpsample (Nat.le_max_left k1 k2) m1,
    ← levelSet_myUpsample (Nat.le_max_right k1 k2) m2]
  rw [levelSet_inter_same_level, myLand_eq_land]

/-- **`levelSet` equality reduces to `myUpsample` equality** at the common level `max k₁ k₂`: this
is the injectivity criterion (`levelSet_inj_of_lt`) driving Scott's relation 7.1(i) decider. -/
theorem levelSet_eq_iff_myUpsample_eq (k1 m1 k2 m2 : ℕ) :
    levelSet k1 m1 = levelSet k2 m2 ↔
      myUpsample k1 (max k1 k2) m1 = myUpsample k2 (max k1 k2) m2 := by
  constructor
  · intro h
    exact levelSet_inj_of_lt (myUpsample_lt _ _ _) (myUpsample_lt _ _ _)
      (by rw [levelSet_myUpsample (Nat.le_max_left k1 k2),
        levelSet_myUpsample (Nat.le_max_right k1 k2), h])
  · intro h
    rw [← levelSet_myUpsample (Nat.le_max_left k1 k2) m1,
      ← levelSet_myUpsample (Nat.le_max_right k1 k2) m2, h]

/-- The **raw** `(level, mask)` code for `VX n ∩ VX m`, before re-canonicalization: upsample both
`canonIdx`-normalized masks to the common level `max k₁ k₂` and take `myLand`. -/
def VinterRaw (n m : ℕ) : ℕ :=
  Nat.pair (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
    (myLand
      (myUpsample (canonIdx n).unpair.1 (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
        (canonIdx n).unpair.2)
      (myUpsample (canonIdx m).unpair.1 (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
        (canonIdx m).unpair.2))

theorem primrec_VinterRaw : Nat.Primrec (fun t => VinterRaw t.unpair.1 t.unpair.2) := by
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
  have hland : Nat.Primrec (fun t : ℕ => myLand
      (myUpsample (canonIdx t.unpair.1).unpair.1
        (max (canonIdx t.unpair.1).unpair.1 (canonIdx t.unpair.2).unpair.1) (canonIdx t.unpair.1).unpair.2)
      (myUpsample (canonIdx t.unpair.2).unpair.1
        (max (canonIdx t.unpair.1).unpair.1 (canonIdx t.unpair.2).unpair.1) (canonIdx t.unpair.2).unpair.2)) :=
    (primrec_myLand.comp (hup1.pair hup2)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (hkJ.pair hland).of_eq fun _ => rfl

/-- **`VinterRaw` realizes `VX n ∩ VX m`** at the `levelSet` level (unconditionally — `V`'s
consistency is genuinely automatic, mirroring `PN`). -/
theorem levelSet_VinterRaw (n m : ℕ) :
    levelSet (VinterRaw n m).unpair.1 (VinterRaw n m).unpair.2 = VX n ∩ VX m := by
  unfold VinterRaw
  rw [unpair_pair_fst, unpair_pair_snd]
  exact (levelSet_myInter (canonIdx n).unpair.1 (canonIdx n).unpair.2
    (canonIdx m).unpair.1 (canonIdx m).unpair.2).symm

/-- **Scott's consistency condition reduces to non-emptiness.** -/
theorem Vcons_iff_nonempty_inter (n m : ℕ) :
    (∃ k, VX k ⊆ VX n ∩ VX m) ↔ (VX n ∩ VX m).Nonempty := by
  constructor
  · rintro ⟨k, hk⟩
    exact (VX_nonempty k).mono hk
  · intro hne
    rw [← levelSet_VinterRaw] at hne
    have hVmem : V.mem (VX n ∩ VX m) := by
      rw [← levelSet_VinterRaw]
      exact ⟨(VinterRaw n m).unpair.1, (VinterRaw n m).unpair.2, rfl, hne⟩
    obtain ⟨k, hk⟩ := V_surj_VX hVmem
    exact ⟨k, by rw [hk]⟩

/-- **7.1(i) for `V`**: `Xₙ ∩ Xₘ = X_k` is recursively decidable, reduced to `myUpsample` equality
of the raw intersection code against `X_k`'s own code (`levelSet_eq_iff_myUpsample_eq`). -/
theorem V_interEq_computable : RecDecidable₃ (fun n m k => VX n ∩ VX m = VX k) := by
  unfold RecDecidable₃
  have hvr : Nat.Primrec (fun t : ℕ => VinterRaw t.unpair.1 t.unpair.2.unpair.1) :=
    (primrec_VinterRaw.comp (Nat.Primrec.left.pair
      (Nat.Primrec.left.comp Nat.Primrec.right))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hvrK : Nat.Primrec (fun t : ℕ => (VinterRaw t.unpair.1 t.unpair.2.unpair.1).unpair.1) :=
    Nat.Primrec.left.comp hvr
  have hvrM : Nat.Primrec (fun t : ℕ => (VinterRaw t.unpair.1 t.unpair.2.unpair.1).unpair.2) :=
    Nat.Primrec.right.comp hvr
  have hck : Nat.Primrec (fun t : ℕ => canonIdx t.unpair.2.unpair.2) :=
    primrec_canonIdx.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hckK : Nat.Primrec (fun t : ℕ => (canonIdx t.unpair.2.unpair.2).unpair.1) :=
    Nat.Primrec.left.comp hck
  have hckM : Nat.Primrec (fun t : ℕ => (canonIdx t.unpair.2.unpair.2).unpair.2) :=
    Nat.Primrec.right.comp hck
  have hkJ : Nat.Primrec (fun t : ℕ =>
      max (VinterRaw t.unpair.1 t.unpair.2.unpair.1).unpair.1 (canonIdx t.unpair.2.unpair.2).unpair.1) :=
    primrec_max hvrK hckK
  have hLHS : Nat.Primrec (fun t : ℕ => myUpsample (VinterRaw t.unpair.1 t.unpair.2.unpair.1).unpair.1
      (max (VinterRaw t.unpair.1 t.unpair.2.unpair.1).unpair.1 (canonIdx t.unpair.2.unpair.2).unpair.1)
      (VinterRaw t.unpair.1 t.unpair.2.unpair.1).unpair.2) :=
    (primrec_myUpsample.comp (hvrK.pair (hkJ.pair hvrM))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hRHS : Nat.Primrec (fun t : ℕ => myUpsample (canonIdx t.unpair.2.unpair.2).unpair.1
      (max (VinterRaw t.unpair.1 t.unpair.2.unpair.1).unpair.1 (canonIdx t.unpair.2.unpair.2).unpair.1)
      (canonIdx t.unpair.2.unpair.2).unpair.2) :=
    (primrec_myUpsample.comp (hckK.pair (hkJ.pair hckM))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  refine RecDecidable.of_iff (fun t => ?_) (RecDecidable.natEq hLHS hRHS)
  dsimp only
  rw [← levelSet_VinterRaw, ← levelSet_eq_iff_myUpsample_eq]
  rfl

/-- **7.1(ii) for `V`**: consistency `∃k. X_k ⊆ Xₙ ∩ Xₘ` is recursively decidable, via
`Vcons_iff_nonempty_inter` and `myLevelSetNonempty`. -/
theorem V_cons_computable : RecDecidable₂ (fun n m => ∃ k, VX k ⊆ VX n ∩ VX m) := by
  have hvr : Nat.Primrec (fun t : ℕ => VinterRaw t.unpair.1 t.unpair.2) := primrec_VinterRaw
  have hfprim : Nat.Primrec (fun t : ℕ => myLevelSetNonempty (VinterRaw t.unpair.1 t.unpair.2).unpair.1
      (VinterRaw t.unpair.1 t.unpair.2).unpair.2) :=
    (primrec_myLevelSetNonempty.comp ((Nat.Primrec.left.comp hvr).pair
      (Nat.Primrec.right.comp hvr))).of_eq fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  refine RecDecidable₂.of_paired_zero_one_char hfprim ?_ ?_
  · intro t
    dsimp only
    have := myLevelSetNonempty_le_one (VinterRaw t.unpair.1 t.unpair.2).unpair.1
      (VinterRaw t.unpair.1 t.unpair.2).unpair.2
    omega
  · intro n m
    dsimp only
    rw [unpair_pair_fst, unpair_pair_snd, Vcons_iff_nonempty_inter, ← levelSet_VinterRaw,
      myLevelSetNonempty_eq_one_iff]

/-- The intersection index: `canonIdx` of the raw intersection code `VinterRaw`. -/
def Vinter (n m : ℕ) : ℕ := canonIdx (VinterRaw n m)

theorem primrec_Vinter : Nat.Primrec (fun t => Vinter t.unpair.1 t.unpair.2) :=
  (primrec_canonIdx.comp primrec_VinterRaw).of_eq fun _ => rfl

theorem Vinter_spec {n m : ℕ} (h : ∃ k, VX k ⊆ VX n ∩ VX m) : VX (Vinter n m) = VX n ∩ VX m := by
  have hne : (levelSet (VinterRaw n m).unpair.1 (VinterRaw n m).unpair.2).Nonempty := by
    rw [levelSet_VinterRaw]; exact (Vcons_iff_nonempty_inter n m).mp h
  unfold Vinter
  rw [VX_canonIdx]
  show levelSet (canonIdx (VinterRaw n m)).unpair.1 (canonIdx (VinterRaw n m)).unpair.2 = VX n ∩ VX m
  rw [canonIdx_eq_self_of_nonempty hne, levelSet_VinterRaw]

/-- A fixed index of `V.master = Set.univ`. -/
def VmasterIdx : ℕ := Nat.pair 0 1

theorem VX_VmasterIdx : VX VmasterIdx = V.master := by
  have hne : (levelSet (Nat.pair 0 1 : ℕ).unpair.1 (Nat.pair 0 1 : ℕ).unpair.2).Nonempty := by
    rw [unpair_pair_fst, unpair_pair_snd, levelSet_zero_one]; exact Set.univ_nonempty
  unfold VX VmasterIdx
  rw [canonIdx_eq_self_of_nonempty hne, unpair_pair_fst, unpair_pair_snd, levelSet_zero_one]
  rfl

/-- **Exercise 8.12(b).** `V` (Exercise 8.12(a)) has a genuine `ComputablePresentation`. -/
def VComputablePresentation : ComputablePresentation V where
  X := VX
  mem_X := V_mem_VX
  surj := V_surj_VX
  interEq_computable := V_interEq_computable
  cons_computable := V_cons_computable
  inter := Vinter
  inter_primrec := primrec_Vinter
  inter_spec := Vinter_spec
  masterIdx := VmasterIdx
  masterIdx_spec := VX_VmasterIdx

/-- **Exercise 8.12(b) (Scott 1981, PRG-19).** `V` is effectively given. -/
theorem V_isEffectivelyGiven : V.IsEffectivelyGiven := ⟨VComputablePresentation⟩

end Scott1980.Neighborhood

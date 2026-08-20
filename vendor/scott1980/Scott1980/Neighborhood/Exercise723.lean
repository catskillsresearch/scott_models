/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Example78
import Scott1980.Neighborhood.Theorem74
import Scott1980.Neighborhood.Theorem75
import Scott1980.Neighborhood.Exercise514

/-!
# Exercise 7.23 (Scott 1981, PRG-19, §7) — completing the discussion of `PN`

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII.

> **Exercise 7.23.** Complete the discussion of `PN` of Example 7.8. Show that the combinators
> `fun` and `graph` of Exercise 5.14 are computable. Also do the same for `λx,y. x∩y`,
> `λx,y. x∪y`, and `λx,y. x+y`, where for `x,y ∈ PN` we define `x+y = {n+m ∣ n∈x and m∈y}`.
> What are the computable elements of `PN`?

**The key structural fact.** Write `E n := ℕ \ Example78.nbhd n = {k ∣ n.testBit k}` for the finite
set Scott's `nbhd n` excludes. `Example78.nbhd n ⊆ Example78.nbhd k ↔ E k ⊆ E n` (containment of
neighbourhoods *reverses* into containment of the excluded finite sets — this is exactly
`ComputablePresentation.incl_computable`, already proven generically for any
`ComputablePresentation`, applied to `Example78.PNpres`). Every binary combinator `λx,y. h(x,y)`
this exercise asks about turns out to test a *containment of finite sets* `E k ⊆ h(E n, E m)`, which
is exactly `nbhd n ⊆ nbhd k` (and/or `nbhd m ⊆ nbhd k`) reindexed — so **`∩`/`∪` are computable
reusing `incl_computable` directly, with no new bitwise/primitive-recursive machinery**: `∩` is the
conjunction of two containments (`Eₖ⊆Eₙ∩Eₘ ↔ Eₖ⊆Eₙ ∧ Eₖ⊆Eₘ`), and `∪` reduces to a single
containment against `myLor n m` (`Eₖ⊆Eₙ∪Eₘ ↔ Eₖ⊆E_{myLor n m} ↔ nbhd(myLor n m) ⊆ nbhd k`).
-/

namespace Scott1980.Neighborhood.Exercise723

open Scott1980.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open Scott1980.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open Scott1980.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

/-! ## `nbhd`-containment reverses into excluded-set containment -/

/-- **The reversal fact.** `nbhd n ⊆ nbhd k ↔ myLor n k = n`: `nbhd n ⊆ nbhd k` iff
`nbhd n ∩ nbhd k = nbhd n` iff (by `nbhd_inter` + injectivity) `nbhd (myLor n k) = nbhd n`. -/
theorem nbhd_subset_iff_myLor_eq (n k : ℕ) : nbhd n ⊆ nbhd k ↔ myLor n k = n := by
  constructor
  · intro h
    apply nbhd_injective
    rw [← nbhd_inter]
    exact (Set.inter_eq_left.mpr h)
  · intro h
    rw [← h, ← nbhd_inter]
    exact Set.inter_subset_right

/-! ## `λx,y. x∩y` -/

/-- **`λx,y. x∩y` as an approximable map** `PN × PN → PN`. On neighbourhoods: `X ∪ Y` relates to
`Z` iff `X ⊆ Z` and `Y ⊆ Z` (the "test at the minimal witness" idiom: `X`, `Y` are themselves the
tightest possible arguments consistent with the input information). -/
def capMap : ApproximableMap (prod PN PN) PN where
  rel W Z := ∃ X Y, W = prodNbhd X Y ∧ PN.mem X ∧ PN.mem Y ∧ PN.mem Z ∧ X ⊆ Z ∧ Y ⊆ Z
  rel_dom := by rintro W Z ⟨X, Y, rfl, hX, hY, _, _, _⟩; exact prod_mem_prodNbhd hX hY
  rel_cod := by rintro W Z ⟨X, Y, rfl, _, _, hZ, _, _⟩; exact hZ
  master_rel := ⟨Set.univ, Set.univ, rfl, PN.master_mem, PN.master_mem, PN.master_mem,
    Set.subset_univ _, Set.subset_univ _⟩
  inter_right := by
    rintro W Z Z' ⟨X, Y, rfl, hX, hY, hZ, hXZ, hYZ⟩ ⟨X', Y', heq, _, _, hZ', hXZ', hYZ'⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    obtain ⟨k, hk⟩ := hZ; obtain ⟨k', hk'⟩ := hZ'; subst hk; subst hk'
    exact ⟨X, Y, rfl, hX, hY, ⟨myLor k k', nbhd_inter k k'⟩,
      Set.subset_inter hXZ hXZ', Set.subset_inter hYZ hYZ'⟩
  mono := by
    rintro W W' Z Z' ⟨X, Y, rfl, hX, hY, hZ, hXZ, hYZ⟩ hW'W hZZ' hW' hZ'
    obtain ⟨X', Y', hX', hY', rfl⟩ := hW'
    obtain ⟨hXX', hYY'⟩ := prodNbhd_subset_iff.mp hW'W
    exact ⟨X', Y', rfl, hX', hY', hZ', hXX'.trans (hXZ.trans hZZ'), hYY'.trans (hYZ.trans hZZ')⟩

/-- `capMap`'s neighbourhood relation on indices: `nbhd n ∪ nbhd m` relates to `nbhd k` iff both
`nbhd n ⊆ nbhd k` and `nbhd m ⊆ nbhd k`. -/
theorem capMap_rel_iff (n m k : ℕ) :
    capMap.rel (prodNbhd (nbhd n) (nbhd m)) (nbhd k) ↔ nbhd n ⊆ nbhd k ∧ nbhd m ⊆ nbhd k := by
  constructor
  · rintro ⟨X, Y, heq, _, _, _, hXZ, hYZ⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hXZ, hYZ⟩
  · rintro ⟨hXZ, hYZ⟩
    exact ⟨nbhd n, nbhd m, rfl, ⟨n, rfl⟩, ⟨m, rfl⟩, ⟨k, rfl⟩, hXZ, hYZ⟩

/-- **`λx,y. x∩y` is computable.** Reduces to `PNpres.incl_computable`, tested twice and
conjoined. -/
theorem capMap_isComputable :
    IsComputableMap (prodPresentation PNpres PNpres) PNpres capMap := by
  have hincl : RecDecidable (fun s => nbhd s.unpair.1 ⊆ nbhd s.unpair.2) := PNpres.incl_computable
  have hr0 : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.1 t.unpair.2) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair Nat.Primrec.right
  have hr1 : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.2 t.unpair.2) :=
    (Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) ((hincl.comp hr0).and (hincl.comp hr1))).re
  simp only [prodPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact capMap_rel_iff t.unpair.1.unpair.1 t.unpair.1.unpair.2 t.unpair.2

/-! ## Bit-level utilities: `Nat.testBit` is primitive recursively decidable

Needed for `λx,y.x+y` (Minkowski sum) and for `fun`/`graph`, both of which test membership of a
*bit position* `k` of the excluded set `E_k` against a target condition. -/

/-- **Every set bit lies below the number itself.** If `n.testBit i = true` then `i < n` (since
`n ≥ 2^i > i`). -/
theorem lt_of_testBit_true {n i : ℕ} (h : n.testBit i = true) : i < n := by
  by_contra hle
  have hle' : n ≤ i := by omega
  have hlt : n < 2 ^ i := lt_of_le_of_lt hle' Nat.lt_two_pow_self
  rw [Nat.testBit_eq_false_of_lt hlt] at h
  exact absurd h (by decide)

/-- Iterated halving `(·/2)^[k] n`, the primitive-recursive core of `Nat.testBit`. -/
def halfIter (n k : ℕ) : ℕ := (fun x : ℕ => x / 2)^[k] n

@[simp] theorem halfIter_zero (n : ℕ) : halfIter n 0 = n := rfl

theorem halfIter_succ (n k : ℕ) : halfIter n (k + 1) = halfIter (n / 2) k := by
  unfold halfIter; rw [Function.iterate_succ_apply]

theorem primrec_halfIter : Nat.Primrec (fun t => halfIter t.unpair.1 t.unpair.2) := by
  have hstep : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2 / 2) :=
    primrec_div2.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  refine (Nat.Primrec.prec primrec_id hstep).of_eq (fun t => ?_)
  simp only [Nat.unpaired, unpair_pair_snd]
  exact rec_const_iterate (fun x => x / 2) t.unpair.1 t.unpair.2

/-- The `{0,1}`-valued primitive-recursive proxy for `Nat.testBit`. -/
def bitAt (n k : ℕ) : ℕ := halfIter n k % 2

theorem primrec_bitAt : Nat.Primrec (fun t => bitAt t.unpair.1 t.unpair.2) :=
  primrec_mod2.comp primrec_halfIter

theorem bitAt_le_one (n k : ℕ) : bitAt n k ≤ 1 := by unfold bitAt; omega

/-- **Correctness of `bitAt`.** `bitAt n k = 1 ↔ n.testBit k = true`. -/
theorem bitAt_eq_one_iff (n k : ℕ) : bitAt n k = 1 ↔ n.testBit k = true := by
  induction k generalizing n with
  | zero =>
    show n % 2 = 1 ↔ n.testBit 0 = true
    rw [Nat.testBit_zero, decide_eq_true_iff]
  | succ k ih =>
    show halfIter n (k + 1) % 2 = 1 ↔ n.testBit (k + 1) = true
    rw [halfIter_succ, Nat.testBit_add_one]
    exact ih (n / 2)

/-! ## `λx,y. x∪y` -/

/-- **`λx,y. x∪y` as an approximable map** `PN × PN → PN`. On neighbourhoods: `X ∪ Y` relates to
`Z` iff `nbhd(myLor n m) ⊆ Z` — the excluded set of `Z` must fit inside the *union* `Eₙ ∪ Eₘ`, i.e.
`nbhd n ∩ nbhd m ⊆ Z` (`Eₙ ∪ Eₘ = E_{myLor n m}`, `nbhd_inter`). -/
def cupMap : ApproximableMap (prod PN PN) PN where
  rel W Z := ∃ X Y, W = prodNbhd X Y ∧ PN.mem X ∧ PN.mem Y ∧ PN.mem Z ∧ X ∩ Y ⊆ Z
  rel_dom := by rintro W Z ⟨X, Y, rfl, hX, hY, _, _⟩; exact prod_mem_prodNbhd hX hY
  rel_cod := by rintro W Z ⟨X, Y, rfl, _, _, hZ, _⟩; exact hZ
  master_rel := ⟨Set.univ, Set.univ, rfl, PN.master_mem, PN.master_mem, PN.master_mem,
    Set.inter_subset_left.trans (Set.subset_univ _)⟩
  inter_right := by
    rintro W Z Z' ⟨X, Y, rfl, hX, hY, hZ, hXYZ⟩ ⟨X', Y', heq, _, _, hZ', hXYZ'⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    obtain ⟨k, hk⟩ := hZ; obtain ⟨k', hk'⟩ := hZ'; subst hk; subst hk'
    exact ⟨X, Y, rfl, hX, hY, ⟨myLor k k', nbhd_inter k k'⟩, Set.subset_inter hXYZ hXYZ'⟩
  mono := by
    rintro W W' Z Z' ⟨X, Y, rfl, hX, hY, hZ, hXYZ⟩ hW'W hZZ' hW' hZ'
    obtain ⟨X', Y', hX', hY', rfl⟩ := hW'
    obtain ⟨hXX', hYY'⟩ := prodNbhd_subset_iff.mp hW'W
    exact ⟨X', Y', rfl, hX', hY', hZ',
      (Set.inter_subset_inter hXX' hYY').trans (hXYZ.trans hZZ')⟩

/-- `cupMap`'s neighbourhood relation on indices: `nbhd n ∪ nbhd m` relates to `nbhd k` iff
`nbhd (myLor n m) ⊆ nbhd k`. -/
theorem cupMap_rel_iff (n m k : ℕ) :
    cupMap.rel (prodNbhd (nbhd n) (nbhd m)) (nbhd k) ↔ nbhd (myLor n m) ⊆ nbhd k := by
  rw [← nbhd_inter n m]
  constructor
  · rintro ⟨X, Y, heq, _, _, _, hXYZ⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact hXYZ
  · intro h
    exact ⟨nbhd n, nbhd m, rfl, ⟨n, rfl⟩, ⟨m, rfl⟩, ⟨k, rfl⟩, h⟩

/-- **`λx,y. x∪y` is computable.** Reduces to `PNpres.incl_computable` against the primitive
recursive reindexing `myLor`. -/
theorem cupMap_isComputable :
    IsComputableMap (prodPresentation PNpres PNpres) PNpres cupMap := by
  have hincl : RecDecidable (fun s => nbhd s.unpair.1 ⊆ nbhd s.unpair.2) := PNpres.incl_computable
  have hlor : Nat.Primrec (fun t : ℕ => myLor t.unpair.1.unpair.1 t.unpair.1.unpair.2) :=
    (primrec_myLor.comp ((Nat.Primrec.left.comp Nat.Primrec.left).pair
      (Nat.Primrec.right.comp Nat.Primrec.left))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hr : Nat.Primrec (fun t => Nat.pair (myLor t.unpair.1.unpair.1 t.unpair.1.unpair.2)
      t.unpair.2) := hlor.pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  simp only [prodPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact cupMap_rel_iff t.unpair.1.unpair.1 t.unpair.1.unpair.2 t.unpair.2

/-! ## `λx,y. x+y` (Minkowski sum)

Scott's `x + y = {n + m ∣ n ∈ x, m ∈ y}`. Written on excluded sets, `Eₙ + Eₘ` (Minkowski sum of two
*finite* sets) is again finite, and — since `a + b` ranges over `Eₙ + Eₘ` exactly when `a` ranges
over `Eₙ` and `b` over `Eₘ` — `Eₙ + Eₘ = ⋃ {a + Eₘ ∣ a ∈ Eₙ}`, a union of shifted copies of `Eₘ`, one
per set bit of `n`. This is computed by `plusIdx`, an iterative bitwise-OR fold (mirroring `myLor`)
of `m <<< a` over the set bits `a` of `n`. -/

/-- Scott's `x + y = {n+m ∣ n ∈ x, m ∈ y}` (Minkowski sum) for `x, y ⊆ ℕ`. -/
def sumSet (X Y : Set ℕ) : Set ℕ := {k | ∃ a ∈ X, ∃ b ∈ Y, a + b = k}

@[inherit_doc] infixl:65 " +ˢ " => sumSet

theorem mem_sumSet {X Y : Set ℕ} {k : ℕ} : k ∈ X +ˢ Y ↔ ∃ a ∈ X, ∃ b ∈ Y, a + b = k := Iff.rfl

theorem sumSet_mono {X X' Y Y' : Set ℕ} (hX : X ⊆ X') (hY : Y ⊆ Y') : X +ˢ Y ⊆ X' +ˢ Y' := by
  rintro k ⟨a, ha, b, hb, rfl⟩
  exact ⟨a, hX ha, b, hY hb, rfl⟩

/-- **Choice-free antitone `compl`** (only the direction needed here): unlike the general
`Set.compl_subset_compl` (a `BooleanAlgebra` lemma whose `↔` proof is classical), this direction is
constructive contraposition and needs no excluded middle. -/
theorem compl_subset_compl_of_subset {X Y : Set ℕ} (h : X ⊆ Y) : Yᶜ ⊆ Xᶜ :=
  fun _ hx hxX => hx (h hxX)

/-- The excluded set of `nbhd n`, as a set of naturals: `(nbhd n)ᶜ = {k ∣ n.testBit k}`. -/
theorem compl_nbhd (n : ℕ) : (nbhd n)ᶜ = {k | n.testBit k = true} := by
  ext k; simp [nbhd]

/-- Pointwise form of `compl_nbhd`, convenient for `rw`/case-splitting on the (decidable) bit. -/
theorem mem_compl_nbhd {n x : ℕ} : x ∈ (nbhd n)ᶜ ↔ n.testBit x = true := by
  rw [compl_nbhd]; rfl

/-- **Choice-free De Morgan for `nbhd`'s excluded sets.** The general `Set.compl_inter` needs
excluded middle; here, since membership in `nbhd a`/`nbhd b` is decided by `Nat.testBit`, a case
split on the two (concrete) bits suffices. -/
theorem compl_inter_nbhd (a b : ℕ) : (nbhd a ∩ nbhd b)ᶜ = (nbhd a)ᶜ ∪ (nbhd b)ᶜ := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union, mem_nbhd]
  cases a.testBit x <;> cases b.testBit x <;> decide

/-- **Reference spec for `plusIdx`.** The running bitwise-OR of `m <<< a` over set bits `a < N` of
`n`, built by ordinary (non-primitive-recursive) structural recursion — used only to state and prove
correctness of the primitive-recursive `plusIdx` below. -/
def orUpTo (n m : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => myLor (orUpTo n m k) (selectFn (bitAt n k) (m <<< k) 0)

/-- **`orUpTo`'s bit-by-bit characterization.** Bit `k` of `orUpTo n m N` is set exactly when some
`a < N` is a set bit of `n` with `a ≤ k` and `k - a` a set bit of `m`. -/
theorem testBit_orUpTo (n m : ℕ) : ∀ N k,
    (orUpTo n m N).testBit k = true ↔ ∃ a, a < N ∧ n.testBit a = true ∧ a ≤ k ∧ m.testBit (k - a) = true
  | 0, k => by simp [orUpTo]
  | N + 1, k => by
    show (myLor (orUpTo n m N) (selectFn (bitAt n N) (m <<< N) 0)).testBit k = true ↔ _
    rw [myLor_eq_lor, Nat.testBit_lor, Bool.or_eq_true, testBit_orUpTo n m N]
    by_cases hbit : n.testBit N = true
    · rw [(bitAt_eq_one_iff n N).mpr hbit, selectFn_one, Nat.testBit_shiftLeft]
      constructor
      · rintro (⟨a, haN, ha, hak, hb⟩ | h)
        · exact ⟨a, Nat.lt_succ_of_lt haN, ha, hak, hb⟩
        · rw [Bool.and_eq_true, decide_eq_true_iff] at h
          exact ⟨N, Nat.lt_succ_self N, hbit, h.1, h.2⟩
      · rintro ⟨a, haN1, ha, hak, hb⟩
        rcases (show a < N ∨ a = N by omega) with haN | haN
        · exact Or.inl ⟨a, haN, ha, hak, hb⟩
        · subst haN
          exact Or.inr (by rw [Bool.and_eq_true, decide_eq_true_iff]; exact ⟨hak, hb⟩)
    · have hne1 : bitAt n N ≠ 1 := fun h => hbit ((bitAt_eq_one_iff n N).mp h)
      have hle := bitAt_le_one n N
      have hnbit : bitAt n N = 0 := by omega
      rw [hnbit, selectFn_zero]
      simp only [Nat.zero_testBit, Bool.false_eq_true, or_false]
      constructor
      · rintro ⟨a, haN, ha, hak, hb⟩; exact ⟨a, Nat.lt_succ_of_lt haN, ha, hak, hb⟩
      · rintro ⟨a, haN1, ha, hak, hb⟩
        rcases (show a < N ∨ a = N by omega) with haN | haN
        · exact ⟨a, haN, ha, hak, hb⟩
        · subst haN; exact absurd ha hbit

/-- **`orUpTo n m n` computes the Minkowski sum `Eₙ + Eₘ` exactly.** Every set bit `a` of `n`
satisfies `a < n` (`lt_of_testBit_true`), so ranging `a` over `N = n` sees every set bit of `n`. -/
theorem testBit_orUpTo_self (n m k : ℕ) :
    (orUpTo n m n).testBit k = true ↔ ∃ a, a ≤ k ∧ n.testBit a = true ∧ m.testBit (k - a) = true := by
  rw [testBit_orUpTo]
  constructor
  · rintro ⟨a, _, ha, hak, hb⟩; exact ⟨a, hak, ha, hb⟩
  · rintro ⟨a, hak, ha, hb⟩; exact ⟨a, lt_of_testBit_true ha, ha, hak, hb⟩

/-- **`plusIdx n m`: the primitive-recursive index of `Eₙ + Eₘ`.** -/
def plusIdx (n m : ℕ) : ℕ := orUpTo n m n

theorem plusIdx_testBit (n m k : ℕ) :
    (plusIdx n m).testBit k = true ↔ ∃ a, a ≤ k ∧ n.testBit a = true ∧ m.testBit (k - a) = true :=
  testBit_orUpTo_self n m k

/-- **`plusIdx`'s excluded set is the Minkowski sum `Eₙ + Eₘ`.** -/
theorem compl_nbhd_plusIdx (n m : ℕ) : (nbhd (plusIdx n m))ᶜ = (nbhd n)ᶜ +ˢ (nbhd m)ᶜ := by
  rw [compl_nbhd, compl_nbhd, compl_nbhd]
  ext k
  simp only [mem_sumSet, Set.mem_setOf_eq, plusIdx_testBit]
  constructor
  · rintro ⟨a, hak, ha, hb⟩; exact ⟨a, ha, k - a, hb, by omega⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, by omega, ha, by rw [Nat.add_sub_cancel_left]; exact hb⟩

/-- The primitive-recursive step function for `orUpTo`'s bitwise-OR fold: `(n, m, a, acc) ↦
(n, m, a+1, acc ||| (if testBit n a then m<<<a else 0))`. -/
def plusStep (s : ℕ) : ℕ :=
  Nat.pair (Nat.pair s.unpair.1.unpair.1 s.unpair.1.unpair.2)
    (Nat.pair (s.unpair.2.unpair.1 + 1)
      (myLor s.unpair.2.unpair.2
        (selectFn (bitAt s.unpair.1.unpair.1 s.unpair.2.unpair.1)
          (s.unpair.1.unpair.2 <<< s.unpair.2.unpair.1) 0)))

theorem primrec_plusStep : Nat.Primrec plusStep := by
  have hn : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have hm : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.left
  have ha : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hacc : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hbit : Nat.Primrec (fun s : ℕ => bitAt s.unpair.1.unpair.1 s.unpair.2.unpair.1) :=
    (primrec_bitAt.comp (hn.pair ha)).of_eq fun s => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hshift : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.2 <<< s.unpair.2.unpair.1) := by
    have := primrec_mul₂ hm (primrec_two_pow ha)
    exact this.of_eq fun s => by rw [Nat.shiftLeft_eq]
  have hsel := primrec_selectFn hbit hshift (Nat.Primrec.const 0)
  have hlor : Nat.Primrec (fun s : ℕ => myLor s.unpair.2.unpair.2
      (selectFn (bitAt s.unpair.1.unpair.1 s.unpair.2.unpair.1)
        (s.unpair.1.unpair.2 <<< s.unpair.2.unpair.1) 0)) :=
    (primrec_myLor.comp (hacc.pair hsel)).of_eq fun s => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact ((hn.pair hm).pair ((primrec_add₂ ha (Nat.Primrec.const 1)).pair hlor)).of_eq fun _ => rfl

theorem plusStep_unpair11 (s : ℕ) : (plusStep s).unpair.1.unpair.1 = s.unpair.1.unpair.1 := by
  unfold plusStep; rw [unpair_pair_fst, unpair_pair_fst]

theorem plusStep_unpair12 (s : ℕ) : (plusStep s).unpair.1.unpair.2 = s.unpair.1.unpair.2 := by
  unfold plusStep; rw [unpair_pair_fst, unpair_pair_snd]

theorem plusStep_unpair21 (s : ℕ) : (plusStep s).unpair.2.unpair.1 = s.unpair.2.unpair.1 + 1 := by
  unfold plusStep; rw [unpair_pair_snd, unpair_pair_fst]

theorem plusStep_unpair22 (s : ℕ) : (plusStep s).unpair.2.unpair.2 =
    myLor s.unpair.2.unpair.2 (selectFn (bitAt s.unpair.1.unpair.1 s.unpair.2.unpair.1)
      (s.unpair.1.unpair.2 <<< s.unpair.2.unpair.1) 0) := by
  unfold plusStep; rw [unpair_pair_snd, unpair_pair_snd]

theorem plusStep_iter_spec (n m : ℕ) (k : ℕ) :
    (plusStep^[k] (Nat.pair (Nat.pair n m) (Nat.pair 0 0))).unpair.1.unpair.1 = n ∧
    (plusStep^[k] (Nat.pair (Nat.pair n m) (Nat.pair 0 0))).unpair.1.unpair.2 = m ∧
    (plusStep^[k] (Nat.pair (Nat.pair n m) (Nat.pair 0 0))).unpair.2.unpair.1 = k ∧
    (plusStep^[k] (Nat.pair (Nat.pair n m) (Nat.pair 0 0))).unpair.2.unpair.2 = orUpTo n m k := by
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Function.iterate_zero, id_eq, unpair_pair_fst, unpair_pair_snd, orUpTo]
  | succ k ih =>
    obtain ⟨hn, hm, ha, hacc⟩ := ih
    rw [Function.iterate_succ_apply']
    set s := plusStep^[k] (Nat.pair (Nat.pair n m) (Nat.pair 0 0))
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [plusStep_unpair11, hn]
    · rw [plusStep_unpair12, hm]
    · rw [plusStep_unpair21, ha]
    · rw [plusStep_unpair22, hn, hm, ha, hacc]; rfl

theorem primrec_plusIdx : Nat.Primrec (fun t => plusIdx t.unpair.1 t.unpair.2) := by
  have hbase : Nat.Primrec
      (fun z => Nat.pair (Nat.pair z.unpair.1 z.unpair.2) (Nat.pair 0 0)) :=
    (Nat.Primrec.left.pair Nat.Primrec.right).pair
      ((Nat.Primrec.const 0).pair (Nat.Primrec.const 0))
  have hstep : Nat.Primrec (fun w => plusStep w.unpair.2.unpair.2) :=
    primrec_plusStep.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hprec := Nat.Primrec.prec hbase hstep
  refine ((Nat.Primrec.right.comp Nat.Primrec.right).comp
    (hprec.comp (primrec_id.pair Nat.Primrec.left))).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rw [rec_const_iterate]
  exact (plusStep_iter_spec t.unpair.1 t.unpair.2 t.unpair.1).2.2.2

/-- **`λx,y. x+y` as an approximable map** `PN × PN → PN`. On neighbourhoods: `X ∪ Y` relates to `Z`
iff `Zᶜ ⊆ Xᶜ +ˢ Yᶜ` — the excluded set of the output must fit inside the *Minkowski sum* of the
inputs' excluded sets, the most that is guaranteed knowing only `Eₙ ⊆ Sx` and `Eₘ ⊆ Sy`. -/
def plusMap : ApproximableMap (prod PN PN) PN where
  rel W Z := ∃ X Y, W = prodNbhd X Y ∧ PN.mem X ∧ PN.mem Y ∧ PN.mem Z ∧ Zᶜ ⊆ Xᶜ +ˢ Yᶜ
  rel_dom := by rintro W Z ⟨X, Y, rfl, hX, hY, _, _⟩; exact prod_mem_prodNbhd hX hY
  rel_cod := by rintro W Z ⟨X, Y, rfl, _, _, hZ, _⟩; exact hZ
  master_rel := ⟨Set.univ, Set.univ, rfl, PN.master_mem, PN.master_mem, PN.master_mem,
    fun x hx => absurd (Set.mem_univ x) hx⟩
  inter_right := by
    rintro W Z Z' ⟨X, Y, rfl, hX, hY, hZ, hsub⟩ ⟨X', Y', heq, _, _, hZ', hsub'⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    obtain ⟨k, hk⟩ := hZ; obtain ⟨k', hk'⟩ := hZ'; subst hk; subst hk'
    refine ⟨X, Y, rfl, hX, hY, ⟨myLor k k', nbhd_inter k k'⟩, ?_⟩
    rw [compl_inter_nbhd]
    exact Set.union_subset hsub hsub'
  mono := by
    rintro W W' Z Z' ⟨X, Y, rfl, hX, hY, hZ, hsub⟩ hW'W hZZ' hW' hZ'
    obtain ⟨X', Y', hX', hY', rfl⟩ := hW'
    obtain ⟨hXX', hYY'⟩ := prodNbhd_subset_iff.mp hW'W
    refine ⟨X', Y', rfl, hX', hY', hZ', ?_⟩
    calc Z'ᶜ ⊆ Zᶜ := compl_subset_compl_of_subset hZZ'
      _ ⊆ Xᶜ +ˢ Yᶜ := hsub
      _ ⊆ X'ᶜ +ˢ Y'ᶜ :=
        sumSet_mono (compl_subset_compl_of_subset hXX') (compl_subset_compl_of_subset hYY')

/-- **Choice-free converse of `compl_subset_compl_of_subset`, specialized to `nbhd`.** For cofinite
neighbourhoods the excluded sets have decidable membership (`Nat.testBit`), so unlike the general
`Set.compl_subset_compl` this direction needs only a case split on a `Bool`, not excluded middle. -/
theorem nbhd_subset_iff_compl_subset_compl (a b : ℕ) :
    nbhd a ⊆ nbhd b ↔ (nbhd b)ᶜ ⊆ (nbhd a)ᶜ := by
  constructor
  · exact compl_subset_compl_of_subset
  · intro h x hxa
    rw [mem_nbhd] at hxa ⊢
    cases hbit : b.testBit x with
    | false => rfl
    | true => exact absurd (mem_compl_nbhd.mp (h (mem_compl_nbhd.mpr hbit))) (by rw [hxa]; decide)

/-- `plusMap`'s neighbourhood relation on indices: `nbhd n ∪ nbhd m` relates to `nbhd k` iff
`nbhd (plusIdx n m) ⊆ nbhd k`. -/
theorem plusMap_rel_iff (n m k : ℕ) :
    plusMap.rel (prodNbhd (nbhd n) (nbhd m)) (nbhd k) ↔ nbhd (plusIdx n m) ⊆ nbhd k := by
  rw [nbhd_subset_iff_compl_subset_compl, compl_nbhd_plusIdx]
  constructor
  · rintro ⟨X, Y, heq, _, _, _, hsub⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact hsub
  · intro h
    exact ⟨nbhd n, nbhd m, rfl, ⟨n, rfl⟩, ⟨m, rfl⟩, ⟨k, rfl⟩, h⟩

/-- **`λx,y. x+y` is computable.** Reduces to `PNpres.incl_computable` against the primitive
recursive reindexing `plusIdx`. -/
theorem plusMap_isComputable :
    IsComputableMap (prodPresentation PNpres PNpres) PNpres plusMap := by
  have hincl : RecDecidable (fun s => nbhd s.unpair.1 ⊆ nbhd s.unpair.2) := PNpres.incl_computable
  have hpair : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1.unpair.1 t.unpair.1.unpair.2) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.left)
  have hplus : Nat.Primrec (fun t : ℕ => plusIdx t.unpair.1.unpair.1 t.unpair.1.unpair.2) :=
    (primrec_plusIdx.comp hpair).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hr : Nat.Primrec (fun t => Nat.pair (plusIdx t.unpair.1.unpair.1 t.unpair.1.unpair.2)
      t.unpair.2) := hplus.pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  simp only [prodPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact plusMap_rel_iff t.unpair.1.unpair.1 t.unpair.1.unpair.2 t.unpair.2

/-! ## What are the computable elements of `PN`?

Every element `x` of `PN` is a downward-directed filter of the cofinite neighbourhoods `nbhd n`.
Write `elemSet x := ⋃ {Eₙ ∣ x.mem (nbhd n)}` for the (arbitrary) subset of `ℕ` it "positively
describes". Since `PN`'s neighbourhoods carry only *negative* information and any two are consistent
(`PN_consistent`), each single fact `x.mem (nbhd n)` is *generated* by finitely many of the positive
facts `k ∈ elemSet x` (`k ∈ Eₙ`) — combine their witnesses with `myLor` (`exists_combined_witness`) —
so `x.mem (nbhd n) ↔ Eₙ ⊆ elemSet x` (`nbhd_mem_iff_subset_elemSet`). This exhibits `PN` as
(isomorphic to) the classical powerset domain `(Set ℕ, ⊆)`, `x ↦ elemSet x`, and:

> **Theorem.** `x` is a computable element of `PN` iff `elemSet x` is a recursively enumerable
> subset of `ℕ` (`isComputableElement_iff_elemSet_re`).

I.e. **the computable elements of `PN` are exactly the recursively enumerable sets** — Scott's
headline fact about the powerset domain. -/

/-- The subset of `ℕ` "positively described" by a `PN`-element `x`: the union of the excluded finite
sets of every neighbourhood it contains. -/
def elemSet (x : PN.Element) : Set ℕ := {k | ∃ n, x.mem (nbhd n) ∧ n.testBit k = true}

@[simp] theorem mem_elemSet {x : PN.Element} {k : ℕ} :
    k ∈ elemSet x ↔ ∃ n, x.mem (nbhd n) ∧ n.testBit k = true := Iff.rfl

/-- **Finite covering (choice-free, structural induction on the witness list).** If every `k` in a
list `L` has *some* neighbourhood `nbhd m` of `x` with `m.testBit k`, a single `nbhd m₀ ∈ x` works for
all of `L` at once: combine the per-entry witnesses with `myLor` via `x.inter_mem`, one list entry at
a time. -/
theorem exists_combined_witness (x : PN.Element) :
    ∀ L : List ℕ, (∀ k ∈ L, ∃ m, x.mem (nbhd m) ∧ m.testBit k = true) →
      ∃ m₀, x.mem (nbhd m₀) ∧ ∀ k ∈ L, m₀.testBit k = true
  | [] => fun _ => ⟨0, nbhd_zero ▸ x.master_mem, by simp⟩
  | k :: L => by
    intro hL
    obtain ⟨mk, hmk, hbk⟩ := hL k List.mem_cons_self
    obtain ⟨m₀, hm₀, hall⟩ :=
      exists_combined_witness x L (fun j hj => hL j (List.mem_cons_of_mem k hj))
    refine ⟨myLor mk m₀, ?_, ?_⟩
    · rw [← nbhd_inter]; exact x.inter_mem hmk hm₀
    · intro j hj
      rw [myLor_eq_lor, Nat.testBit_lor, Bool.or_eq_true]
      rcases List.mem_cons.mp hj with rfl | hj
      · exact Or.inl hbk
      · exact Or.inr (hall j hj)

/-- The (non-primitive-recursive) list of set-bit positions of `n`: every set bit `k` of `n`
satisfies `k < n` (`lt_of_testBit_true`), so ranging over `List.range n` catches them all. Used only
to state/prove the pure covering fact `nbhd_mem_iff_subset_elemSet`; see `bitsCode` below for the
primitive-recursive analogue used in the computability direction. -/
def bitsList (n : ℕ) : List ℕ := (List.range n).filter (fun k => n.testBit k)

theorem mem_bitsList {n k : ℕ} : k ∈ bitsList n ↔ n.testBit k = true := by
  unfold bitsList
  rw [List.mem_filter, List.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨lt_of_testBit_true h, h⟩⟩

/-- **`x.mem (nbhd n) ↔ Eₙ ⊆ elemSet x`.** Neighbourhood-membership reduces to positive-information
containment: `n`'s excluded set must already be covered by `x`'s recorded information. -/
theorem nbhd_mem_iff_subset_elemSet (x : PN.Element) (n : ℕ) :
    x.mem (nbhd n) ↔ (nbhd n)ᶜ ⊆ elemSet x := by
  rw [compl_nbhd]
  constructor
  · intro hn k hk
    exact ⟨n, hn, hk⟩
  · intro hsub
    obtain ⟨m₀, hm₀, hall⟩ :=
      exists_combined_witness x (bitsList n) (fun k hk => hsub (mem_bitsList.mp hk))
    have hincl : nbhd m₀ ⊆ nbhd n := by
      intro k hk
      simp only [mem_nbhd] at hk ⊢
      cases hn2 : n.testBit k with
      | false => rfl
      | true =>
        have hcontra := hall k (mem_bitsList.mpr hn2)
        rw [hk] at hcontra
        exact absurd hcontra (by decide)
    exact x.up_mem hm₀ ⟨n, rfl⟩ hincl

/-- **`elemSet x` is r.e. when `x` is a computable element.** Direct: `k ∈ elemSet x ↔ ∃ n,
x.mem (nbhd n) ∧ n.testBit k`, an r.e. projection of the conjunction of an r.e. predicate and a
(`bitAt`-)decidable one. -/
theorem elemSet_re_of_isComputableElement {x : PN.Element} (hx : IsComputableElement PNpres x) :
    REPred (fun k => k ∈ elemSet x) := by
  have hx' : REPred (fun n => x.mem (nbhd n)) := hx
  have hbit : RecDecidable (fun t : ℕ => t.unpair.1.testBit t.unpair.2 = true) :=
    ⟨fun t => bitAt t.unpair.1 t.unpair.2, primrec_bitAt, fun t => (bitAt_eq_one_iff _ _).symm⟩
  have hand : REPred (fun t : ℕ => x.mem (nbhd t.unpair.1) ∧ t.unpair.1.testBit t.unpair.2 = true) :=
    (hx'.comp Nat.Primrec.left).and hbit.re
  refine REPred.of_iff (fun k => ?_) hand.proj
  simp only [mem_elemSet, unpair_pair_fst, unpair_pair_snd]

/-! ### `bitsCode`: a primitive-recursive coding of "the list of set bits below `N`"

Needed for the converse computability direction: to invoke the generic closure
`REPred.forall_mem_decodeList`, the bounded conjunction `∀ k ∈ Eₙ, k ∈ A` must be phrased over a
*coded* list (`decodeList`), built by primitive recursion — not the plain `List.filter` form
`bitsList` above (which lives in `List ℕ`, outside the `Nat.Primrec` universe). `bitsCode` mirrors the
`plusStep`/`plusIdx` iteration pattern: it walks `k = 0, …, N-1`, consing `k` onto the running coded
list (`Nat.pair k acc + 1`, matching `decodeList`'s own `c + 1 ↦ c.unpair.1 :: decodeList c.unpair.2`)
exactly when `n.testBit k`. -/

/-- `bitsCode n N` codes the list of `k < N` with `n.testBit k = true`. -/
def bitsCode : ℕ → ℕ → ℕ
  | _, 0 => 0
  | n, N + 1 => selectFn (bitAt n N) (Nat.pair N (bitsCode n N) + 1) (bitsCode n N)

theorem mem_decodeList_bitsCode (n : ℕ) :
    ∀ N k, k ∈ decodeList (bitsCode n N) ↔ k < N ∧ n.testBit k = true
  | 0, k => by simp [bitsCode, decodeList_zero]
  | N + 1, k => by
    show k ∈ decodeList (selectFn (bitAt n N) (Nat.pair N (bitsCode n N) + 1) (bitsCode n N)) ↔ _
    by_cases hbit : n.testBit N = true
    · rw [(bitAt_eq_one_iff n N).mpr hbit, selectFn_one, decodeList_succ, unpair_pair_fst,
        unpair_pair_snd, List.mem_cons, mem_decodeList_bitsCode n N k]
      constructor
      · rintro (rfl | ⟨hkN, hk⟩)
        · exact ⟨by omega, hbit⟩
        · exact ⟨by omega, hk⟩
      · rintro ⟨hkN1, hk⟩
        rcases (show k < N ∨ k = N by omega) with hkN | hkN
        · exact Or.inr ⟨hkN, hk⟩
        · exact Or.inl hkN
    · have hne1 : bitAt n N ≠ 1 := fun h => hbit ((bitAt_eq_one_iff n N).mp h)
      have hle := bitAt_le_one n N
      have hnbit : bitAt n N = 0 := by omega
      rw [hnbit, selectFn_zero, mem_decodeList_bitsCode n N k]
      constructor
      · rintro ⟨hkN, hk⟩
        exact ⟨Nat.lt_succ_of_lt hkN, hk⟩
      · rintro ⟨hkN1, hk⟩
        rcases (show k < N ∨ k = N by omega) with hkN | hkN
        · exact ⟨hkN, hk⟩
        · subst hkN; exact absurd hk hbit

/-- The primitive-recursive step function for `bitsCode`'s iteration: `(n, N, acc) ↦
(n, N+1, if n.testBit N then pair N acc + 1 else acc)`. -/
def bitsStep (s : ℕ) : ℕ :=
  Nat.pair s.unpair.1
    (Nat.pair (s.unpair.2.unpair.1 + 1)
      (selectFn (bitAt s.unpair.1 s.unpair.2.unpair.1)
        (Nat.pair s.unpair.2.unpair.1 s.unpair.2.unpair.2 + 1) s.unpair.2.unpair.2))

theorem primrec_bitsStep : Nat.Primrec bitsStep := by
  have hn : Nat.Primrec (fun s : ℕ => s.unpair.1) := Nat.Primrec.left
  have hN : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hacc : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hbit : Nat.Primrec (fun s : ℕ => bitAt s.unpair.1 s.unpair.2.unpair.1) :=
    (primrec_bitAt.comp (hn.pair hN)).of_eq fun s => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hcons : Nat.Primrec (fun s : ℕ => Nat.pair s.unpair.2.unpair.1 s.unpair.2.unpair.2 + 1) :=
    Nat.Primrec.succ.comp ((hN.pair hacc).of_eq fun _ => rfl)
  have hsel := primrec_selectFn hbit hcons hacc
  exact (hn.pair ((primrec_add₂ hN (Nat.Primrec.const 1)).pair hsel)).of_eq fun _ => rfl

theorem bitsStep_unpair11 (s : ℕ) : (bitsStep s).unpair.1 = s.unpair.1 := by
  unfold bitsStep; rw [unpair_pair_fst]

theorem bitsStep_unpair21 (s : ℕ) : (bitsStep s).unpair.2.unpair.1 = s.unpair.2.unpair.1 + 1 := by
  unfold bitsStep; rw [unpair_pair_snd, unpair_pair_fst]

theorem bitsStep_unpair22 (s : ℕ) : (bitsStep s).unpair.2.unpair.2 =
    selectFn (bitAt s.unpair.1 s.unpair.2.unpair.1)
      (Nat.pair s.unpair.2.unpair.1 s.unpair.2.unpair.2 + 1) s.unpair.2.unpair.2 := by
  unfold bitsStep; rw [unpair_pair_snd, unpair_pair_snd]

theorem bitsStep_iter_spec (n : ℕ) (k : ℕ) :
    (bitsStep^[k] (Nat.pair n (Nat.pair 0 0))).unpair.1 = n ∧
    (bitsStep^[k] (Nat.pair n (Nat.pair 0 0))).unpair.2.unpair.1 = k ∧
    (bitsStep^[k] (Nat.pair n (Nat.pair 0 0))).unpair.2.unpair.2 = bitsCode n k := by
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Function.iterate_zero, id_eq, unpair_pair_fst, unpair_pair_snd, bitsCode]
  | succ k ih =>
    obtain ⟨hn, hN, hacc⟩ := ih
    rw [Function.iterate_succ_apply']
    set s := bitsStep^[k] (Nat.pair n (Nat.pair 0 0))
    refine ⟨?_, ?_, ?_⟩
    · rw [bitsStep_unpair11, hn]
    · rw [bitsStep_unpair21, hN]
    · rw [bitsStep_unpair22, hn, hN, hacc]; rfl

theorem primrec_bitsCode : Nat.Primrec (fun t => bitsCode t.unpair.1 t.unpair.2) := by
  have hbase : Nat.Primrec (fun z : ℕ => Nat.pair z.unpair.1 (Nat.pair 0 0)) :=
    Nat.Primrec.left.pair ((Nat.Primrec.const 0).pair (Nat.Primrec.const 0))
  have hstep : Nat.Primrec (fun w : ℕ => bitsStep w.unpair.2.unpair.2) :=
    primrec_bitsStep.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hprec := Nat.Primrec.prec hbase hstep
  refine ((Nat.Primrec.right.comp Nat.Primrec.right).comp
    (hprec.comp (primrec_id.pair Nat.Primrec.right))).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rw [rec_const_iterate]
  exact (bitsStep_iter_spec t.unpair.1 t.unpair.2).2.2

/-- **`x` is a computable element when `elemSet x` is r.e.** The bounded conjunction `Eₙ ⊆ elemSet x`,
phrased over the coded list `bitsCode n n`, is r.e. by `REPred.forall_mem_decodeList`; by
`nbhd_mem_iff_subset_elemSet` this containment is exactly `x.mem (nbhd n)`. -/
theorem isComputableElement_of_elemSet_re {x : PN.Element} (hA : REPred (fun k => k ∈ elemSet x)) :
    IsComputableElement PNpres x := by
  have hforall : REPred (fun c => ∀ e ∈ decodeList c, e ∈ elemSet x) := hA.forall_mem_decodeList
  have hcode : Nat.Primrec (fun n : ℕ => bitsCode n n) :=
    (primrec_bitsCode.comp (primrec_id.pair primrec_id)).of_eq fun n => by
      simp only [unpair_pair_fst, unpair_pair_snd, id_eq]
  refine REPred.of_iff (fun n => ?_) (hforall.comp hcode)
  show x.mem (nbhd n) ↔ _
  rw [nbhd_mem_iff_subset_elemSet, compl_nbhd]
  constructor
  · intro hsub e he
    exact hsub ((mem_decodeList_bitsCode n n e).mp he).2
  · intro hall k hk
    exact hall k ((mem_decodeList_bitsCode n n k).mpr ⟨lt_of_testBit_true hk, hk⟩)

/-- **What are the computable elements of `PN`? — Exercise 7.23 (Scott 1981, PRG-19).** Exactly the
recursively enumerable subsets of `ℕ`, via the identification `x ↦ elemSet x` of `PN` with the
classical powerset domain `(Set ℕ, ⊆)`. -/
theorem isComputableElement_iff_elemSet_re (x : PN.Element) :
    IsComputableElement PNpres x ↔ REPred (fun k => k ∈ elemSet x) :=
  ⟨elemSet_re_of_isComputableElement, isComputableElement_of_elemSet_re⟩

/-! ## `fun` and `graph` (Exercise 5.14) are computable

The last piece of Exercise 7.23. `PN.Element ≃ Set ℕ` via `elemSet` (established above), matching
Exercise 5.14's classical powerset model `Pω = (Set ℕ, ⊆)`. We reuse Exercise 5.14's combinators
`tag`/`Fun`/`Graph` verbatim, transported to the neighbourhood level by the same "reversal" idiom as
`capMap`/`cupMap`/`plusMap`: a neighbourhood-level combinator tests `Zᶜ ⊆ h(Xᶜ, Yᶜ)` for the
appropriate finite-set operation `h`. For `fun` this `h` is literally `Fun` (Exercise 5.14); `funMap`
is then the `curry` of the resulting two-variable map `gMap : PN × PN → PN`, so its computability is
*free* from `Theorem75.curry_isComputable` once `gMap` is shown computable. `graph` needs its own
direct construction (it does not factor through `curry`/`eval`), built from the canonical witness list
`decodeList (bitsCode j j)` for the excluded set `Eⱼ` of a domain neighbourhood `nbhd j`. -/

/-! ### `num`/`tag` are primitive recursive -/

/-- `tri k = k(k+1)/2` is primitive recursive: `tri k * 2 = k(k+1)` is *exact* division by the
literal `2`, computed by `primrec_div2`. -/
theorem primrec_tri : Nat.Primrec tri :=
  (primrec_div2.comp (primrec_mul₂ primrec_id Nat.Primrec.succ)).of_eq fun _ => rfl

/-- `num n m = tri(n+m) + m` is primitive recursive. -/
theorem primrec_num : Nat.Primrec (fun t => num t.unpair.1 t.unpair.2) :=
  (primrec_add₂ (primrec_tri.comp (primrec_add₂ Nat.Primrec.left Nat.Primrec.right))
    Nat.Primrec.right).of_eq fun _ => rfl

/-- `foldCode`-shaped step for `tagCode`: `(acc, x) ↦ num (x+1) acc` (the `params` slot is unused). -/
def tagStep (w : ℕ) : ℕ := num (w.unpair.1 + 1) w.unpair.2.unpair.1

theorem primrec_tagStep : Nat.Primrec tagStep := by
  have h1 : Nat.Primrec (fun w : ℕ => w.unpair.1 + 1) :=
    primrec_add₂ Nat.Primrec.left (Nat.Primrec.const 1)
  have h2 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  exact (primrec_num.comp (h1.pair h2)).of_eq fun w => by
    simp only [unpair_pair_fst, unpair_pair_snd]
    rfl

/-- **`tag` reformulated as a left fold over the reversed list.** `tag`'s recursion is a `foldr`;
`List.foldl_reverse` bridges it to the `foldl`-shaped `foldCode`. -/
theorem tag_eq_foldr (ns : List ℕ) (m : ℕ) :
    tag ns m = ns.foldr (fun x y => num (x + 1) y) (num 0 m) := by
  induction ns with
  | nil => rfl
  | cons a ns ih => rw [tag_cons, ih]; rfl

theorem tag_eq_foldl_reverse (ns : List ℕ) (m : ℕ) :
    tag ns m = ns.reverse.foldl (fun acc a => num (a + 1) acc) (num 0 m) := by
  rw [List.foldl_reverse]; exact tag_eq_foldr ns m

/-- **`tagCode code m` codes `tag (decodeList code) m`.** Built via `appendCode 0 code` (which
reverses `decodeList code`) so that `foldCode`'s left fold computes `tag`'s right fold. -/
def tagCode (code m : ℕ) : ℕ := foldCode tagStep 0 (num 0 m) (appendCode 0 code)

theorem tagCode_spec (code m : ℕ) : tagCode code m = tag (decodeList code) m := by
  unfold tagCode
  rw [foldCode_eq']
  have hstep : (fun acc x => tagStep (Nat.pair x (Nat.pair acc 0)))
      = (fun acc x => num (x + 1) acc) := by
    funext acc x
    show tagStep (Nat.pair x (Nat.pair acc 0)) = num (x + 1) acc
    unfold tagStep
    simp only [unpair_pair_fst, unpair_pair_snd]
  rw [hstep, decodeList_appendCode, decodeList_zero, List.append_nil]
  exact (tag_eq_foldl_reverse (decodeList code) m).symm

theorem primrec_tagCode : Nat.Primrec (fun t => tagCode t.unpair.1 t.unpair.2) := by
  have hz : Nat.Primrec (fun t : ℕ => num 0 t.unpair.2) :=
    (primrec_num.comp ((Nat.Primrec.const 0).pair Nat.Primrec.right)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hc : Nat.Primrec (fun t : ℕ => appendCode 0 t.unpair.1) :=
    (primrec_appendCode.comp ((Nat.Primrec.const 0).pair Nat.Primrec.left)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_foldCode primrec_tagStep (Nat.Primrec.const 0) hz hc).of_eq fun _ => rfl

/-- **The canonical witness list for `Eⱼ = (nbhd j)ᶜ`.** `decodeList (bitsCode j j)` has exactly the
set bits of `j` as entries (order immaterial for `entries`, but fixed here for `tag`'s coding). -/
theorem mem_bitsCodeList {n k : ℕ} : k ∈ decodeList (bitsCode n n) ↔ n.testBit k = true := by
  rw [mem_decodeList_bitsCode]
  exact ⟨fun h => h.2, fun h => ⟨lt_of_testBit_true h, h⟩⟩

/-- `tagOfBits j m` codes `tag (decodeList (bitsCode j j)) m`, primitive recursive in `(j, m)`. -/
def tagOfBits (j m : ℕ) : ℕ := tagCode (bitsCode j j) m

theorem tagOfBits_spec (j m : ℕ) : tagOfBits j m = tag (decodeList (bitsCode j j)) m :=
  tagCode_spec (bitsCode j j) m

theorem primrec_tagOfBits : Nat.Primrec (fun t => tagOfBits t.unpair.1 t.unpair.2) := by
  have hj : Nat.Primrec (fun t : ℕ => bitsCode t.unpair.1 t.unpair.1) :=
    (primrec_bitsCode.comp (Nat.Primrec.left.pair Nat.Primrec.left)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_tagCode.comp (hj.pair Nat.Primrec.right)).of_eq fun t => by
    simp only [unpair_pair_fst, unpair_pair_snd]
    rfl

/-! ### `unnum` is primitive recursive

`gMap`'s computability needs to *decode* `tag`: given `c ∈ Eₙ`, recover the unique `(ns, m)` with
`tag ns m = c` (uniqueness is `tag_injective`). Decoding peels one `unnum` layer at a time; `unnum`
itself is `nextCell` iterated (Exercise 5.13), so we first make `unnum` primitive recursive by the
same iterate-a-step-function device as `halfIter`/`bitsCode`/`plusIdx`. -/

/-- Pair-coded version of `nextCell : ℕ × ℕ → ℕ × ℕ` (`(0, m) ↦ (m+1, 0)`, `(n+1, m) ↦ (n, m+1)`). -/
def nextCellStep (w : ℕ) : ℕ :=
  selectFn (isZero w.unpair.1) (Nat.pair (w.unpair.2 + 1) 0)
    (Nat.pair (w.unpair.1 - 1) (w.unpair.2 + 1))

theorem primrec_nextCellStep : Nat.Primrec nextCellStep := by
  have hn : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hm : Nat.Primrec (fun w : ℕ => w.unpair.2) := Nat.Primrec.right
  have hz : Nat.Primrec (fun w : ℕ => isZero w.unpair.1) := primrec_isZero.comp hn
  have ha : Nat.Primrec (fun w : ℕ => Nat.pair (w.unpair.2 + 1) 0) :=
    (primrec_add₂ hm (Nat.Primrec.const 1)).pair (Nat.Primrec.const 0)
  have hb : Nat.Primrec (fun w : ℕ => Nat.pair (w.unpair.1 - 1) (w.unpair.2 + 1)) :=
    (primrec_sub₂ hn (Nat.Primrec.const 1)).pair (primrec_add₂ hm (Nat.Primrec.const 1))
  exact (primrec_selectFn hz ha hb).of_eq fun _ => rfl

theorem nextCellStep_eq (n m : ℕ) :
    nextCellStep (Nat.pair n m) = Nat.pair (nextCell (n, m)).1 (nextCell (n, m)).2 := by
  unfold nextCellStep
  simp only [unpair_pair_fst, unpair_pair_snd]
  rcases n with _ | k
  · have hz : isZero 0 = 1 := by unfold isZero; omega
    rw [hz, selectFn_one]; rfl
  · have hz : isZero (k + 1) = 0 := by unfold isZero; omega
    rw [hz, selectFn_zero]; rfl

/-- `nextCellStep` iterated from `(0,0)`, coding `unnum v` as a single `Nat.pair`. -/
def unnumPair (v : ℕ) : ℕ := nextCellStep^[v] (Nat.pair 0 0)

theorem unnumPair_spec (v : ℕ) : unnumPair v = Nat.pair (unnum v).1 (unnum v).2 := by
  unfold unnumPair
  induction v with
  | zero => rfl
  | succ v ih => rw [Function.iterate_succ_apply', ih, nextCellStep_eq]; rfl

theorem primrec_unnumPair : Nat.Primrec unnumPair := by
  have hbase : Nat.Primrec (fun _ : ℕ => Nat.pair (0 : ℕ) 0) := Nat.Primrec.const (Nat.pair 0 0)
  have hstep : Nat.Primrec (fun w : ℕ => nextCellStep w.unpair.2.unpair.2) :=
    primrec_nextCellStep.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hprec := Nat.Primrec.prec hbase hstep
  refine (hprec.comp ((Nat.Primrec.const 0).pair primrec_id)).of_eq fun v => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  show Nat.rec (Nat.pair 0 0) (fun _ ih => nextCellStep ih) v = unnumPair v
  rw [rec_const_iterate]; rfl

/-- The first component of `unnum v`, primitive recursive. -/
def unnum1 (v : ℕ) : ℕ := (unnumPair v).unpair.1

/-- The second component of `unnum v`, primitive recursive. -/
def unnum2 (v : ℕ) : ℕ := (unnumPair v).unpair.2

theorem unnum1_spec (v : ℕ) : unnum1 v = (unnum v).1 := by
  unfold unnum1; rw [unnumPair_spec, unpair_pair_fst]

theorem unnum2_spec (v : ℕ) : unnum2 v = (unnum v).2 := by
  unfold unnum2; rw [unnumPair_spec, unpair_pair_snd]

theorem primrec_unnum1 : Nat.Primrec unnum1 := Nat.Primrec.left.comp primrec_unnumPair

theorem primrec_unnum2 : Nat.Primrec unnum2 := Nat.Primrec.right.comp primrec_unnumPair

/-! ### `untagRef`: the (non-primitive-recursive) structural inverse of `tag`

Reference decoder, by well-founded recursion peeling one `unnum` layer at a time (mirroring
`tag_surjective`'s existence proof, but now *computing* the witness); used only to state/prove
correctness of the primitive-recursive `untagList`/`untagVal` below. -/

/-- `untagRef c = (ns, m)` with `tag ns m = c` (`tag_untagRef`). -/
def untagRef (c : ℕ) : List ℕ × ℕ :=
  if _h : (unnum c).1 = 0 then ([], (unnum c).2)
  else
    have hlt : (unnum c).2 < c := by
      have heq : num (unnum c).1 (unnum c).2 = c := by
        have h := numP_unnum c
        simpa [numP] using h
      obtain ⟨k, hk⟩ : ∃ k, (unnum c).1 = k + 1 := ⟨(unnum c).1 - 1, by omega⟩
      rw [hk] at heq
      have hb := num_succ_left_gt k (unnum c).2
      omega
    (((unnum c).1 - 1) :: (untagRef (unnum c).2).1, (untagRef (unnum c).2).2)
termination_by c
decreasing_by all_goals exact hlt

theorem untagRef_zero_case {c : ℕ} (h : (unnum c).1 = 0) :
    untagRef c = ([], (unnum c).2) := by
  rw [untagRef]; simp [h]

theorem untagRef_succ_case {c k : ℕ} (h : (unnum c).1 = k + 1) :
    untagRef c = (k :: (untagRef (unnum c).2).1, (untagRef (unnum c).2).2) := by
  have h0 : ¬ (unnum c).1 = 0 := by omega
  rw [untagRef, dif_neg h0, h]
  have hsub : k + 1 - 1 = k := by omega
  rw [hsub]

/-- **`untagRef` is a genuine right-inverse of `tag`.** Strong induction on `c`, mirroring
`tag_surjective`. -/
theorem tag_untagRef (c : ℕ) : tag (untagRef c).1 (untagRef c).2 = c := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rcases hc : (unnum c).1 with a | k
    · rw [untagRef_zero_case hc]
      have heq := numP_unnum c
      simp only [numP, hc] at heq
      rw [tag_nil]
      exact heq
    · rw [untagRef_succ_case hc]
      have heq : num (k + 1) (unnum c).2 = c := by
        have h := numP_unnum c
        simpa [numP, hc] using h
      have hlt : (unnum c).2 < c := by
        have hb := num_succ_left_gt k (unnum c).2
        omega
      rw [tag_cons, ih (unnum c).2 hlt, heq]

/-- **`unnum`'s second component strictly decreases** when the first is a successor — the
decreasing measure for both `untagRef` (well-founded recursion) and `untagStep` (bounded
iteration) below. -/
theorem unnum_snd_lt_of_fst_succ {c k : ℕ} (h : (unnum c).1 = k + 1) : (unnum c).2 < c := by
  have heq : num (k + 1) (unnum c).2 = c := by
    have h' := numP_unnum c
    simpa [numP, h] using h'
  have hb := num_succ_left_gt k (unnum c).2
  omega

/-! ### `untagList`/`untagVal`: `untagRef`, made primitive recursive

Same "bounded iteration, no-op once done" device as `bitsCode`/`plusIdx`/`tagCode`: pack a state
`(code, done, revAcc, val)`; each step peels one `unnum` layer of `code` (consing onto `revAcc`,
coded via `appendStep`'s convention) until `unnum`'s first component is `0`, at which point `done`
is set and the state freezes. Since `code` strictly decreases every non-frozen step
(`unnum_snd_lt_of_fst_succ`), `c + 1` iterations always suffice to freeze starting from `code = c`. -/

/-- The state-transition step: no-op once `done`; otherwise peel one `unnum` layer. -/
def untagStep (w : ℕ) : ℕ :=
  selectFn w.unpair.2.unpair.1 w
    (selectFn (isZero (unnum1 w.unpair.1))
      (Nat.pair (unnum2 w.unpair.1)
        (Nat.pair 1 (Nat.pair w.unpair.2.unpair.2.unpair.1 (unnum2 w.unpair.1))))
      (Nat.pair (unnum2 w.unpair.1)
        (Nat.pair 0
          (Nat.pair (Nat.pair (unnum1 w.unpair.1 - 1) w.unpair.2.unpair.2.unpair.1 + 1)
            w.unpair.2.unpair.2.unpair.2))))

theorem primrec_untagStep : Nat.Primrec untagStep := by
  have hdone : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hrevAcc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hval : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have ha : Nat.Primrec (fun w : ℕ => unnum1 w.unpair.1) := primrec_unnum1.comp Nat.Primrec.left
  have hb : Nat.Primrec (fun w : ℕ => unnum2 w.unpair.1) := primrec_unnum2.comp Nat.Primrec.left
  have hz : Nat.Primrec (fun w : ℕ => isZero (unnum1 w.unpair.1)) := primrec_isZero.comp ha
  have hhalt : Nat.Primrec (fun w : ℕ => Nat.pair (unnum2 w.unpair.1)
      (Nat.pair 1 (Nat.pair w.unpair.2.unpair.2.unpair.1 (unnum2 w.unpair.1)))) :=
    hb.pair ((Nat.Primrec.const 1).pair (hrevAcc.pair hb))
  have hcont : Nat.Primrec (fun w : ℕ => Nat.pair (unnum2 w.unpair.1)
      (Nat.pair 0
        (Nat.pair (Nat.pair (unnum1 w.unpair.1 - 1) w.unpair.2.unpair.2.unpair.1 + 1)
          w.unpair.2.unpair.2.unpair.2))) :=
    hb.pair ((Nat.Primrec.const 0).pair
      ((Nat.Primrec.succ.comp ((primrec_sub₂ ha (Nat.Primrec.const 1)).pair hrevAcc)).pair hval))
  have hinner := primrec_selectFn hz hhalt hcont
  exact (primrec_selectFn hdone primrec_id hinner).of_eq fun _ => rfl

theorem untagStep_done {w : ℕ} (h : w.unpair.2.unpair.1 = 1) : untagStep w = w := by
  unfold untagStep; rw [h, selectFn_one]

theorem untagStep_of_done_iterate (w : ℕ) (h : w.unpair.2.unpair.1 = 1) :
    ∀ k, untagStep^[k] w = w
  | 0 => rfl
  | k + 1 => by rw [Function.iterate_succ_apply', untagStep_of_done_iterate w h k, untagStep_done h]

theorem untagStep_halt {w : ℕ} (hdone : w.unpair.2.unpair.1 = 0) (ha : unnum1 w.unpair.1 = 0) :
    untagStep w = Nat.pair (unnum2 w.unpair.1)
      (Nat.pair 1 (Nat.pair w.unpair.2.unpair.2.unpair.1 (unnum2 w.unpair.1))) := by
  unfold untagStep
  rw [hdone, selectFn_zero, ha]
  have : isZero 0 = 1 := by unfold isZero; omega
  rw [this, selectFn_one]

theorem untagStep_cont {w : ℕ} (hdone : w.unpair.2.unpair.1 = 0) {k : ℕ}
    (ha : unnum1 w.unpair.1 = k + 1) :
    untagStep w = Nat.pair (unnum2 w.unpair.1)
      (Nat.pair 0
        (Nat.pair (Nat.pair k w.unpair.2.unpair.2.unpair.1 + 1) w.unpair.2.unpair.2.unpair.2)) := by
  unfold untagStep
  rw [hdone, selectFn_zero, ha]
  have hz : isZero (k + 1) = 0 := by unfold isZero; omega
  have hsub : k + 1 - 1 = k := by omega
  rw [hz, selectFn_zero, hsub]

/-- **Main invariant.** Given enough fuel (`c ≤ fuel`), `fuel + 1` iterations of `untagStep` from a
fresh `code = c` state (arbitrary carried `r`, `v`) freeze with `revAcc` holding `(untagRef c).1`
consed onto `r` (i.e. `reverse (untagRef c).1 ++ decodeList r`, matching `appendCode`'s convention)
and `val` holding `(untagRef c).2`. -/
theorem untagStep_iter_spec : ∀ c, ∀ fuel r v : ℕ, c ≤ fuel →
    untagStep^[fuel + 1] (Nat.pair c (Nat.pair 0 (Nat.pair r v))) =
      Nat.pair (untagRef c).2 (Nat.pair 1
        (Nat.pair ((untagRef c).1.foldl (fun acc x => Nat.pair x acc + 1) r) (untagRef c).2)) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro fuel r v hfuel
    set w : ℕ := Nat.pair c (Nat.pair 0 (Nat.pair r v)) with hw
    have hw1 : w.unpair.1 = c := by rw [hw, unpair_pair_fst]
    have hw2 : w.unpair.2.unpair.1 = 0 := by rw [hw]; simp only [unpair_pair_snd, unpair_pair_fst]
    have hw3 : w.unpair.2.unpair.2.unpair.1 = r := by
      rw [hw]; simp only [unpair_pair_snd, unpair_pair_fst]
    have hw4 : w.unpair.2.unpair.2.unpair.2 = v := by
      rw [hw]; simp only [unpair_pair_snd]
    rw [Function.iterate_succ_apply]
    rcases hc : (unnum c).1 with _ | k
    · have ha0 : unnum1 w.unpair.1 = 0 := by rw [hw1, unnum1_spec, hc]
      have hstep : untagStep w = Nat.pair (unnum c).2 (Nat.pair 1 (Nat.pair r (unnum c).2)) := by
        rw [untagStep_halt hw2 ha0, hw1, hw3, unnum2_spec]
      rw [hstep]
      have hdone1 : (Nat.pair (unnum c).2
          (Nat.pair 1 (Nat.pair r (unnum c).2))).unpair.2.unpair.1 = 1 := by
        simp only [unpair_pair_snd, unpair_pair_fst]
      rw [untagStep_of_done_iterate _ hdone1, untagRef_zero_case hc, List.foldl_nil]
    · have hak : unnum1 w.unpair.1 = k + 1 := by rw [hw1, unnum1_spec, hc]
      set b : ℕ := (unnum c).2 with hbdef
      have hblt : b < c := unnum_snd_lt_of_fst_succ hc
      have hc1 : 1 ≤ c := by omega
      have hstep : untagStep w = Nat.pair b (Nat.pair 0 (Nat.pair (Nat.pair k r + 1) v)) := by
        rw [untagStep_cont hw2 hak, hw1, hw3, hw4, unnum2_spec]
      rw [hstep]
      rcases fuel with _ | fuel'
      · omega
      · have hble : b ≤ fuel' := by omega
        have hihb := ih b hblt fuel' (Nat.pair k r + 1) v hble
        rw [hihb]
        have href := untagRef_succ_case (c := c) (k := k) hc
        rw [← hbdef] at href
        rw [href, List.foldl_cons]

/-- `untagStep` iterated `c + 1` times from the fresh state `(c, 0, 0, 0)`. -/
def untagState (c : ℕ) : ℕ := untagStep^[c + 1] (Nat.pair c (Nat.pair 0 (Nat.pair 0 0)))

theorem untagState_spec (c : ℕ) :
    untagState c = Nat.pair (untagRef c).2
      (Nat.pair 1 (Nat.pair ((untagRef c).1.foldl (fun acc x => Nat.pair x acc + 1) 0)
        (untagRef c).2)) :=
  untagStep_iter_spec c c 0 0 (le_refl c)

theorem primrec_untagState : Nat.Primrec untagState := by
  have hbase : Nat.Primrec (fun c : ℕ => Nat.pair c (Nat.pair (0 : ℕ) (Nat.pair 0 0))) :=
    primrec_id.pair ((Nat.Primrec.const 0).pair ((Nat.Primrec.const 0).pair (Nat.Primrec.const 0)))
  have hstep : Nat.Primrec (fun w : ℕ => untagStep w.unpair.2.unpair.2) :=
    primrec_untagStep.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hprec := Nat.Primrec.prec hbase hstep
  refine (hprec.comp (primrec_id.pair Nat.Primrec.succ)).of_eq fun c => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rw [rec_const_iterate]
  unfold untagState
  rw [Function.iterate_succ_apply']

/-- **`untagList c`**: the (`appendCode`-reversed) code of `(untagRef c).1`, primitive recursive. -/
def untagList (c : ℕ) : ℕ := appendCode 0 (untagState c).unpair.2.unpair.2.unpair.1

/-- **`untagVal c`**: the value component of `untagRef c`, primitive recursive. -/
def untagVal (c : ℕ) : ℕ := (untagState c).unpair.2.unpair.2.unpair.2

theorem primrec_untagList : Nat.Primrec untagList :=
  primrec_appendCode.comp
    ((Nat.Primrec.const 0).pair
      (Nat.Primrec.left.comp (Nat.Primrec.right.comp (Nat.Primrec.right.comp primrec_untagState))))
    |>.of_eq fun c => by unfold untagList; simp only [unpair_pair_fst, unpair_pair_snd]

theorem primrec_untagVal : Nat.Primrec untagVal :=
  Nat.Primrec.right.comp (Nat.Primrec.right.comp (Nat.Primrec.right.comp primrec_untagState))

/-- **`decodeList (untagList c) = (untagRef c).1`.** The `appendCode`-reversal in `untagList`
undoes the reversal built up by `untagStep`'s accumulator. -/
theorem decodeList_untagList (c : ℕ) : decodeList (untagList c) = (untagRef c).1 := by
  unfold untagList
  rw [decodeList_appendCode, decodeList_zero, List.append_nil]
  have hspec := untagState_spec c
  have hrevAcc : (untagState c).unpair.2.unpair.2.unpair.1
      = (untagRef c).1.foldl (fun acc x => Nat.pair x acc + 1) 0 := by
    rw [hspec]; simp only [unpair_pair_snd, unpair_pair_fst]
  rw [hrevAcc]
  have hfold : ∀ l : List ℕ, ∀ r : ℕ,
      decodeList (l.foldl (fun acc x => Nat.pair x acc + 1) r) = l.reverse ++ decodeList r := by
    intro l
    induction l with
    | nil => intro r; simp
    | cons a l ih =>
      intro r
      rw [List.foldl_cons, ih, decodeList_succ, unpair_pair_fst, unpair_pair_snd,
        List.reverse_cons, List.append_assoc, List.singleton_append]
  rw [hfold (untagRef c).1 0, decodeList_zero, List.append_nil, List.reverse_reverse]

/-- **`untagVal c = (untagRef c).2`.** -/
theorem untagVal_spec (c : ℕ) : untagVal c = (untagRef c).2 := by
  unfold untagVal; rw [untagState_spec]; simp only [unpair_pair_snd]

/-- **`untagList`/`untagVal` genuinely decode `tag`.** -/
theorem tag_untagList_untagVal (c : ℕ) : tag (decodeList (untagList c)) (untagVal c) = c := by
  rw [decodeList_untagList, untagVal_spec]; exact tag_untagRef c

/-- **`λx,y. Fun x y` as an approximable map** `PN × PN → PN`, built by the same "reversal" idiom as
`plusMap`: `Zᶜ ⊆ Fun Xᶜ Yᶜ`. `funMap` (the actual `fun` combinator of Exercise 5.14, a map
`PN → (PN →⃗ PN)`) is `curry gMap` (`Theorem75.curry`). -/
def gMap : ApproximableMap (prod PN PN) PN where
  rel W Z := ∃ X Y, W = prodNbhd X Y ∧ PN.mem X ∧ PN.mem Y ∧ PN.mem Z ∧ Zᶜ ⊆ Fun Xᶜ Yᶜ
  rel_dom := by rintro W Z ⟨X, Y, rfl, hX, hY, _, _⟩; exact prod_mem_prodNbhd hX hY
  rel_cod := by rintro W Z ⟨X, Y, rfl, _, _, hZ, _⟩; exact hZ
  master_rel := ⟨Set.univ, Set.univ, rfl, PN.master_mem, PN.master_mem, PN.master_mem,
    fun x hx => absurd (Set.mem_univ x) hx⟩
  inter_right := by
    rintro W Z Z' ⟨X, Y, rfl, hX, hY, hZ, hsub⟩ ⟨X', Y', heq, _, _, hZ', hsub'⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    obtain ⟨k, hk⟩ := hZ; obtain ⟨k', hk'⟩ := hZ'; subst hk; subst hk'
    refine ⟨X, Y, rfl, hX, hY, ⟨myLor k k', nbhd_inter k k'⟩, ?_⟩
    rw [compl_inter_nbhd]
    exact Set.union_subset hsub hsub'
  mono := by
    rintro W W' Z Z' ⟨X, Y, rfl, hX, hY, hZ, hsub⟩ hW'W hZZ' hW' hZ'
    obtain ⟨X', Y', hX', hY', rfl⟩ := hW'
    obtain ⟨hXX', hYY'⟩ := prodNbhd_subset_iff.mp hW'W
    refine ⟨X', Y', rfl, hX', hY', hZ', ?_⟩
    calc Z'ᶜ ⊆ Zᶜ := compl_subset_compl_of_subset hZZ'
      _ ⊆ Fun Xᶜ Yᶜ := hsub
      _ ⊆ Fun X'ᶜ Y'ᶜ :=
        Fun_mono (compl_subset_compl_of_subset hXX') (compl_subset_compl_of_subset hYY')

/-- `gMap`'s neighbourhood relation on indices: `nbhd n ∪ nbhd m` relates to `nbhd k` iff
`nbhd k`'s excluded set fits inside `Fun (nbhd n)ᶜ (nbhd m)ᶜ`. -/
theorem gMap_rel_iff (n m k : ℕ) :
    gMap.rel (prodNbhd (nbhd n) (nbhd m)) (nbhd k) ↔ (nbhd k)ᶜ ⊆ Fun (nbhd n)ᶜ (nbhd m)ᶜ := by
  constructor
  · rintro ⟨X, Y, heq, _, _, _, hsub⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact hsub
  · intro h
    exact ⟨nbhd n, nbhd m, rfl, ⟨n, rfl⟩, ⟨m, rfl⟩, ⟨k, rfl⟩, h⟩

/-- **`Fun` membership, decoded.** `Fun`'s defining existential over lists reduces to a bounded
existential over the finite excluded set `Eₙ`: given `c ∈ Eₙ`, `tag`'s injectivity forces the
witness list `ns` to be *exactly* `decodeList (untagList c)`, so testing `(∀n∈ns, n∈Eₘ) ∧ tag ns j
∈ Eₙ` reduces to testing `c` itself against `untagVal`/`untagList`. -/
theorem mem_Fun_compl_nbhd_iff (n m j : ℕ) :
    j ∈ Fun (nbhd n)ᶜ (nbhd m)ᶜ ↔
      ∃ c ∈ decodeList (bitsCode n n), untagVal c = j ∧
        ∀ i ∈ decodeList (untagList c), i ∈ (nbhd m)ᶜ := by
  constructor
  · rintro ⟨ns, hns, htag⟩
    have hc : tag ns j ∈ decodeList (bitsCode n n) := by
      rw [mem_bitsCodeList]; exact mem_compl_nbhd.mp htag
    refine ⟨tag ns j, hc, ?_, ?_⟩
    · exact (tag_injective (tag_untagList_untagVal (tag ns j))).2
    · rw [(tag_injective (tag_untagList_untagVal (tag ns j))).1]
      exact hns
  · rintro ⟨c, hc, hval, hall⟩
    refine ⟨decodeList (untagList c), hall, ?_⟩
    rw [mem_compl_nbhd, ← hval, tag_untagList_untagVal]
    exact mem_bitsCodeList.mp hc

/-- **Bounded-quantifier reformulation** of `mem_Fun_compl_nbhd_iff`, avoiding `decodeList`/
`bitsCode` for the outer existential (feeding directly into `RecDecidable.bExists`). -/
theorem mem_Fun_compl_nbhd_iff' (n m j : ℕ) :
    j ∈ Fun (nbhd n)ᶜ (nbhd m)ᶜ ↔
      ∃ c, c < n ∧ n.testBit c = true ∧ untagVal c = j ∧
        ∀ i ∈ decodeList (untagList c), bitAt m i = 1 := by
  rw [mem_Fun_compl_nbhd_iff]
  simp only [mem_bitsCodeList, mem_compl_nbhd, bitAt_eq_one_iff]
  constructor
  · rintro ⟨c, hbit, hval, hall⟩
    exact ⟨c, lt_of_testBit_true hbit, hbit, hval, hall⟩
  · rintro ⟨c, -, hbit, hval, hall⟩
    exact ⟨c, hbit, hval, hall⟩

/-! ### `gMap` is computable -/

/-- `(i,m) ↦ bitAt m i = 1`, i.e. `m.testBit i`, as a `RecDecidable₂` relation (argument order
swapped from `bitAt`'s own `(n,k) ↦ bitAt n k`, to feed `RecDecidable₂.bForallList`). -/
theorem bitAt_swap_isComputable : RecDecidable₂ (fun i m => bitAt m i = 1) :=
  ⟨fun t => bitAt t.unpair.2 t.unpair.1,
    (primrec_bitAt.comp (Nat.Primrec.right.pair Nat.Primrec.left)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd],
    fun _ => Iff.rfl⟩

/-- **The innermost list-check is recursively decidable.** Reindexes `bForallList` along
`untagList` to get `∀i ∈ decodeList (untagList c), bitAt m i = 1` as a function of `(c,m)`, packed
`(c,(j,m))`-style (`j` is a dummy free parameter here, along for the ride to match `gMap`'s later
packing). -/
theorem untagList_bitAt_isComputable :
    RecDecidable (fun w : ℕ => ∀ i ∈ decodeList (untagList w.unpair.1), bitAt w.unpair.2.unpair.2 i = 1) :=
  RecDecidable.of_iff (fun w => by simp only [unpair_pair_fst, unpair_pair_snd])
    (bitAt_swap_isComputable.bForallList.comp
      ((primrec_untagList.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.right)))

/-- **`(c, j, m) ↦ untagVal c = j ∧ ∀i ∈ decodeList (untagList c), m.testBit i`.** Recursively
decidable, packed `(c,(j,m))`-style. -/
theorem untagVal_and_isComputable :
    RecDecidable (fun w : ℕ => untagVal w.unpair.1 = w.unpair.2.unpair.1 ∧
      ∀ i ∈ decodeList (untagList w.unpair.1), bitAt w.unpair.2.unpair.2 i = 1) :=
  (RecDecidable.natEq (primrec_untagVal.comp Nat.Primrec.left)
    (Nat.Primrec.left.comp Nat.Primrec.right)).and untagList_bitAt_isComputable

/-- **`j ∈ Fun (nbhd n)ᶜ (nbhd m)ᶜ` is recursively decidable, jointly in `(n,j,m)`.** Combines
`mem_Fun_compl_nbhd_iff'` (a bounded `∃c < n`) with `RecDecidable.bExists`, packed `(n,(j,m))`-style. -/
theorem mem_Fun_compl_nbhd_isComputable :
    RecDecidable (fun w : ℕ =>
      w.unpair.2.unpair.1 ∈ Fun (nbhd w.unpair.1)ᶜ (nbhd w.unpair.2.unpair.2)ᶜ) := by
  have hbitN : RecDecidable (fun w : ℕ => w.unpair.2.unpair.1.testBit w.unpair.1 = true) :=
    ⟨fun w => bitAt w.unpair.2.unpair.1 w.unpair.1,
      (primrec_bitAt.comp ((Nat.Primrec.left.comp Nat.Primrec.right).pair Nat.Primrec.left)).of_eq
        fun w => by simp only [unpair_pair_fst, unpair_pair_snd],
      fun w => (bitAt_eq_one_iff _ _).symm⟩
  have hCJ' : RecDecidable (fun w : ℕ => untagVal w.unpair.1 = w.unpair.2.unpair.2.unpair.1 ∧
      ∀ i ∈ decodeList (untagList w.unpair.1), bitAt w.unpair.2.unpair.2.unpair.2 i = 1) :=
    RecDecidable.of_iff (fun w => by simp only [unpair_pair_fst, unpair_pair_snd])
      (untagVal_and_isComputable.comp (Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)))
  have hp := hbitN.and hCJ'
  refine RecDecidable.of_iff (fun w => ?_) (hp.bExists Nat.Primrec.left)
  rw [mem_Fun_compl_nbhd_iff']
  simp only [unpair_pair_fst, unpair_pair_snd]

/-- **The implication guarding a single bit of `nbhd k`'s excluded set is recursively decidable,
jointly in `(j,n,m,k)`.** Packed `(j,((n,m),k))`-style. -/
theorem testBit_imp_mem_Fun_isComputable :
    RecDecidable (fun w : ℕ => w.unpair.2.unpair.2.testBit w.unpair.1 = true →
      w.unpair.1 ∈ Fun (nbhd w.unpair.2.unpair.1.unpair.1)ᶜ (nbhd w.unpair.2.unpair.1.unpair.2)ᶜ) := by
  have hktest : RecDecidable (fun w : ℕ => w.unpair.2.unpair.2.testBit w.unpair.1 = true) :=
    ⟨fun w => bitAt w.unpair.2.unpair.2 w.unpair.1,
      (primrec_bitAt.comp ((Nat.Primrec.right.comp Nat.Primrec.right).pair Nat.Primrec.left)).of_eq
        fun w => by simp only [unpair_pair_fst, unpair_pair_snd],
      fun w => (bitAt_eq_one_iff _ _).symm⟩
  have hmem2 : RecDecidable (fun w : ℕ =>
      w.unpair.1 ∈ Fun (nbhd w.unpair.2.unpair.1.unpair.1)ᶜ (nbhd w.unpair.2.unpair.1.unpair.2)ᶜ) :=
    RecDecidable.of_iff (fun w => by simp only [unpair_pair_fst, unpair_pair_snd])
      (mem_Fun_compl_nbhd_isComputable.comp
        ((Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
          (Nat.Primrec.left.pair (Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right)))))
  refine RecDecidable.of_iff (fun w => ?_) (hktest.not.or hmem2)
  constructor
  · intro h
    rcases hktest.em w with hb | hb
    · exact Or.inr (h hb)
    · exact Or.inl hb
  · rintro (hb | hb) hbit
    · exact absurd hbit hb
    · exact hb

/-- **`(nbhd k)ᶜ ⊆ Fun (nbhd n)ᶜ (nbhd m)ᶜ`, bounded-quantifier form.** Every excluded point of
`nbhd k` is below `k` (`lt_of_testBit_true`), so the subset test is a bounded `∀j < k`. -/
theorem compl_nbhd_subset_Fun_iff (n m k : ℕ) : (nbhd k)ᶜ ⊆ Fun (nbhd n)ᶜ (nbhd m)ᶜ ↔
    ∀ j, j < k → (k.testBit j = true → j ∈ Fun (nbhd n)ᶜ (nbhd m)ᶜ) := by
  constructor
  · intro h j _ hj
    exact h (mem_compl_nbhd.mpr hj)
  · intro h j hj
    rw [mem_compl_nbhd] at hj
    exact h j (lt_of_testBit_true hj) hj

/-- **`gMap` is computable.** The neighbourhood relation `gMap_rel_iff` reduces (via
`compl_nbhd_subset_Fun_iff`) to a bounded `∀j < k`, primitive recursive by
`testBit_imp_mem_Fun_isComputable`/`RecDecidable.bForall`. -/
theorem gMap_isComputable :
    IsComputableMap (prodPresentation PNpres PNpres) PNpres gMap := by
  have hall : RecDecidable (fun u : ℕ => ∀ j, j < u.unpair.2 →
      u.unpair.2.testBit j = true →
        j ∈ Fun (nbhd u.unpair.1.unpair.1)ᶜ (nbhd u.unpair.1.unpair.2)ᶜ) :=
    RecDecidable.of_iff (fun u => by simp only [unpair_pair_fst, unpair_pair_snd])
      (testBit_imp_mem_Fun_isComputable.bForall Nat.Primrec.right)
  refine (RecDecidable.of_iff (fun t => ?_) hall).re
  simp only [prodPresentation_X]
  exact (gMap_rel_iff _ _ _).trans (compl_nbhd_subset_Fun_iff _ _ _)

/-! ### `fun`, via currying `gMap` -/

/-- **`fun` as an approximable map** `PN → (PN → PN)`, obtained by currying `gMap`. -/
def funMap : ApproximableMap PN (funSpace PN PN) := curry gMap

/-- **`fun` is computable**, relative to *any* valid function-space presentation
`funPresentation PNpres PNpres gN incl0 incl1 eq1 …` (Theorem 7.5's generic `curry_isComputable`,
fed `gMap_isComputable`). Every such presentation exists (`funSpace_isEffectivelyGiven`); this
result is stated generically over the witnessing deciders, exactly as `curry_isComputable` itself
is, rather than committing to one concrete choice of `gN`/`incl0`/`incl1`/`eq1` for `PN`. -/
theorem funMap_isComputable (gN incl0 incl1 eq1 : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf PNpres PNpres (decodeList c))
      : Set (ApproximableMap PN PN)).Nonempty) (hgNp : Nat.Primrec gN)
    (hincl0 : ∀ s, incl0 s = 1 ↔ PNpres.X s.unpair.1 ⊆ PNpres.X s.unpair.2)
    (hincl0p : Nat.Primrec incl0)
    (hincl1 : ∀ s, incl1 s = 1 ↔ PNpres.X s.unpair.1 ⊆ PNpres.X s.unpair.2)
    (hincl1p : Nat.Primrec incl1)
    (heq1 : ∀ s, eq1 s = 1 ↔ PNpres.X s.unpair.1 = PNpres.X s.unpair.2) (heq1p : Nat.Primrec eq1) :
    IsComputableMap PNpres
      (funPresentation PNpres PNpres gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p hincl1 hincl1p
        heq1 heq1p)
      funMap :=
  curry_isComputable PNpres PNpres PNpres gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p hincl1
    hincl1p heq1 heq1p gMap_isComputable

/-! ### `graph`, dually to `gMap` -/

/-- `GraphIdx W`: the domain-theoretic "positive content" of `graph(W)`, mirroring Exercise 5.14's
`Graph f = {tag ns m ∣ m ∈ f (entries ns)}`, but phrased at the level of neighbourhood relations and
tested against *every* map `f ∈ W` (Scott's "guaranteed regardless of which `f ∈ W`" idiom, as in
`eval`'s `∀ f ∈ F, f.rel X Y`). The "argument" is canonically `tagOfBits n m = tag (decodeList
(bitsCode n n)) m` (`decodeList (bitsCode n n)` has entries exactly `Eₙ`, `mem_bitsCodeList`), so it
ranges over the countably many finite sets `(nbhd n)ᶜ` rather than over arbitrary lists — exactly the
finite-set arguments `Graph` needs, up to the reindexing already used throughout this file. Using the
*primitive-recursive* list `bitsCode n n` (rather than the merely well-founded `bitsList n`) is what
makes the decode direction (`mem_GraphIdx_iff` below) computable. -/
def GraphIdx (W : Set (ApproximableMap PN PN)) : Set ℕ :=
  {c | ∃ n m₀ m, c = tagOfBits n m ∧ (∀ f ∈ W, f.rel (nbhd n) (nbhd m₀)) ∧ m₀.testBit m = true}

/-- **`GraphIdx` is antitone: shrinking `W` (more information about the map) can only add
guaranteed content.** -/
theorem GraphIdx_mono {W W' : Set (ApproximableMap PN PN)} (h : W' ⊆ W) :
    GraphIdx W ⊆ GraphIdx W' := by
  rintro c ⟨n, m₀, m, rfl, hf, hbit⟩
  exact ⟨n, m₀, m, rfl, fun f hf' => hf f (h hf'), hbit⟩

/-- **`graph` as an approximable map** `(PN → PN) → PN`, dually to `gMap`'s "reversal idiom":
`Zᶜ ⊆ GraphIdx W`. -/
def graphMap : ApproximableMap (funSpace PN PN) PN where
  rel W Z := (funSpace PN PN).mem W ∧ PN.mem Z ∧ Zᶜ ⊆ GraphIdx W
  rel_dom := fun ⟨h, _, _⟩ => h
  rel_cod := fun ⟨_, h, _⟩ => h
  master_rel := ⟨(funSpace PN PN).master_mem, PN.master_mem, by
    show (Set.univ : Set ℕ)ᶜ ⊆ GraphIdx Set.univ
    intro x hx
    exact absurd (Set.mem_univ x) hx⟩
  inter_right := by
    rintro W Z Z' ⟨hW, hZ, hsub⟩ ⟨_, hZ', hsub'⟩
    obtain ⟨k, hk⟩ := hZ; obtain ⟨k', hk'⟩ := hZ'; subst hk; subst hk'
    refine ⟨hW, ⟨myLor k k', nbhd_inter k k'⟩, ?_⟩
    rw [compl_inter_nbhd]
    exact Set.union_subset hsub hsub'
  mono := by
    rintro W W' Z Z' ⟨hW, hZ, hsub⟩ hW'W hZZ' hW' hZ'
    obtain ⟨k', rfl⟩ := hZ'
    refine ⟨hW', ⟨k', rfl⟩, ?_⟩
    calc (nbhd k')ᶜ ⊆ Zᶜ := compl_subset_compl_of_subset hZZ'
      _ ⊆ GraphIdx W := hsub
      _ ⊆ GraphIdx W' := GraphIdx_mono hW'W

/-! ### `graph` is computable -/

/-- **`decodeList` is injective**, immediately from the round-trip `encodeList_decodeList`
(`decodeList` has a left inverse). -/
theorem decodeList_injective {a b : ℕ} (h : decodeList a = decodeList b) : a = b := by
  have := congrArg encodeList h
  rwa [encodeList_decodeList, encodeList_decodeList] at this

/-- **`GraphIdx` membership, decoded.** `tagOfBits n m = tag (decodeList (bitsCode n n)) m` is a
*specific* choice of encoding for the pair `(Eₙ, m)`; since `tag` is injective and every code `c`
decodes (via `untagList`/`untagVal`) to *some* `tag`-preimage, `c ∈ GraphIdx W` reduces to the
primitive-recursive check `untagList c = bitsCode n n` (pinning down `n`, by injectivity of
`decodeList`) together with `untagVal c` playing the role of `m`. -/
theorem mem_GraphIdx_iff (W : Set (ApproximableMap PN PN)) (c : ℕ) :
    c ∈ GraphIdx W ↔ ∃ n m₀, untagList c = bitsCode n n ∧
      (∀ f ∈ W, f.rel (nbhd n) (nbhd m₀)) ∧ m₀.testBit (untagVal c) = true := by
  constructor
  · rintro ⟨n, m₀, m, rfl, hf, hbit⟩
    have htag : tag (decodeList (untagList (tagOfBits n m))) (untagVal (tagOfBits n m)) =
        tag (decodeList (bitsCode n n)) m :=
      (tag_untagList_untagVal (tagOfBits n m)).trans (tagOfBits_spec n m)
    obtain ⟨hlist, hval⟩ := tag_injective htag
    refine ⟨n, m₀, decodeList_injective hlist, hf, ?_⟩
    rw [hval]; exact hbit
  · rintro ⟨n, m₀, heq, hf, hbit⟩
    refine ⟨n, m₀, untagVal c, ?_, hf, hbit⟩
    rw [tagOfBits_spec, ← heq]
    exact (tag_untagList_untagVal c).symm

/-- **Membership in a function-space step set, as inclusion of `Xenum`s.** `∀ f ∈ W, f.rel X Y` iff
`W ⊆ step X Y` (`mem_step`); specialised to `W = Xenum … c` and the singleton step neighbourhood
(`Xenum_singleton`), this becomes the *decidable* function-space inclusion `incl_computable`. -/
theorem forall_rel_iff_subset_step {W : Set (ApproximableMap PN PN)} {n m₀ : ℕ} :
    (∀ f ∈ W, f.rel (nbhd n) (nbhd m₀)) ↔ W ⊆ step (nbhd n) (nbhd m₀) := by
  constructor
  · intro h f hf; exact mem_step.mpr (h f hf)
  · intro h f hf; exact mem_step.mp (h hf)

/-- **`j ∈ GraphIdx (Xenum … c)` is recursively enumerable, jointly in `(c, j)`.** Unfolds via
`mem_GraphIdx_iff`/`forall_rel_iff_subset_step`/`Xenum_singleton` to `∃ n m₀, <primitive-recursive
check> ∧ Xenum … c ⊆ Xenum … (pair (pair n m₀) 0 + 1) ∧ <bit test>` — a decidable body existentially
quantified over the two witnesses `n, m₀` (`REPred.proj`, applied twice). -/
theorem graphIdx_isComputable (gN incl0 incl1 eq1 : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf PNpres PNpres (decodeList c))
      : Set (ApproximableMap PN PN)).Nonempty) (hgNp : Nat.Primrec gN)
    (hincl0 : ∀ s, incl0 s = 1 ↔ PNpres.X s.unpair.1 ⊆ PNpres.X s.unpair.2)
    (hincl0p : Nat.Primrec incl0)
    (hincl1 : ∀ s, incl1 s = 1 ↔ PNpres.X s.unpair.1 ⊆ PNpres.X s.unpair.2)
    (hincl1p : Nat.Primrec incl1)
    (heq1 : ∀ s, eq1 s = 1 ↔ PNpres.X s.unpair.1 = PNpres.X s.unpair.2) (heq1p : Nat.Primrec eq1) :
    REPred₂ (fun c j => j ∈ GraphIdx
      (Xenum PNpres PNpres gN c : Set (ApproximableMap PN PN))) := by
  have hinclP : RecDecidable₂ (fun a b =>
      (Xenum PNpres PNpres gN a : Set (ApproximableMap PN PN)) ⊆ Xenum PNpres PNpres gN b) :=
    (funPresentation PNpres PNpres gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p hincl1 hincl1p heq1
      heq1p).incl_computable
  -- packed `w = ⟨m₀, ⟨n, ⟨c, j⟩⟩⟩`; the base predicate is decidable in `w`.
  have hj : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hn : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hm0 : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hbitsCodeArg : Nat.Primrec (fun w : ℕ => bitsCode w.unpair.2.unpair.1 w.unpair.2.unpair.1) :=
    (primrec_bitsCode.comp (hn.pair hn)).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hpairArg : Nat.Primrec
      (fun w : ℕ => Nat.pair (Nat.pair w.unpair.2.unpair.1 w.unpair.1) 0 + 1) :=
    Nat.Primrec.succ.comp ((hn.pair hm0).pair (Nat.Primrec.const 0))
  have hA : RecDecidable (fun w : ℕ =>
      untagList w.unpair.2.unpair.2.unpair.2 =
        bitsCode w.unpair.2.unpair.1 w.unpair.2.unpair.1) :=
    RecDecidable.natEq (primrec_untagList.comp hj) hbitsCodeArg
  have hB : RecDecidable (fun w : ℕ =>
      (Xenum PNpres PNpres gN w.unpair.2.unpair.2.unpair.1 : Set (ApproximableMap PN PN)) ⊆
        Xenum PNpres PNpres gN (Nat.pair (Nat.pair w.unpair.2.unpair.1 w.unpair.1) 0 + 1)) :=
    RecDecidable.of_iff (fun w => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hinclP.comp (hc.pair hpairArg))
  have hC : RecDecidable (fun w : ℕ =>
      w.unpair.1.testBit (untagVal w.unpair.2.unpair.2.unpair.2) = true) :=
    ⟨fun w => bitAt w.unpair.1 (untagVal w.unpair.2.unpair.2.unpair.2),
      (primrec_bitAt.comp (hm0.pair (primrec_untagVal.comp hj))).of_eq fun w => by
        simp only [unpair_pair_fst, unpair_pair_snd],
      fun w => (bitAt_eq_one_iff _ _).symm⟩
  have hre : REPred (fun w : ℕ =>
      untagList w.unpair.2.unpair.2.unpair.2 =
        bitsCode w.unpair.2.unpair.1 w.unpair.2.unpair.1 ∧
      (Xenum PNpres PNpres gN w.unpair.2.unpair.2.unpair.1 : Set (ApproximableMap PN PN)) ⊆
        Xenum PNpres PNpres gN (Nat.pair (Nat.pair w.unpair.2.unpair.1 w.unpair.1) 0 + 1) ∧
      w.unpair.1.testBit (untagVal w.unpair.2.unpair.2.unpair.2) = true) :=
    (hA.and (hB.and hC)).re
  have hp2 := hre.proj.proj
  refine REPred.of_iff (fun t => ?_) hp2
  dsimp only
  rw [mem_GraphIdx_iff]
  constructor
  · rintro ⟨n, m₀, heq, hf, hbit⟩
    refine ⟨n, m₀, ?_⟩
    show untagList (Nat.pair m₀ (Nat.pair n t)).unpair.2.unpair.2.unpair.2 =
          bitsCode (Nat.pair m₀ (Nat.pair n t)).unpair.2.unpair.1
            (Nat.pair m₀ (Nat.pair n t)).unpair.2.unpair.1 ∧
        (Xenum PNpres PNpres gN (Nat.pair m₀ (Nat.pair n t)).unpair.2.unpair.2.unpair.1
          : Set (ApproximableMap PN PN)) ⊆
          Xenum PNpres PNpres gN (Nat.pair
            (Nat.pair (Nat.pair m₀ (Nat.pair n t)).unpair.2.unpair.1
              (Nat.pair m₀ (Nat.pair n t)).unpair.1) 0 + 1) ∧
        (Nat.pair m₀ (Nat.pair n t)).unpair.1.testBit
          (untagVal (Nat.pair m₀ (Nat.pair n t)).unpair.2.unpair.2.unpair.2) = true
    simp only [unpair_pair_fst, unpair_pair_snd]
    refine ⟨heq, ?_, hbit⟩
    rw [Xenum_singleton PNpres PNpres gN hgN n m₀]
    exact forall_rel_iff_subset_step.mp hf
  · rintro ⟨n, m₀, hbase⟩
    simp only [unpair_pair_fst, unpair_pair_snd] at hbase
    obtain ⟨heq, hsub, hbit⟩ := hbase
    refine ⟨n, m₀, heq, ?_, hbit⟩
    apply forall_rel_iff_subset_step.mpr
    rwa [Xenum_singleton PNpres PNpres gN hgN n m₀] at hsub

/-- **`(nbhd k)ᶜ ⊆ S`, bounded-quantifier form**, for an *arbitrary* target set `S`: every excluded
point of `nbhd k` is below `k` (`lt_of_testBit_true`), so the subset test is a bounded `∀ j < k`.
(The `S`-generic form of `compl_nbhd_subset_Fun_iff`.) -/
theorem compl_nbhd_subset_iff (S : Set ℕ) (k : ℕ) : (nbhd k)ᶜ ⊆ S ↔
    ∀ j, j < k → (k.testBit j = true → j ∈ S) := by
  constructor
  · intro h j _ hj
    exact h (mem_compl_nbhd.mpr hj)
  · intro h j hj
    rw [mem_compl_nbhd] at hj
    exact h j (lt_of_testBit_true hj) hj

/-- `graphMap`'s neighbourhood relation on indices: `Xenum … c` relates to `nbhd m` iff `nbhd m`'s
excluded set fits inside `GraphIdx (Xenum … c)`. -/
theorem graphMap_rel_iff (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf PNpres PNpres (decodeList c))
      : Set (ApproximableMap PN PN)).Nonempty) (c m : ℕ) :
    graphMap.rel (Xenum PNpres PNpres gN c) (nbhd m) ↔
      (nbhd m)ᶜ ⊆ GraphIdx (Xenum PNpres PNpres gN c) := by
  constructor
  · rintro ⟨_, _, hsub⟩; exact hsub
  · intro h; exact ⟨Xenum_mem PNpres PNpres gN hgN c, ⟨m, rfl⟩, h⟩

/-- **`graph` is computable (Exercise 7.23, dually to `gMap`).** Relative to *any* valid
function-space presentation `funPresentation PNpres PNpres gN incl0 incl1 eq1 …`, `graphMap`'s
neighbourhood relation reduces (via `graphMap_rel_iff`) to a bounded `∀ j < m`, r.e. by
`graphIdx_isComputable`/`REPred.forall_mem_decodeList₂` (the bound enumerated by `bitsCode m m`,
`mem_bitsCodeList`). -/
theorem graphMap_isComputable (gN incl0 incl1 eq1 : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf PNpres PNpres (decodeList c))
      : Set (ApproximableMap PN PN)).Nonempty) (hgNp : Nat.Primrec gN)
    (hincl0 : ∀ s, incl0 s = 1 ↔ PNpres.X s.unpair.1 ⊆ PNpres.X s.unpair.2)
    (hincl0p : Nat.Primrec incl0)
    (hincl1 : ∀ s, incl1 s = 1 ↔ PNpres.X s.unpair.1 ⊆ PNpres.X s.unpair.2)
    (hincl1p : Nat.Primrec incl1)
    (heq1 : ∀ s, eq1 s = 1 ↔ PNpres.X s.unpair.1 = PNpres.X s.unpair.2) (heq1p : Nat.Primrec eq1) :
    IsComputableMap
      (funPresentation PNpres PNpres gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p hincl1 hincl1p
        heq1 heq1p)
      PNpres graphMap := by
  have hidx := graphIdx_isComputable gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p hincl1 hincl1p
    heq1 heq1p
  have hforall : REPred (fun t : ℕ => ∀ j ∈ decodeList t.unpair.2,
      j ∈ GraphIdx (Xenum PNpres PNpres gN t.unpair.1 : Set (ApproximableMap PN PN))) :=
    REPred.forall_mem_decodeList₂ hidx
  have hreidx : Nat.Primrec (fun s : ℕ => Nat.pair s.unpair.1 (bitsCode s.unpair.2 s.unpair.2)) :=
    Nat.Primrec.left.pair ((primrec_bitsCode.comp (Nat.Primrec.right.pair
      Nat.Primrec.right)).of_eq fun s => by simp only [unpair_pair_fst, unpair_pair_snd])
  refine REPred.of_iff (fun s => ?_) (hforall.comp hreidx)
  simp only [unpair_pair_fst, unpair_pair_snd]
  exact (graphMap_rel_iff gN hgN s.unpair.1 s.unpair.2).trans (by
    rw [compl_nbhd_subset_iff]
    exact ⟨fun h j hj => h j (lt_of_testBit_true (mem_bitsCodeList.mp hj))
        (mem_bitsCodeList.mp hj),
      fun h j hjlt hjbit => h j (mem_bitsCodeList.mpr hjbit)⟩)

end Scott1980.Neighborhood.Exercise723

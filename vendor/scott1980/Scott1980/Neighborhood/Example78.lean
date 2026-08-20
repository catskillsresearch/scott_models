/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Definition71

/-!
# Example 7.8 (Scott 1981, PRG-19, §7) — the powerset `PN` is effectively given

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII.

> **Example 7.8.** We have often made reference to the powerset `PN` as a domain and we should
> check here that it is effectively given. … the neighbourhoods of `PN` are ordered … in the
> partial ordering *converse* to that [of finite sets]. … What we need first is an enumeration of
> all finite sets of integers:
> `Eₙ = {k ∣ ∃ i, j. i < 2ᵏ and n = i + 2ᵏ + j·2ᵏ⁺¹}`.
> The idea is that `k ∈ Eₙ` means the exponent `k` occurs in the binary expansion of `n`. … as a
> neighbourhood system `(PN) = {N ∖ Eₙ ∣ n ∈ ℕ}`. As the relationship `Eₙ ∪ Eₘ = E_k` is
> recursive, there is no trouble in proving that this is a computable presentation. In this system,
> of course, any two neighbourhoods are consistent.

**Formalisation.** Scott's `Eₙ = {k ∣ ∃ i,j. i < 2ᵏ ∧ n = i + 2ᵏ + j·2ᵏ⁺¹}` is exactly "`k` is a
set bit of `n`", i.e. `Nat.testBit n k`. The neighbourhoods are the *cofinite* sets
`ℕ ∖ Eₙ = {k ∣ ¬ n.testBit k}`, here `nbhd n := {k ∣ n.testBit k = false}` (so `nbhd 0 = ℕ = Δ`).

* `nbhd_inter`: `nbhd n ∩ nbhd m = nbhd (n ||| m)` — the intersection of two cofinite neighbourhoods
  removes the *union* `Eₙ ∪ Eₘ = E_{n ||| m}` of the excluded finite sets. This is Scott's
  `Eₙ ∪ Eₘ = E_k` with `k = n ||| m` (bitwise OR).
* `nbhd_injective`: `n ↦ nbhd n` is one-one (the converse-inclusion ordering Scott mentions; here we
  only need injectivity, from `Nat.eq_of_testBit_eq`).
* `PN` is the neighbourhood system `{nbhd n ∣ n}` over the token type `ℕ`; it is closed under
  intersection because `nbhd n ∩ nbhd m = nbhd (n ||| m)` is again a neighbourhood (so in fact *any*
  two neighbourhoods are consistent — `PN_consistent`).
* `PNpres` is the computable presentation: the enumeration is `nbhd`, the intersection function is
  the **choice-free primitive-recursive bitwise OR** `Domain.Recursive.myLor` (`= (· ||| ·)`,
  `myLor_eq_lor`), and Scott's relation 7.1(i) `nbhd n ∩ nbhd m = nbhd k ↔ (n ||| m) = k` is decided
  by `RecDecidable.natEq` (equality of two primitive-recursive functions). Relation 7.1(ii) is
  *always true* (any two neighbourhoods are consistent), so it is trivially recursively decidable.
* `PN_isEffectivelyGiven`: `PN` admits a computable presentation.

Everything is choice-free (`⊆ {propext, Quot.sound}`): all the bit-level facts go through mathlib's
`Nat.testBit_lor` / `Nat.eq_of_testBit_eq` (both `[propext, Quot.sound]`) and the bespoke
primitive-recursive `myLor`.
-/

namespace Scott1980.Neighborhood.Example78

open Domain.Recursive NeighborhoodSystem

/-- The neighbourhood `ℕ ∖ Eₙ` of the powerset domain: the cofinite set of bit positions **not**
set in `n`. Scott's `Eₙ` is `{k ∣ n.testBit k}`, so `nbhd n = {k ∣ n.testBit k = false}`. -/
def nbhd (n : ℕ) : Set ℕ := {k | n.testBit k = false}

@[simp] theorem mem_nbhd {n k : ℕ} : k ∈ nbhd n ↔ n.testBit k = false := Iff.rfl

/-- `nbhd 0 = ℕ = Δ`: `0` has no set bits, so its excluded set `E₀` is empty. -/
theorem nbhd_zero : nbhd 0 = Set.univ := by
  ext k; simp [nbhd, Nat.zero_testBit]

/-- **Scott's `Eₙ ∪ Eₘ = E_{n ||| m}`.** The intersection of two cofinite neighbourhoods is again
one: `nbhd n ∩ nbhd m = nbhd (n ||| m)` (bitwise OR of the excluded finite sets). -/
theorem nbhd_inter (n m : ℕ) : nbhd n ∩ nbhd m = nbhd (myLor n m) := by
  ext k
  simp only [nbhd, Set.mem_inter_iff, Set.mem_setOf_eq, myLor_eq_lor, Nat.testBit_lor,
    Bool.or_eq_false_iff]

/-- The enumeration `n ↦ nbhd n` is **one-one** (Scott's converse-ordered neighbourhoods are in
bijection with the indices): from `nbhd n = nbhd m` we recover `n = m` bit by bit. -/
theorem nbhd_injective {n m : ℕ} (h : nbhd n = nbhd m) : n = m := by
  apply Nat.eq_of_testBit_eq
  intro k
  have hk : (n.testBit k = false) ↔ (m.testBit k = false) := by
    have := Set.ext_iff.mp h k; simpa only [mem_nbhd] using this
  cases hn : n.testBit k <;> cases hm : m.testBit k <;> simp_all

/-- **The powerset domain `PN`** as a neighbourhood system over the token type `ℕ`: the
neighbourhoods are the cofinite sets `nbhd n`, with master `Δ = ℕ`. Closure under intersection is
`nbhd_inter` (the intersection is `nbhd (n ||| m)`), so no consistency hypothesis is even needed. -/
def PN : NeighborhoodSystem ℕ where
  mem Y := ∃ n, Y = nbhd n
  master := Set.univ
  master_mem := ⟨0, nbhd_zero.symm⟩
  inter_mem := by
    rintro X Y Z ⟨a, rfl⟩ ⟨b, rfl⟩ _ _
    exact ⟨myLor a b, nbhd_inter a b⟩
  sub_master := by rintro X _; exact Set.subset_univ X

/-- **Any two neighbourhoods of `PN` are consistent** (Scott: "any two neighbourhoods are
consistent"): their intersection `nbhd (n ||| m)` is itself a neighbourhood contained in both. -/
theorem PN_consistent (n m : ℕ) : ∃ k, nbhd k ⊆ nbhd n ∩ nbhd m :=
  ⟨myLor n m, (nbhd_inter n m).symm.subset⟩

/-- **Example 7.8 — the computable presentation of `PN`.** The enumeration is `nbhd`; the
intersection function is the choice-free primitive-recursive bitwise OR `myLor`; Scott's relation
7.1(i) is `nbhd n ∩ nbhd m = nbhd k ↔ (n ||| m) = k`, decided by `RecDecidable.natEq`; relation
7.1(ii) (consistency) is always true. -/
def PNpres : ComputablePresentation PN where
  X := nbhd
  mem_X n := ⟨n, rfl⟩
  surj := by rintro Y ⟨n, rfl⟩; exact ⟨n, rfl⟩
  interEq_computable := by
    -- `nbhd n ∩ nbhd m = nbhd k ↔ myLor n m = k`, an equality of two primitive-recursive functions
    refine RecDecidable.of_iff (q := fun t =>
        nbhd t.unpair.1 ∩ nbhd t.unpair.2.unpair.1 = nbhd t.unpair.2.unpair.2)
      (fun t => ?_)
      (RecDecidable.natEq
        (a := fun t => myLor t.unpair.1 t.unpair.2.unpair.1)
        (b := fun t => t.unpair.2.unpair.2)
        ((primrec_myLor.comp
          (Nat.Primrec.left.pair (Nat.Primrec.left.comp Nat.Primrec.right))).of_eq fun s => by
            simp only [unpair_pair_fst, unpair_pair_snd])
        (Nat.Primrec.right.comp Nat.Primrec.right))
    -- the pointwise equivalence
    dsimp only
    constructor
    · intro h; exact nbhd_injective ((nbhd_inter _ _).symm.trans h)
    · intro h; rw [nbhd_inter]; exact congrArg nbhd h
  cons_computable :=
    recDecidable_of_forall fun t => ⟨myLor t.unpair.1 t.unpair.2, (nbhd_inter _ _).symm.subset⟩
  inter := myLor
  inter_primrec := primrec_myLor
  inter_spec := fun {n m} _ => (nbhd_inter n m).symm
  masterIdx := 0
  masterIdx_spec := nbhd_zero

/-- **Example 7.8 (Scott 1981, PRG-19).** The powerset domain `PN` is effectively given. -/
theorem PN_isEffectivelyGiven : PN.IsEffectivelyGiven := ⟨PNpres⟩

end Scott1980.Neighborhood.Example78

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Exercise316
import Mathlib.Logic.Equiv.Nat

/-!
# Exercise 8.25 (Scott 1981, PRG-19, §8), step 2 — `𝒰^∞ × 𝒰^∞ ≅ 𝒰^∞`

Scott's hint asks us to first establish `𝒰^∞ × 𝒰^∞ ≅ 𝒰^∞`, where `𝒰^∞` is the countable power of
the universal domain `𝒰` with itself. We take `𝒰^∞ := iterSys 𝒰` (Exercise 3.16's infinite iterate,
already available with a full API: `iterSeqEquiv`, `iter_isomorphic`, `projN`, effective givenness).

The isomorphism `𝒰^∞ × 𝒰^∞ ≅ 𝒰^∞` is the domain-level shadow of the classical fact that a pair of
sequences can be interleaved into a single sequence without loss of information: `ℕ ⊕ ℕ ≃ ℕ`
(`Equiv.natSumNatEquivNat`) reindexes `(ℕ → E) × (ℕ → E) ≅ (ℕ ⊕ ℕ → E) ≅ (ℕ → E)` for *any*
preordered `E`, order-isomorphically. Transporting along `iterSeqEquiv` turns this into
`(iterSys V).Element × (iterSys V).Element ≃o (iterSys V).Element` for any `V`, i.e.
`iterSys V × iterSys V ≅ᴰ iterSys V`. Specializing `V := 𝒰` gives the required `𝒰^∞ × 𝒰^∞ ≅ 𝒰^∞`.

Everything here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem

variable {α : Type*}

/-! ### Generic order-isomorphism lemmas about `Pi`/`Prod` types -/

/-- Reindexing a non-dependent `ι → E` arrow type along a bijection of index types is an order
isomorphism, for the pointwise order on both sides. (Named distinctly from `Exercise324Iter.lean`'s
`piCongrOrderIso`, which reindexes *dependent* `Pi` types along a fixed index type instead.) -/
def arrowReindexOrderIso {ι ι' : Type*} (e : ι ≃ ι') (E : Type*) [Preorder E] :
    (ι → E) ≃o (ι' → E) where
  toFun f i' := f (e.symm i')
  invFun g i := g (e i)
  left_inv f := by funext i; simp
  right_inv g := by funext i'; simp
  map_rel_iff' := by
    intro f g
    constructor
    · intro h i
      simpa using h (e i)
    · intro h i'
      simpa using h (e.symm i')

/-- The pointwise order on `α ⊕ β → E` corresponds, coordinatewise, to the product order on
`(α → E) × (β → E)`: splitting a sum-indexed family into its two summand-indexed restrictions is an
order isomorphism. -/
def sumArrowOrderIso (α β : Type*) (E : Type*) [Preorder E] :
    (α ⊕ β → E) ≃o (α → E) × (β → E) where
  toFun f := (fun a => f (Sum.inl a), fun b => f (Sum.inr b))
  invFun p := Sum.elim p.1 p.2
  left_inv f := by funext i; cases i <;> rfl
  right_inv p := rfl
  map_rel_iff' := by
    intro f g
    constructor
    · rintro ⟨h1, h2⟩ i
      cases i with
      | inl a => exact h1 a
      | inr b => exact h2 b
    · intro h
      exact ⟨fun a => h (Sum.inl a), fun b => h (Sum.inr b)⟩

/-- **Interleaving.** Two `ℕ`-indexed sequences of `E` can be merged, order-isomorphically, into a
single `ℕ`-indexed sequence, via the pairing bijection `ℕ ⊕ ℕ ≃ ℕ`. -/
def interleaveOrderIso (E : Type*) [Preorder E] : (ℕ → E) × (ℕ → E) ≃o (ℕ → E) :=
  (sumArrowOrderIso ℕ ℕ E).symm.trans (arrowReindexOrderIso Equiv.natSumNatEquivNat E)

/-! ### `𝒟^∞ × 𝒟^∞ ≅ 𝒟^∞` for every `𝒟`, in particular for `𝒟 = 𝒰` -/

/-- The order isomorphism `|𝒟^∞ × 𝒟^∞| ≃o |𝒟^∞|` underlying `pow_prod_isomorphic`. -/
def powProdOrderIso (V : NeighborhoodSystem α) :
    (prod (iterSys V) (iterSys V)).Element ≃o (iterSys V).Element :=
  (prodEquiv (iterSys V) (iterSys V)).trans <|
    (prodCongrOrderIso (iterSeqEquiv V) (iterSeqEquiv V)).trans <|
      (interleaveOrderIso V.Element).trans (iterSeqEquiv V).symm

/-- **Exercise 8.25 (Scott 1981, PRG-19), first step: `𝒟^∞ × 𝒟^∞ ≅ 𝒟^∞`**, for any `𝒟`. Specialized
to `𝒟 = 𝒰` this is Scott's `𝒰^∞ × 𝒰^∞ ≅ 𝒰^∞`. -/
theorem pow_prod_isomorphic (V : NeighborhoodSystem α) :
    prod (iterSys V) (iterSys V) ≅ᴰ iterSys V :=
  ⟨powProdOrderIso V⟩

end Scott1980.Neighborhood

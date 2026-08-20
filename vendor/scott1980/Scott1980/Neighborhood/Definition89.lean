/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Theorem88n
import Scott1980.Neighborhood.Theorem74
import Scott1980.Neighborhood.Theorem75
import Scott1980.Neighborhood.Exercise326Sum
import Scott1980.Neighborhood.Exercise319

/-!
# Definition 8.9 (Scott 1981, PRG-19) — the combinators `a+b`, `a×b`, `a→b` on projections of `𝒰`

> **Definition 8.9.** Let the computable projection pairs `i₊ : 𝒰+𝒰 → 𝒰` and `j₊ : 𝒰 → 𝒰+𝒰` be
> fixed. Similarly choose `i_×, j_×` and `i_→, j_→` for `𝒰×𝒰` and `𝒰→𝒰`. Define, for all
> `a, b : 𝒰 → 𝒰`:
>
> `a + b = cond ∘ ⟨which, i₊∘in₀∘a∘out₀, i₊∘in₁∘b∘out₁⟩ ∘ j₊`;
> `a × b = i_× ∘ ⟨a∘proj₀, b∘proj₁⟩ ∘ j_×`;
> `a → b = i_→ ∘ (λf. b∘f∘a) ∘ j_→`.

## The six fixed maps

`𝒰+𝒰`, `𝒰×𝒰`, `𝒰→𝒰` are each effectively given (Theorem 7.4/7.5 applied twice to `U`'s own
presentation), so `theorem_8_8_b_strong` (`Theorem88n.lean`) hands each of them a *computable*
projection pair into `U`. Scott's "let ... be fixed" is exactly a choice out of that (non-unique)
existential — extracted here via `Exists.choose`, the same way every other "fixed but arbitrary
choice" in this development is handled (e.g. `U` itself, `Definition87.lean`). Since
`theorem_8_8_b_strong` already carries `U`'s own inherited `Classical.choice` footprint (see
`Theorem88n.lean`), this extraction adds no *marginal* taint.

## The three combinators

Built by direct transcription of Scott's formulas from existing combinators: `cond`/`whichMap`
(Exercise 3.26), `inMap₀/₁`/`outMap₀/₁` (Exercise 3.18/3.19), `paired`/`proj₀/₁` (Lecture III,
`Product.lean`), and `curry`/`evalMap`/`prodMap` (`FunctionSpace.lean`, Exercise 3.19) for the
`λf. b∘f∘a` clause: uncurried, `(f,x) ↦ b(f(a(x)))` is
`b ∘ eval ∘ (id ×ₘ a)`, so `λf. b∘f∘a = curry (b ∘ eval ∘ (id ×ₘ a))`.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

/-! ## `𝒰`-nonemptiness, and the three effectively-given constructs -/

/-- Every `𝒰`-neighbourhood is non-empty (built into Definition 8.7). -/
theorem U_mem_nonempty : ∀ X, U.mem X → X.Nonempty := fun _ hX => hX.2.1

/-- `𝒰 + 𝒰` is effectively given (Theorem 7.4, applied to `U`'s own presentation twice). -/
theorem sumUU_isEffectivelyGiven :
    (sum U U U_mem_nonempty U_mem_nonempty).IsEffectivelyGiven :=
  sum_isEffectivelyGiven U_isEffectivelyGiven U_isEffectivelyGiven

/-- `𝒰 × 𝒰` is effectively given (Theorem 7.4, applied to `U`'s own presentation twice). -/
theorem prodUU_isEffectivelyGiven : (prod U U).IsEffectivelyGiven :=
  prod_isEffectivelyGiven U_isEffectivelyGiven U_isEffectivelyGiven

/-- `𝒰 → 𝒰` is effectively given (Theorem 7.5, applied to `U`'s own presentation twice). -/
theorem funSpaceUU_isEffectivelyGiven : (funSpace U U).IsEffectivelyGiven :=
  funSpace_isEffectivelyGiven U_isEffectivelyGiven U_isEffectivelyGiven

/-- A fixed presentation of `𝒰 + 𝒰`. -/
noncomputable def sumUUPresentation : ComputablePresentation (sum U U U_mem_nonempty U_mem_nonempty) :=
  sumUU_isEffectivelyGiven.some

/-- A fixed presentation of `𝒰 × 𝒰`. -/
noncomputable def prodUUPresentation : ComputablePresentation (prod U U) :=
  prodUU_isEffectivelyGiven.some

/-- A fixed presentation of `𝒰 → 𝒰`. -/
noncomputable def funSpaceUUPresentation : ComputablePresentation (funSpace U U) :=
  funSpaceUU_isEffectivelyGiven.some

/-! ## Definition 8.9 — the six fixed computable projection pairs -/

/-- **`i₊ : 𝒰+𝒰 → 𝒰`** (Definition 8.9), fixed by `theorem_8_8_b_strong` applied to `𝒰+𝒰`. -/
noncomputable def iPlus : ApproximableMap (sum U U U_mem_nonempty U_mem_nonempty) U :=
  (theorem_8_8_b_strong sumUUPresentation).choose

/-- **`j₊ : 𝒰 → 𝒰+𝒰`** (Definition 8.9). -/
noncomputable def jPlus : ApproximableMap U (sum U U U_mem_nonempty U_mem_nonempty) :=
  (theorem_8_8_b_strong sumUUPresentation).choose_spec.choose

theorem jPlus_comp_iPlus : jPlus.comp iPlus = idMap _ :=
  (theorem_8_8_b_strong sumUUPresentation).choose_spec.choose_spec.1

theorem iPlus_comp_jPlus_le : iPlus.comp jPlus ≤ idMap U :=
  (theorem_8_8_b_strong sumUUPresentation).choose_spec.choose_spec.2.1

theorem iPlus_isComputableMap : IsComputableMap sumUUPresentation UComputablePresentation iPlus :=
  (theorem_8_8_b_strong sumUUPresentation).choose_spec.choose_spec.2.2.1

theorem jPlus_isComputableMap : IsComputableMap UComputablePresentation sumUUPresentation jPlus :=
  (theorem_8_8_b_strong sumUUPresentation).choose_spec.choose_spec.2.2.2

/-- **`i_× : 𝒰×𝒰 → 𝒰`** (Definition 8.9), fixed by `theorem_8_8_b_strong` applied to `𝒰×𝒰`. -/
noncomputable def iTimes : ApproximableMap (prod U U) U :=
  (theorem_8_8_b_strong prodUUPresentation).choose

/-- **`j_× : 𝒰 → 𝒰×𝒰`** (Definition 8.9). -/
noncomputable def jTimes : ApproximableMap U (prod U U) :=
  (theorem_8_8_b_strong prodUUPresentation).choose_spec.choose

theorem jTimes_comp_iTimes : jTimes.comp iTimes = idMap _ :=
  (theorem_8_8_b_strong prodUUPresentation).choose_spec.choose_spec.1

theorem iTimes_comp_jTimes_le : iTimes.comp jTimes ≤ idMap U :=
  (theorem_8_8_b_strong prodUUPresentation).choose_spec.choose_spec.2.1

theorem iTimes_isComputableMap :
    IsComputableMap prodUUPresentation UComputablePresentation iTimes :=
  (theorem_8_8_b_strong prodUUPresentation).choose_spec.choose_spec.2.2.1

theorem jTimes_isComputableMap :
    IsComputableMap UComputablePresentation prodUUPresentation jTimes :=
  (theorem_8_8_b_strong prodUUPresentation).choose_spec.choose_spec.2.2.2

/-- **`i_→ : (𝒰→𝒰) → 𝒰`** (Definition 8.9), fixed by `theorem_8_8_b_strong` applied to `𝒰→𝒰`. -/
noncomputable def iArrow : ApproximableMap (funSpace U U) U :=
  (theorem_8_8_b_strong funSpaceUUPresentation).choose

/-- **`j_→ : 𝒰 → (𝒰→𝒰)`** (Definition 8.9). -/
noncomputable def jArrow : ApproximableMap U (funSpace U U) :=
  (theorem_8_8_b_strong funSpaceUUPresentation).choose_spec.choose

theorem jArrow_comp_iArrow : jArrow.comp iArrow = idMap _ :=
  (theorem_8_8_b_strong funSpaceUUPresentation).choose_spec.choose_spec.1

theorem iArrow_comp_jArrow_le : iArrow.comp jArrow ≤ idMap U :=
  (theorem_8_8_b_strong funSpaceUUPresentation).choose_spec.choose_spec.2.1

theorem iArrow_isComputableMap :
    IsComputableMap funSpaceUUPresentation UComputablePresentation iArrow :=
  (theorem_8_8_b_strong funSpaceUUPresentation).choose_spec.choose_spec.2.2.1

theorem jArrow_isComputableMap :
    IsComputableMap UComputablePresentation funSpaceUUPresentation jArrow :=
  (theorem_8_8_b_strong funSpaceUUPresentation).choose_spec.choose_spec.2.2.2

/-! ## Definition 8.9 — the three combinators -/

/-- **`a + b : 𝒰 → 𝒰`** (Definition 8.9): `cond ∘ ⟨which, i₊∘in₀∘a∘out₀, i₊∘in₁∘b∘out₁⟩ ∘ j₊`. -/
noncomputable def sumComb (a b : ApproximableMap U U) : ApproximableMap U U :=
  (cond U).comp
    ((paired (whichMap U U U_mem_nonempty U_mem_nonempty)
        (paired (iPlus.comp ((inMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).comp
                  (a.comp (outMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)))))
                (iPlus.comp ((inMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).comp
                  (b.comp (outMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty))))))).comp
      jPlus)

/-- **`a × b : 𝒰 → 𝒰`** (Definition 8.9): `i_× ∘ ⟨a∘proj₀, b∘proj₁⟩ ∘ j_×`. -/
noncomputable def prodComb (a b : ApproximableMap U U) : ApproximableMap U U :=
  iTimes.comp ((paired (a.comp (proj₀ U U)) (b.comp (proj₁ U U))).comp jTimes)

/-- **`λf. b∘f∘a : (𝒰→𝒰) → (𝒰→𝒰)`**, uncurried as `b ∘ eval ∘ (id ×ₘ a)`. -/
noncomputable def lamComb (a b : ApproximableMap U U) :
    ApproximableMap (funSpace U U) (funSpace U U) :=
  curry (b.comp ((evalMap U U).comp (prodMap (idMap (funSpace U U)) a)))

/-- **`a → b : 𝒰 → 𝒰`** (Definition 8.9): `i_→ ∘ (λf. b∘f∘a) ∘ j_→`. -/
noncomputable def arrowComb (a b : ApproximableMap U U) : ApproximableMap U U :=
  iArrow.comp ((lamComb a b).comp jArrow)

end Scott1980.Neighborhood

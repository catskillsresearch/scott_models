/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Proposition810b
import Scott1980.Neighborhood.Table55
import Scott1980.Neighborhood.Exercise823
import Scott1980.Neighborhood.Exercise715
import Scott1980.Neighborhood.Exercise825Pow
import Scott1980.Neighborhood.Exercise825Embed
import Scott1980.Neighborhood.Exercise825Closing
import Scott1980.Neighborhood.Exercise820

/-!
# Exercise 8.25 (Scott 1981, PRG-19, §8), step 3 — solving `D ≅ D → 𝒰^∞` by the fixed-point method

Scott's hint: solve `D ≅ D → 𝒰^∞` "using the methods of Exercise 8.23". This file supplies the
one remaining ingredient `Exercise825Closing.lean` needs: a concrete `D` with `D ≅ D → V` for
`V := iterSys 𝒰 = 𝒰^∞`.

## Strategy

Exercise 8.23's abstract machinery (`Exercise823.isFinitaryProjection_fixOp`,
`Exercise823.fixedDomain_fixOp_iso_T`) turns "a continuous operator `t : (𝒰→𝒰) → (𝒰→𝒰)` sending
finitary projections to finitary projections, with `Fix(t(a)) ≅ T(a)`" into a genuine solution
`D_{‖t‖} ≅ T(‖t‖)`. We instantiate `T(a) := D_a → D_c` (Proposition 8.10(b)'s `→`-case) for a
*fixed* finitary projection `c : 𝒰 → 𝒰` with `Fix(c) ≅ 𝒰^∞`, so `t(a) := a → c = arrowComb a c`
(`a` varying, `c` fixed) and `T(‖t‖) = D_{‖t‖} → D_c ≅ D_{‖t‖} → 𝒰^∞`.

## Building `c` with `Fix(c) ≅ 𝒰^∞`

`𝒰^∞ = iterSys 𝒰` is effectively given (`Exercise715.iterSys_isEffectivelyGiven`), so Theorem
8.8(b)'s `theorem_8_8_b_strong` gives a projection pair `i : 𝒰^∞ → 𝒰`, `j : 𝒰 → 𝒰^∞` with
`j∘i = I` and `i∘j ≤ I`. Setting `c := i∘j`, Proposition 8.10(b)'s generic
`elementIsoOfProjectionPair`/`isFinitary_of_projectionPair` machinery gives `IsFinitaryProjection c`
and `𝒰^∞ ≅ Fix(c)` directly (`cElementIso`), and combined with `Proposition82.elementIso` applied
to `fixedNbhd c ◁ 𝒰` (Theorem 8.5/8.6's usual bridge, `inj_comp_proj_eq_self`) gives
`fixedNbhd c ≅ 𝒰^∞` (`fixedNbhd_cCombinator_isomorphic`).

## Building `t` as a genuinely continuous self-map of `funSpace 𝒰 𝒰`

This is the technical crux: `a ↦ arrowComb a c` must be *continuous in `a`* (an element of
`funSpace 𝒰 𝒰`), not just a family of maps indexed by `a`. We build it from Table 5.5's `compC`/
`curryC`/`evalC` combinators via a joint three-variable evaluator

`R(ψ, φ, x) := c(φ(ψ(x)))`,   `ψ, φ ∈ |𝒰→𝒰|`, `x ∈ |𝒰|`,

purely as a composite of `evalMap`/`proj`/`paired`/`comp` (`RMap`) — manifestly continuous jointly
in all three arguments since `evalMap` itself is. Currying `R` twice (`curryOnceC`, then
`curryC`, giving `lamOp c : (𝒰→𝒰) → ((𝒰→𝒰) → (𝒰→𝒰))`, an element of a fourth-order function
space) recovers Definition 8.9's `lamComb a c = expMap a c` at each fixed `a` (`toApproxMap_lamOp`,
checked against `Proposition810b.toApproxMap_toElementMap_expMap`). Composing on the outside with
the *fixed* Hom-functor action `expMap jArrow iArrow` (conjugating by the fixed projection pair
`𝒰 ⇄ (𝒰→𝒰)`) produces `t := tOpMap c`, and unwinds to exactly `arrowComb a c` at every `a`
(`tOp_tOpMap`) — so `t` really is Definition 8.9's `arrowComb (-) c`, made continuous.

## Assembling the theorem

`ht_tOpMap` transports Proposition 8.10(b)'s `finitaryProjection_arrowComb` along `tOp_tOpMap` to
get Exercise 8.23's hypothesis; `Exercise823.isFinitaryProjection_fixOp` and
`Exercise823.fixedDomain_fixOp_iso_T` (instantiated at `T(a) := funSpace (fixedNbhd a)
(fixedNbhd c)`, via `arrowComb_elementIso`) hand us `D ≅ D → (fixedNbhd c) ≅ D → 𝒰^∞` for
`D := fixedNbhd (fixOp t)` (`Dsol_isomorphic_funSpace_cCombinator`). Combined with
`Exercise825Pow.pow_prod_isomorphic` (transported along `fixedNbhd c ≅ 𝒰^∞`, giving
`hVV_cCombinator : (fixedNbhd c) × (fixedNbhd c) ≅ fixedNbhd c`), `Exercise825Closing`'s abstract
closing argument finishes: `D ≅ D → D` (`exercise_8_25_main`).

**Non-triviality/universality** (`U_trianglelefteq_Dsol`): chaining `𝒰 ⊴ 𝒰^∞`
(`Exercise825Embed.trianglelefteq_iterSys`), `𝒰^∞ ≅ fixedNbhd c` (hence `⊴`), the *general* fact
`𝒱 ⊴ (𝒟 → 𝒱)` (`Exercise820.trianglelefteq_funSpace_const`, the constant-function embedding) at
`𝒱 := fixedNbhd c`, `𝒟 := D`, and `D → (fixedNbhd c) ≅ D` (from `Dsol_isomorphic_funSpace_cCombinator`,
reversed) gives `𝒰 ⊴ D`: the solution domain genuinely contains a copy of the universal domain `𝒰`,
so it is non-trivial (matching Scott's remark).

Axiom footprint: everything here mentions `U`, so — like `Definition89.lean`/`Proposition810b.lean`
— it inherits `U`'s own `Classical.choice` footprint (`⊆ {propext, Classical.choice, Quot.sound}`),
confirmed not new.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

/-! ## Building `c`, a finitary projection with `Fix(c) ≅ 𝒰^∞` -/

/-- A fixed computable presentation of `𝒰^∞ = iterSys 𝒰` (Exercise 7.15). -/
noncomputable def presentationIterU : ComputablePresentation (iterSys U) :=
  Classical.choice (iterSys_isEffectivelyGiven U_isEffectivelyGiven)

/-- **`i : 𝒰^∞ → 𝒰`**, fixed by Theorem 8.8(b) applied to `𝒰^∞`. -/
noncomputable def cInj : ApproximableMap (iterSys U) U :=
  (theorem_8_8_b_strong presentationIterU).choose

/-- **`j : 𝒰 → 𝒰^∞`**, fixed by Theorem 8.8(b) applied to `𝒰^∞`. -/
noncomputable def cProj : ApproximableMap U (iterSys U) :=
  (theorem_8_8_b_strong presentationIterU).choose_spec.choose

theorem cProj_comp_cInj : cProj.comp cInj = idMap (iterSys U) :=
  (theorem_8_8_b_strong presentationIterU).choose_spec.choose_spec.1

theorem cInj_comp_cProj_le : cInj.comp cProj ≤ idMap U :=
  (theorem_8_8_b_strong presentationIterU).choose_spec.choose_spec.2.1

/-- **`c := i ∘ j : 𝒰 → 𝒰`**, the finitary projection witnessing `𝒰^∞` inside `𝒰`. -/
noncomputable def cCombinator : ApproximableMap U U := cInj.comp cProj

theorem isRetraction_cCombinator : IsRetraction cCombinator := by
  show (cInj.comp cProj).comp (cInj.comp cProj) = cInj.comp cProj
  rw [comp_assoc, ← comp_assoc cProj cInj cProj, cProj_comp_cInj, idMap_comp]

theorem isProjection_cCombinator : IsProjection cCombinator :=
  ⟨isRetraction_cCombinator, cInj_comp_cProj_le⟩

/-- **`𝒰^∞ ≅ Fix(c)`**, from the generic projection-pair `elementIso` (Proposition 8.10(b)'s
`elementIsoOfProjectionPair`). -/
noncomputable def cElementIso :
    (iterSys U).Element ≃o {y : U.Element // cCombinator.toElementMap y = y} :=
  elementIsoOfProjectionPair cInj cProj cProj_comp_cInj rfl

theorem isFinitary_cCombinator : IsFinitary cCombinator :=
  isFinitary_of_projectionPair cInj cProj cProj_comp_cInj rfl

theorem isFinitaryProjection_cCombinator : IsFinitaryProjection cCombinator :=
  ⟨isProjection_cCombinator, isFinitary_cCombinator⟩

/-- **`fixedNbhd a ≅ Fix(a)`, for any finitary projection `a : 𝒰 → 𝒰`.** Theorem 8.6(a)'s
`inj_comp_proj_eq_self` identifies `retractionOfSubsystem (fixedNbhd_subsystem a)` with `a` itself,
transporting Proposition 8.2's `elementIso` along the identification. -/
noncomputable def fixedNbhd_elementIso_fix {a : ApproximableMap U U} (ha : IsFinitaryProjection a) :
    (fixedNbhd a).Element ≃o {y : U.Element // a.toElementMap y = y} := by
  have h := Subsystem.elementIso (fixedNbhd_subsystem a)
  unfold Subsystem.retractionOfSubsystem at h
  rwa [inj_comp_proj_eq_self ha] at h

/-- **`fixedNbhd c ≅ 𝒰^∞`.** -/
theorem fixedNbhd_cCombinator_isomorphic : fixedNbhd cCombinator ≅ᴰ iterSys U :=
  ⟨(fixedNbhd_elementIso_fix isFinitaryProjection_cCombinator).trans cElementIso.symm⟩

/-! ## The joint evaluator `R(ψ, φ, x) := c(φ(ψ(x)))`, built from `evalMap`/`proj`/`paired` -/

/-- The domain `(𝒰→𝒰) × ((𝒰→𝒰) × 𝒰)` of the joint evaluator: an element `⟨ψ, ⟨φ, x⟩⟩` packages
the varying map `ψ` (to become `a`), the curry variable `φ`, and the point `x`. -/
abbrev RDom := prod (funSpace U U) (prod (funSpace U U) U)

/-- `R(ψ, φ, x) := c(φ(ψ(x)))`, purely as a composite of `evalMap`, `proj`s and `paired` — jointly
continuous in `(ψ, φ, x)` since `evalMap` is. -/
noncomputable def RMap (c : ApproximableMap U U) : ApproximableMap RDom U :=
  c.comp ((evalMap U U).comp
    (paired
      ((proj₀ (funSpace U U) U).comp (proj₁ (funSpace U U) (prod (funSpace U U) U)))
      ((evalMap U U).comp
        (paired (proj₀ (funSpace U U) (prod (funSpace U U) U))
          ((proj₁ (funSpace U U) U).comp (proj₁ (funSpace U U) (prod (funSpace U U) U)))))))

theorem toElementMap_RMap (c : ApproximableMap U U) (ψ φ : (funSpace U U).Element) (x : U.Element) :
    (RMap c).toElementMap (pair ψ (pair φ x)) =
      c.toElementMap ((toApproxMap φ).toElementMap ((toApproxMap ψ).toElementMap x)) := by
  simp only [RMap, toElementMap_comp, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

/-! ## Currying `R` twice: `lamOp c : (𝒰→𝒰) → ((𝒰→𝒰) → (𝒰→𝒰))`, recovering `lamComb (-) c` -/

/-- First curry (peeling off `ψ`), leaving the `(φ, x)` pair bundled: an element of
`𝒰→𝒰 → funSpace ((𝒰→𝒰) × 𝒰) 𝒰`. -/
noncomputable def curryOnceC (c : ApproximableMap U U) :
    ApproximableMap (funSpace U U) (funSpace (prod (funSpace U U) U) U) :=
  curry (RMap c)

/-- Second curry (via Table 5.5's `curryC`, peeling off `φ`): `ψ ↦ (φ ↦ (x ↦ R(ψ,φ,x)))`, an
element of the fourth-order function space `(𝒰→𝒰) → ((𝒰→𝒰) → (𝒰→𝒰))`. -/
noncomputable def lamOp (c : ApproximableMap U U) :
    ApproximableMap (funSpace U U) (funSpace (funSpace U U) (funSpace U U)) :=
  (curryC (funSpace U U) U U).comp (curryOnceC c)

/-- **`lamOp c` recovers `expMap (-) c = lamComb (-) c` at every `a`.** The heart of the
continuity argument: unwinding both curry layers (`curryC_toApproxMap`, `toElementMap_curry_apply`
twice) and `RMap`'s value formula (`toElementMap_RMap`) against `expMap`'s own value formula
(`toApproxMap_toElementMap_expMap`) shows both sides send `φ` to (the element representing)
`x ↦ c(φ(a(x)))`. -/
theorem toApproxMap_lamOp (c a : ApproximableMap U U) :
    toApproxMap ((lamOp c).toElementMap (toFilter a)) = expMap a c := by
  apply ApproximableMap.ext_of_toElementMap
  intro φ
  apply (funSpaceEquiv U U).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply]
  apply ApproximableMap.ext_of_toElementMap
  intro x
  show (toApproxMap ((toApproxMap ((lamOp c).toElementMap (toFilter a))).toElementMap φ)).toElementMap x
    = (toApproxMap ((expMap a c).toElementMap φ)).toElementMap x
  rw [lamOp, toElementMap_comp, curryC_toApproxMap, toElementMap_curry_apply, curryOnceC,
    toElementMap_curry_apply, toElementMap_RMap, Sub8_6.toApproxMap_toFilter,
    toApproxMap_toElementMap_expMap, toElementMap_comp, toElementMap_comp]

/-! ## `t := tOpMap c`, conjugating `lamOp c` by the fixed pair `𝒰 ⇄ (𝒰→𝒰)` -/

/-- **`t(a) := a → c`, made continuous in `a`.** Conjugates `lamOp c`'s output by the fixed
projection pair `jArrow : 𝒰 → (𝒰→𝒰)`, `iArrow : (𝒰→𝒰) → 𝒰` (Definition 8.9), via `expMap jArrow
iArrow`. -/
noncomputable def tOpMap (c : ApproximableMap U U) :
    ApproximableMap (funSpace U U) (funSpace U U) :=
  (expMap jArrow iArrow).comp (lamOp c)

/-- **`tOp (tOpMap c) a = arrowComb a c`**, for every `a`: `t` really does implement
`a ↦ arrowComb a c`, continuously. -/
theorem tOp_tOpMap (c a : ApproximableMap U U) :
    Exercise823.tOp (tOpMap c) a = arrowComb a c := by
  show toApproxMap ((tOpMap c).toElementMap (toFilter a)) = arrowComb a c
  rw [tOpMap, toElementMap_comp, toApproxMap_toElementMap_expMap, toApproxMap_lamOp,
    expMap_eq_lamComb]
  rfl

/-- **`t` sends finitary projections to finitary projections** (Exercise 8.23's hypothesis `ht`),
via `tOp_tOpMap` and Proposition 8.10(b)'s `finitaryProjection_arrowComb`. -/
theorem ht_tOpMap (c : ApproximableMap U U) (hc : IsFinitaryProjection c) :
    ∀ a, IsFinitaryProjection a → IsFinitaryProjection (Exercise823.tOp (tOpMap c) a) := by
  intro a ha
  rw [tOp_tOpMap]
  exact finitaryProjection_arrowComb a c ha hc

/-! ## Assembling `D ≅ D → 𝒰^∞` -/

/-- Exercise 8.23's abstract correspondence `T(a) := D_a → D_c` (a domain, for each finitary
projection `a`). -/
noncomputable def TArrow (a : ApproximableMap U U) : Σ β : Type, NeighborhoodSystem β :=
  ⟨_, funSpace (fixedNbhd a) (fixedNbhd cCombinator)⟩

theorem hT_TArrow (a : ApproximableMap U U) (ha : IsFinitaryProjection a) :
    Nonempty (Exercise823.Fix (Exercise823.tOp (tOpMap cCombinator) a) ≃o
      (TArrow a).2.Element) := by
  rw [tOp_tOpMap]
  exact ⟨(arrowComb_elementIso a cCombinator ha isFinitaryProjection_cCombinator).symm⟩

/-- **`D ≅ D → 𝒰^∞` for `D := fixedNbhd (fixOp t)`.** Exercise 8.23's `fixedDomain_fixOp_iso_T`
gives `Fix(‖t‖) ≅ D → D_c`; `fixedNbhd_elementIso_fix` identifies `D`'s own element type with
`Fix(‖t‖)`, and `fixedNbhd_cCombinator_isomorphic` identifies `D_c` with `𝒰^∞`. -/
theorem Dsol_isomorphic_funSpace_cCombinator :
    fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)) ≅ᴰ
      funSpace (fixedNbhd (Exercise823.fixOp (tOpMap cCombinator))) (fixedNbhd cCombinator) := by
  have hht := ht_tOpMap cCombinator isFinitaryProjection_cCombinator
  have hFP := Exercise823.isFinitaryProjection_fixOp (tOpMap cCombinator) hht
  have h1 : Nonempty ((fixedNbhd (Exercise823.fixOp (tOpMap cCombinator))).Element ≃o
      Exercise823.Fix (Exercise823.fixOp (tOpMap cCombinator))) :=
    ⟨fixedNbhd_elementIso_fix hFP⟩
  have h2 := Exercise823.fixedDomain_fixOp_iso_T (tOpMap cCombinator) hht TArrow hT_TArrow
  exact h1.elim fun e1 => h2.elim fun e2 => ⟨e1.trans e2⟩

/-- **`fixedNbhd c × fixedNbhd c ≅ fixedNbhd c`**, transported from `Exercise825Pow.pow_prod_isomorphic`
along `fixedNbhd_cCombinator_isomorphic`. -/
theorem hVV_cCombinator :
    prod (fixedNbhd cCombinator) (fixedNbhd cCombinator) ≅ᴰ fixedNbhd cCombinator :=
  ((fixedNbhd_cCombinator_isomorphic.prod fixedNbhd_cCombinator_isomorphic).trans
    (pow_prod_isomorphic U)).trans fixedNbhd_cCombinator_isomorphic.symm

/-- **Exercise 8.25 (Scott 1981, PRG-19), main theorem.** `D ≅ D → D`, for
`D := fixedNbhd (fixOp (tOpMap cCombinator))`: a non-trivial domain isomorphic to its own function
space (see `U_trianglelefteq_Dsol` below for non-triviality). -/
theorem exercise_8_25_main :
    fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)) ≅ᴰ
      funSpace (fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)))
        (fixedNbhd (Exercise823.fixOp (tOpMap cCombinator))) :=
  funSpace_self_isomorphic Dsol_isomorphic_funSpace_cCombinator hVV_cCombinator

/-! ## Non-triviality: `𝒰 ⊴ D` -/

/-- **`𝒰 ⊴ D`**: the solution domain contains a copy of the universal domain `𝒰`, so it is
non-trivial (Scott's remark). Chains `𝒰 ⊴ 𝒰^∞` (`Exercise825Embed.trianglelefteq_iterSys`),
`𝒰^∞ ≅ fixedNbhd c`, the general constant-function embedding `𝒱 ⊴ (𝒟 → 𝒱)`
(`Exercise820.trianglelefteq_funSpace_const`), and `D → (fixedNbhd c) ≅ D`. -/
theorem U_trianglelefteq_Dsol : U ⊴ fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)) := by
  set D := fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)) with hD
  have h1 : U ⊴ iterSys U := trianglelefteq_iterSys U
  have h2 : iterSys U ⊴ fixedNbhd cCombinator :=
    ⟨fixedNbhd cCombinator, Subsystem.refl _, fixedNbhd_cCombinator_isomorphic.symm⟩
  have h3 : fixedNbhd cCombinator ⊴ funSpace D (fixedNbhd cCombinator) :=
    trianglelefteq_funSpace_const D (fixedNbhd cCombinator)
  have h4 : funSpace D (fixedNbhd cCombinator) ⊴ D :=
    ⟨D, Subsystem.refl D, Dsol_isomorphic_funSpace_cCombinator.symm⟩
  exact trianglelefteq_trans (trianglelefteq_trans (trianglelefteq_trans h1 h2) h3) h4

end Scott1980.Neighborhood

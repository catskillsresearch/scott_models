/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Theorem86
import Scott1980.Neighborhood.Theorem41
import Scott1980.Neighborhood.Exercise315
import Scott1980.Neighborhood.Exercise816

/-!
# Exercise 8.23 (Scott 1981, PRG-19, §8) — the fixed-point method really does solve `D ≅ T(D)`

> **EXERCISE 8.23.** Suppose a construct `T` on domains can be made into a computable operator
> `t : (U → U) → (U → U)` so that whenever `a : U → U` is a finitary projection, then so is `t(a)`
> and `D_{t(a)} ≅ T(D_a)`. Does it follow that `‖t‖ = fix(t)` is such that `D_{‖t‖} ≅ T(D_{‖t‖})`
> really is the initial solution of the domain equation with respect to projections? Since `t` is
> computable, will this solution be effectively given?

**Answer: yes to all three questions.** This file formalizes the two purely order-theoretic
claims in full (working over an *arbitrary* neighbourhood system `E` in place of `U` — nothing in
the argument is specific to the universal domain), and explains the computability claim in prose,
matching this codebase's existing precedent (Theorem 8.6's own computability clause, `sub`'s
Clause 3, is likewise deferred: computability needs `E` effectively given, Definition 7.1
machinery, a separate prerequisite not otherwise used here).

## Setup: `t` as a self-map of the function space, `tOp` as the induced operator on maps

Scott's `t : (U → U) → (U → U)` is modelled as an approximable **self-map of the function space**
`t : ApproximableMap (funSpace E E) (funSpace E E)` (matching how `Theorem86.lean`'s `subApprox`
itself is built) — an *element* of `funSpace E E` is (via `Theorem 3.10`'s `funSpaceEquiv`)
literally a filter representation of an approximable map `E → E`, so a continuous self-map of
`funSpace E E` is exactly Scott's "computable operator on `(E → E)`" (dropping "computable" to
"approximable", since only Theorem 4.1's *existence* of a fixed point is used for the two claims
proved here). The induced operator on actual maps is `tOp t a := toApproxMap (t.toElementMap
(toFilter a))`, and `‖t‖ := fixOp t := toApproxMap (Theorem 4.1's `t.fixElement`)` is Scott's
`fix(t)`.

## Claim 1 — `‖t‖` really is a finitary projection (`isFinitaryProjection_fixOp`)

This is the crux, and is proved by an elegant chase through **Theorem 8.6's `sub` combinator**
rather than by re-deriving any of Theorem 6.16's heavy ω-colimit-of-domains machinery:

* `sub f = f ↔ IsFinitaryProjection f` (Theorem 8.6(a)) turns "is a finitary projection" into a
  purely equational condition.
* By induction on `n`, every approximant `t.iterElem n` (Theorem 4.1(iii)'s chain `tⁿ(⊥)`) is,
  under `toApproxMap`, a finitary projection: the base case `n = 0` is the constant-bottom map
  `constMap E E.bot` (shown finitary projection directly: idempotent and `≤ I` by bare unfolding;
  finitary because its fixed-point set is the singleton `{⊥}`, order-isomorphic to the terminal
  system `𝟙` = `unitSys`); the step case is exactly hypothesis `ht`.
* Hence every `t.iterElem n` is a fixed point of `sub`, i.e. of `subFilter` (`sub` transported to
  `funSpace E E`'s own elements, Theorem 8.6(b)).
* **The key fact, already on hand in `Theorem86.lean`**: `subFilter` commutes with directed unions
  (`Sub8_6.subFilter_iSupDirected`), because `sub`'s defining formula is a *positive existential*
  in the map's relation. Since `‖t‖`'s underlying element `t.fixElement = ⊔ₙ t.iterElem n`
  (Theorem 4.2(iii)) and `subFilter` fixes every term of this directed union, `subFilter` fixes the
  union itself — i.e. `sub ‖t‖ = ‖t‖`, giving `IsFinitaryProjection ‖t‖` right back out of Theorem
  8.6(a).

This sidesteps entirely the delicate "colimit of finitary domains is finitary" argument Theorem
6.16 needs in the general categorical setting — here it is a two-line consequence of `sub` already
being known to be *continuous* on the function space.

## Claim 2 — `D_{‖t‖} ≅ T(D_{‖t‖})`, and `‖t‖` is initial with respect to projections

`‖t‖` is not merely an *approximate* limit of the chain — Theorem 4.1 makes it a *genuine* fixed
point: `tOp t (fixOp t) = fixOp t` (`tOp_fixOp`, from `toElementMap_fixElement`). Consequently,
whatever abstract correspondence `T` the hypothesis packages (modelled here as a function `T`
from maps to `Σ`-bundled domains, with `hT a : Fix(tOp t a) ≅ T(a)` for every finitary projection
`a`), instantiating at `a := ‖t‖` and rewriting `tOp t (‖t‖) = ‖t‖` on the nose gives
**`Fix(‖t‖) ≅ T(‖t‖)` unconditionally** (`fixedDomain_fixOp_iso_T`) — *not* an approximate/colimit
argument, a literal substitution, precisely because `‖t‖` solves the equation exactly rather than
in the limit.

**Initiality with respect to projections** (`fixedNbhd_fixOp_subsystem`): if `a` is *any* other
finitary projection that is a pre-fixed point of the same operator (`tOp t a ≤ a` — covering, in
particular, every *exact* alternative solution `tOp t a = a`), then Theorem 4.1's minimality
(`fixElement_le_of_toElementMap_le`) gives `‖t‖ ≤ a`, and Exercise 8.16's order-isomorphism
`a ≤ b ↔ D_a ◁ D_b` upgrades this to `D_{‖t‖} ◁ D_a` (hence certainly `D_{‖t‖} ⊴ D_a`, Lemma 6.15)
— exactly Scott's "initial solution with respect to projections".

## Claim 3 — effectively given if `t` is computable (not formalized: prose only)

Scott's own text leaves the *computability* clause of the closely analogous Theorem 8.6 (`sub` is
a computable, finitary projection when `E` is effectively given) unformalized in this codebase for
the same reason: it needs Definition 7.1's `ComputablePresentation` machinery threaded through a
directed *union* of presentations, not merely a single presentation. The expected argument (fully
analogous to Theorem 8.8(b)'s computable back-and-forth and Theorem 8.8(c)'s
`fixedNbhd_isEffectivelyGiven`, both already in this codebase) is: since `t` is computable and
`E.bot` is (trivially) computable, every approximant `t.iterElem n` is computable by a routine
induction (composition of computable maps is computable); the union defining `‖t‖` is then a
*recursively enumerable* union of computable approximants — indexed by `n : ℕ`, decidably
increasing — hence `‖t‖` itself is computable by the standard "effective limit of an effective
chain" argument (the same style of argument `Theorem88b.lean`–`Theorem88m.lean` already carry out
for the *other* effective limiting construction in this book, Theorem 8.8's back-and-forth
`Yₙ`-chain). We do not carry this out in Lean here, matching the `sub`-computability precedent.

Everything **proved** in this file (Claims 1–2) is **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap Sub8_6

namespace Exercise823

variable {α : Type} {E : NeighborhoodSystem α}

/-! ## The constant-bottom map is a finitary projection (base case of the induction) -/

/-- Every approximable map relates every consistent neighbourhood to the master (widen the master
relation's input down to `X` using `mono`, since `X ⊆ Δ` always). -/
theorem rel_master_of_mem (f : ApproximableMap E E) {X : Set α} (hX : E.mem X) :
    f.rel X E.master :=
  f.mono f.master_rel (E.sub_master hX) subset_rfl hX E.master_mem

/-- **`toApproxMap` of the function space's own bottom element is the constant-bottom map.**
Mirrors `Theorem616.lean`'s `botStrict_rel` for the (non-strict) function space `funSpace E E`. -/
theorem toApproxMap_bot_eq_constMap (E : NeighborhoodSystem α) :
    toApproxMap (funSpace E E).bot = constMap E E.bot := by
  apply ApproximableMap.ext
  intro X Y
  simp only [toApproxMap_rel, mem_bot, constMap_rel]
  constructor
  · intro h
    have hcb : constMap E E.bot ∈ step X Y := by rw [h]; trivial
    rwa [mem_step, constMap_rel, mem_bot] at hcb
  · rintro ⟨hX, rfl⟩
    exact Set.eq_univ_of_forall fun f => rel_master_of_mem f hX

theorem isRetraction_constMap_bot (E : NeighborhoodSystem α) :
    IsRetraction (constMap E E.bot) := by
  show (constMap E E.bot).comp (constMap E E.bot) = constMap E E.bot
  apply ApproximableMap.ext
  intro X Z
  simp only [comp_rel, constMap_rel, mem_bot]
  constructor
  · rintro ⟨Y, ⟨hX, rfl⟩, -, hZ⟩
    exact ⟨hX, hZ⟩
  · rintro ⟨hX, hZ⟩
    exact ⟨E.master, ⟨hX, rfl⟩, E.master_mem, hZ⟩

theorem constMap_bot_le_idMap (E : NeighborhoodSystem α) :
    constMap E E.bot ≤ idMap E := by
  rintro X Z hr
  rw [constMap_rel, mem_bot] at hr
  obtain ⟨hX, rfl⟩ := hr
  exact ⟨hX, E.master_mem, E.sub_master hX⟩

theorem isProjection_constMap_bot (E : NeighborhoodSystem α) :
    IsProjection (constMap E E.bot) :=
  ⟨isRetraction_constMap_bot E, constMap_bot_le_idMap E⟩

/-- The fixed-point set of the constant-bottom map is the singleton `{⊥}`. -/
theorem eq_bot_of_fixed_constMap_bot {y : E.Element}
    (hy : (constMap E E.bot).toElementMap y = y) : y = E.bot := by
  rw [toElementMap_constMap] at hy
  exact hy.symm

instance uniqueFixedConstMapBot :
    Unique {y : E.Element // (constMap E E.bot).toElementMap y = y} where
  default := ⟨E.bot, toElementMap_constMap E.bot E.bot⟩
  uniq := fun ⟨_y, hy⟩ => Subtype.ext (eq_bot_of_fixed_constMap_bot hy)

/-- The singleton fixed-point set of the constant-bottom map is order-isomorphic to the (also
singleton) terminal system `unitSys` (`Exercise315.lean`). -/
def finitaryWitnessEquivBot (E : NeighborhoodSystem α) :
    {y : E.Element // (constMap E E.bot).toElementMap y = y} ≃o unitSys.Element where
  toFun _ := default
  invFun _ := default
  left_inv a := (Unique.eq_default a).symm
  right_inv b := (Unique.eq_default b).symm
  map_rel_iff' := by
    intro a b
    have hab : a = b := (Unique.eq_default a).trans (Unique.eq_default b).symm
    exact iff_of_true (le_refl default) (le_of_eq hab)

theorem isFinitaryProjection_constMap_bot (E : NeighborhoodSystem α) :
    IsFinitaryProjection (constMap E E.bot) :=
  ⟨isProjection_constMap_bot E, Unit, unitSys, ⟨finitaryWitnessEquivBot E⟩⟩

/-! ## `t` as a self-map of the function space, and the induced operator `tOp` on maps -/

/-- **Scott's `t(a)`**: the operator `t : (E → E) → (E → E)` induced by an approximable self-map
`t` of the function space `funSpace E E`, applied to an actual map `a : E → E`. -/
def tOp (t : ApproximableMap (funSpace E E) (funSpace E E)) (a : ApproximableMap E E) :
    ApproximableMap E E :=
  toApproxMap (t.toElementMap (toFilter a))

theorem tOp_toApproxMap (t : ApproximableMap (funSpace E E) (funSpace E E))
    (φ : (funSpace E E).Element) : tOp t (toApproxMap φ) = toApproxMap (t.toElementMap φ) := by
  unfold tOp
  rw [toFilter_toApproxMap]

/-- **Scott's `‖t‖ = fix(t)`**, as an actual approximable map `E → E`. -/
def fixOp (t : ApproximableMap (funSpace E E) (funSpace E E)) : ApproximableMap E E :=
  toApproxMap t.fixElement

theorem iterElem_succ' (t : ApproximableMap (funSpace E E) (funSpace E E)) (n : ℕ) :
    t.iterElem (n + 1) = t.toElementMap (t.iterElem n) := by
  show (t.comp (t.iterMap n)).toElementMap (funSpace E E).bot = t.toElementMap (t.iterElem n)
  rw [toElementMap_comp]
  rfl

theorem iterElem_zero' (t : ApproximableMap (funSpace E E) (funSpace E E)) :
    t.iterElem 0 = (funSpace E E).bot := by
  show (idMap (funSpace E E)).toElementMap (funSpace E E).bot = (funSpace E E).bot
  rw [toElementMap_idMap]

/-! ## Claim 1 — `‖t‖` is a finitary projection -/

/-- **Exercise 8.23, Claim 1.** Provided `t` maps finitary projections to finitary projections,
`‖t‖ = fix(t)` really is a finitary projection. -/
theorem isFinitaryProjection_fixOp (t : ApproximableMap (funSpace E E) (funSpace E E))
    (ht : ∀ a, IsFinitaryProjection a → IsFinitaryProjection (tOp t a)) :
    IsFinitaryProjection (fixOp t) := by
  have hchain : ∀ n, IsFinitaryProjection (toApproxMap (t.iterElem n)) := by
    intro n
    induction n with
    | zero =>
      rw [iterElem_zero', toApproxMap_bot_eq_constMap]
      exact isFinitaryProjection_constMap_bot E
    | succ k ih =>
      rw [iterElem_succ', ← tOp_toApproxMap t (t.iterElem k)]
      exact ht _ ih
  have hsub : ∀ n, subFilter (t.iterElem n) = t.iterElem n := by
    intro n
    apply toApproxMap_injective
    rw [toApproxMap_subFilter]
    exact sub_eq_self_of_isFinitaryProjection (hchain n)
  have hdir : ∀ i j : ℕ, ∃ k, t.iterElem i ≤ t.iterElem k ∧ t.iterElem j ≤ t.iterElem k :=
    fun i j => ⟨max i j, iterElem_mono t (le_max_left i j), iterElem_mono t (le_max_right i j)⟩
  have hdirSub : ∀ i j : ℕ, ∃ k, subFilter (t.iterElem i) ≤ subFilter (t.iterElem k) ∧
      subFilter (t.iterElem j) ≤ subFilter (t.iterElem k) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hdir i j
    refine ⟨k, ?_, ?_⟩
    · rw [hsub i, hsub k]; exact hik
    · rw [hsub j, hsub k]; exact hjk
  have hEq : t.fixElement = iSupDirected t.iterElem hdir := by
    apply NeighborhoodSystem.Element.ext
    intro Z
    rw [mem_fixElement, mem_iSupDirected]
    simp_rw [mem_iterElem]
  have hkey : subFilter t.fixElement = t.fixElement := by
    rw [hEq, subFilter_iSupDirected t.iterElem hdir hdirSub]
    apply NeighborhoodSystem.Element.ext
    intro Z
    rw [mem_iSupDirected, mem_iSupDirected]
    simp_rw [hsub]
  show IsFinitaryProjection (toApproxMap t.fixElement)
  apply isFinitaryProjection_of_sub_eq_self
  rw [← toApproxMap_subFilter, hkey]

/-! ## Claim 2 — `‖t‖` genuinely solves the equation, and is initial with respect to projections -/

/-- **`‖t‖` is a genuine (not merely approximate) fixed point of `t`.** -/
theorem tOp_fixOp (t : ApproximableMap (funSpace E E) (funSpace E E)) :
    tOp t (fixOp t) = fixOp t := by
  show toApproxMap (t.toElementMap (toFilter (toApproxMap t.fixElement))) = toApproxMap t.fixElement
  rw [toFilter_toApproxMap, toElementMap_fixElement]

/-- The fixed-point-set ("`D_a`") of an approximable self-map, matching `IsFinitary`'s own
formulation. -/
abbrev Fix (a : ApproximableMap E E) := {y : E.Element // a.toElementMap y = y}

/-- **Exercise 8.23, Claim 2 (the domain equation).** Given any correspondence `T` (bundling, for
each map, a type and a domain over it) with `Fix(t(a)) ≅ T(a)` for every finitary projection `a`
(Scott's hypothesis `D_{t(a)} ≅ T(D_a)`), substituting the *exact* fixed point `a := ‖t‖` and using
`tOp_fixOp` gives `Fix(‖t‖) ≅ T(‖t‖)` unconditionally — no colimit/continuity argument needed,
since `‖t‖` solves the equation on the nose rather than merely in the limit. -/
theorem fixedDomain_fixOp_iso_T (t : ApproximableMap (funSpace E E) (funSpace E E))
    (ht : ∀ a, IsFinitaryProjection a → IsFinitaryProjection (tOp t a))
    (T : ApproximableMap E E → Σ β : Type, NeighborhoodSystem β)
    (hT : ∀ a, IsFinitaryProjection a → Nonempty (Fix (tOp t a) ≃o (T a).2.Element)) :
    Nonempty (Fix (fixOp t) ≃o (T (fixOp t)).2.Element) := by
  have h := hT (fixOp t) (isFinitaryProjection_fixOp t ht)
  rwa [tOp_fixOp] at h

/-- **Exercise 8.23, Claim 2 (initiality with respect to projections).** If `a` is *any* other
finitary projection that is a pre-fixed point of the same operator (`tOp t a ≤ a`, in particular
any exact alternative solution `tOp t a = a`), then `‖t‖`'s domain embeds as a literal subsystem of
`a`'s domain: `D_{‖t‖} ◁ D_a` (hence certainly `D_{‖t‖} ⊴ D_a`, Lemma 6.15) — Scott's "the initial
solution... with respect to projections". The proof is Theorem 4.1's minimality
(`fixElement_le_of_toElementMap_le`) transported through Exercise 8.16's order-isomorphism
`a ≤ b ↔ D_a ◁ D_b`. -/
theorem fixedNbhd_fixOp_subsystem (t : ApproximableMap (funSpace E E) (funSpace E E))
    (ht : ∀ a, IsFinitaryProjection a → IsFinitaryProjection (tOp t a))
    {a : ApproximableMap E E} (ha : IsFinitaryProjection a) (hpre : tOp t a ≤ a) :
    fixedNbhd (fixOp t) ◁ fixedNbhd a := by
  have hpre' : toApproxMap (t.toElementMap (toFilter a)) ≤ toApproxMap (toFilter a) := by
    show tOp t a ≤ toApproxMap (toFilter a)
    rw [toApproxMap_toFilter]
    exact hpre
  have h1 : t.toElementMap (toFilter a) ≤ toFilter a := by
    have hiff := (funSpaceEquiv E E).le_iff_le
      (x := t.toElementMap (toFilter a)) (y := toFilter a)
    rw [funSpaceEquiv_apply, funSpaceEquiv_apply] at hiff
    exact hiff.mp hpre'
  have h2 : t.fixElement ≤ toFilter a := fixElement_le_of_toElementMap_le t h1
  have hle : fixOp t ≤ a := by
    show toApproxMap t.fixElement ≤ a
    rw [← toApproxMap_toFilter a]
    exact toApproxMap_monotone h2
  exact (isFinitaryProjection_le_iff_fixedNbhd_subsystem
    (isFinitaryProjection_fixOp t ht) ha).mp hle

end Exercise823

end Scott1980.Neighborhood

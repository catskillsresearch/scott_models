/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Exercise825Unit
import Scott1980.Neighborhood.Exercise825FixedPoint

/-!
# Exercise 8.25 (Scott 1981, PRG-19, §8) — a non-trivial domain isomorphic to its own function space

> **EXERCISE 8.25.** Give an example of a *non-trivial* domain `D` (i.e. `D ≇ 𝟙`) with `D ≅ D → D`.
> [Hint: `1 → 1 = 1` is of no use. Instead, first construct a solution `D ≅ D → 𝒰^∞` (`𝒰^∞` the
> countably-infinite power of the universal domain `𝒰`), using the method of Exercise 8.23; note
> `𝒰^∞ × 𝒰^∞ ≅ 𝒰^∞`, so this reduces to a single fixed-point construction over `𝒰`. Remark that
> `𝒰 ◁ D`, hence `D` is universal (and certainly non-trivial). Finally show `D × D ≅ D`, and combine
> this with `D ≅ D → 𝒰^∞` to conclude `D ≅ D → D`. Is `D` effectively given?]

## Following Scott's hint, step by step

1. **The "obvious" solution is trivial** (`Exercise825Unit.lean`). Solving `D ≅ D → V` by the
   fixed-point method starting at the *smallest* `V = 𝟙` produces nothing: `funSpace_unitSys_isomorphic`
   proves `(𝟙 → 𝟙) ≅ 𝟙`, so the recursion is stuck at the trivial domain and never escapes it. This
   is why Scott says to change the method and start from `𝒰^∞` instead.

2. **`𝒰^∞ × 𝒰^∞ ≅ 𝒰^∞`** (`Exercise825Pow.lean`'s `pow_prod_isomorphic`, applied at `𝒰`), so the
   two-variable equation `D ≅ D → 𝒰^∞` collapses to a single self-map fixed point over `𝒰`, matching
   Exercise 8.23's setup.

3. **Solve `D ≅ D → 𝒰^∞`** (`Exercise825FixedPoint.lean`). Concretely: `𝒰^∞` is effectively given
   (Exercise 7.15), so Theorem 8.8(b) gives a projection pair `𝒰^∞ ⇄ 𝒰`; composing it gives a
   finitary projection `c : 𝒰 → 𝒰` with `Fix(c) ≅ 𝒰^∞` (`fixedNbhd_cCombinator_isomorphic`). The
   operator `t(a) := a → c` (Definition 8.9's `arrowComb (-) c`) is built as a genuinely continuous
   self-map `tOpMap c` of `funSpace 𝒰 𝒰` (the technical heart of this file: a joint
   evaluator/double-curry construction from Table 5.5's combinators, `toApproxMap_lamOp`/
   `tOp_tOpMap`), sends finitary projections to finitary projections (`ht_tOpMap`, via Proposition
   8.10(b)), and Exercise 8.23's abstract machinery (`isFinitaryProjection_fixOp`,
   `fixedDomain_fixOp_iso_T`) hands us `D ≅ D → 𝒰^∞` for `D := fixedNbhd (fixOp (tOpMap c))`
   (`Dsol_isomorphic_funSpace_cCombinator`).

4. **`𝒰 ◁ D`, hence `D` is universal and non-trivial** (`Exercise825FixedPoint.lean`'s
   `U_trianglelefteq_Dsol`). Chains `𝒰 ⊴ 𝒰^∞` (`Exercise825Embed.lean`'s `trianglelefteq_iterSys`,
   the "singleton stack" embedding), `𝒰^∞ ≅ fixedNbhd c`, the *general* constant-function embedding
   `V ⊴ (D → V)` for any domains `D`, `V` (`Exercise820.lean`'s `trianglelefteq_funSpace_const`), and
   `D → 𝒰^∞ ≅ D` (step 3, reversed). Since `𝒰` embeds as a genuine subdomain, `D` is certainly not
   the one-point domain — non-trivial, and in fact *universal* (every countable domain embeds in
   `𝒰`, hence in `D`).

5. **`D × D ≅ D`, and `D ≅ D → D`** (`Exercise825Closing.lean`'s abstract closing argument,
   instantiated at `V := fixedNbhd c` via `hVV_cCombinator : (fixedNbhd c) × (fixedNbhd c) ≅
   fixedNbhd c` transported from step 2 along `fixedNbhd c ≅ 𝒰^∞`). This is `exercise_8_25_main`
   below, the answer to the exercise.

## Is `D` effectively given?

**Yes, but this is not formalized here** — matching this codebase's existing precedent for the
*computability* clauses of the closely analogous Theorem 8.6 (`sub`) and Exercise 8.23 (`‖t‖`),
both of which defer the same argument for the same reason (see `Exercise823.lean`'s module
docstring, Claim 3). The expected argument, informally:

* `𝒰` and `𝒰^∞` are both effectively given (`U_isEffectivelyGiven`, `iterSys_isEffectivelyGiven`),
  so Theorem 8.8(b)'s back-and-forth pair `i, j` witnessing `c := i∘j` is *computable*
  (`theorem_8_8_b_strong`'s `IsComputableMap` clauses, already proved).
* Definition 8.9's `arrowComb` is built from `iArrow`/`jArrow`/`curry`/`evalMap`/`prodMap`, all
  computable when their inputs are (routine, and already implicit in how `Definition89.lean`
  builds these combinators from `theorem_8_8_b_strong`'s computable witnesses); hence `a ↦ a → c`
  is a computable operator whenever `a` is a computable finitary projection.
* By induction, every approximant `t.iterElem n` (`Exercise823.lean`'s notation) is then computable
  (composition of computable maps is computable), and `‖t‖ = fix(t) = ⊔ₙ t.iterElem n` is a
  *recursively enumerable* union of computable approximants indexed by `n : ℕ` — hence computable by
  the standard "effective limit of an effective chain" argument, the same style already carried out
  for the *other* effective limiting construction in this book (Theorem 8.8's `Yₙ`-chain,
  `Theorem88b.lean`–`Theorem88m.lean`).

Carrying this out in Lean would require threading Definition 7.1's `ComputablePresentation`
machinery through a directed union of presentations (one more layer than any single
`ComputablePresentation` construction currently in this codebase provides) — a standalone,
comparably-sized follow-up effort, left undone here exactly as `Theorem86.lean`'s `sub` and
`Exercise823.lean`'s `‖t‖` already are.

## Axiom footprint

`exercise_8_25_main` and `exercise_8_25_universal` both mention `𝒰`, so — like every other theorem
in this codebase that does — they inherit `𝒰`'s own `Classical.choice` footprint
(`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`), confirmed not new.
-/

namespace Scott1980.Neighborhood

/-- **Exercise 8.25 (Scott 1981, PRG-19), the answer.** The concrete domain
`D := fixedNbhd (fixOp (tOpMap cCombinator))` (built in `Exercise825FixedPoint.lean` by the
fixed-point method of Exercise 8.23, applied to `T(a) := a → 𝒰^∞`) satisfies `D ≅ D → D`. -/
theorem exercise_8_25 :
    fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)) ≅ᴰ
      funSpace (fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)))
        (fixedNbhd (Exercise823.fixOp (tOpMap cCombinator))) :=
  exercise_8_25_main

/-- **Exercise 8.25 (Scott 1981, PRG-19), non-triviality/universality.** The solution domain `D`
of `exercise_8_25` contains a genuine embedded copy of the universal domain `𝒰` (`𝒰 ⊴ D`), so it is
certainly not the one-point domain, and is in fact universal: every countable neighbourhood system
embeds (up to isomorphism) into `𝒰`, hence into `D`. -/
theorem exercise_8_25_universal : U ⊴ fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)) :=
  U_trianglelefteq_Dsol

end Scott1980.Neighborhood

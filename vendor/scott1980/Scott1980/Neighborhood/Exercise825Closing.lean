/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Exercise825Congr
import Scott1980.Neighborhood.Exercise315

/-!
# Exercise 8.25 (Scott 1981, PRG-19, §8), toolkit — the abstract closing argument

Scott's hint chain for a *non-trivial* solution of `D ≅ D → D` ends with an abstract algebraic
step, isolated here from the concrete construction of `D` and `V = 𝒰^∞`: given

* `hDV : D ≅ D → V` (a solution of the *auxiliary* equation, e.g. via `Exercise823`'s fixed-point
  machinery with `V = 𝒰^∞`), and
* `hVV : V × V ≅ V` (e.g. `Exercise825Pow.pow_prod_isomorphic`),

conclude first `prod_self_isomorphic : D × D ≅ D` and then
`funSpace_self_isomorphic : D ≅ D → D`.

The argument (all isomorphisms, no fixed-point theory needed at this level):

```
D × D ≅ (D → V) × (D → V)     [hDV.prod hDV]
      ≅ D → (V × V)           [funProd_isomorphic, reversed]
      ≅ D → V                 [funSpace_congr_right hVV]
      ≅ D                     [hDV.symm]
```

and then, reusing `prod_self_isomorphic : D × D ≅ D`,

```
D → D ≅ D → (D → V)           [funSpace_congr_right hDV]
      ≅ (D × D) → V           [curry_isomorphic, reversed]
      ≅ D → V                 [funSpace_congr_left prod_self_isomorphic]
      ≅ D                     [hDV.symm]
```

(so `D ≅ D → D` is the `.symm` of this last chain).

Everything is stated for abstract `D`, `V`, so it applies verbatim once the concrete `D`
(solving `D ≅ D → 𝒰^∞`) and `V := 𝒰^∞` are in hand.

Everything is **choice-free modulo `ApproximableMap.ext_of_toElementMap`**
(`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`, matching `funSpace_congr`'s budget).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {V : NeighborhoodSystem β}

/-- **Closing argument, step 1.** `D ≅ D → V` and `V × V ≅ V` imply `D × D ≅ D`. -/
theorem prod_self_isomorphic (hDV : D ≅ᴰ funSpace D V) (hVV : prod V V ≅ᴰ V) :
    prod D D ≅ᴰ D :=
  ((hDV.prod hDV).trans (funProd_isomorphic).symm).trans
    ((funSpace_congr_right hVV).trans hDV.symm)

/-- **Closing argument, step 2 (Exercise 8.25's main equation).** `D ≅ D → V` and `V × V ≅ V`
imply `D ≅ D → D`. -/
theorem funSpace_self_isomorphic (hDV : D ≅ᴰ funSpace D V) (hVV : prod V V ≅ᴰ V) :
    D ≅ᴰ funSpace D D :=
  have hDD : prod D D ≅ᴰ D := prod_self_isomorphic hDV hVV
  have step : funSpace D D ≅ᴰ D :=
    ((funSpace_congr_right hDV).trans (curry_isomorphic D D V).symm).trans
      ((funSpace_congr_left hDD).trans hDV.symm)
  step.symm

end Scott1980.Neighborhood

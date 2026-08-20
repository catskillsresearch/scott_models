/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Proposition810b

/-!
# Exercise 8.18 (Scott 1981, PRG-19)

> **Exercise 8.18.** Many of the cases of 8.10 were left unproved. Please establish these
> assertions explicitly.

Recall **Proposition 8.10**: "If `a, b : 𝒰 → 𝒰` are projections, then so are `a+b`, `a×b`, and
`a→b`. If `a` and `b` are finitary, then so are the others; for the fixed-point set of each of them
is isomorphic to the corresponding construct applied to the domains determined by `a` and `b`."

## What is formalized here

**Every case of Proposition 8.10 — for all three combinators `+`, `×`, `→`, in both halves — was
already fully established** by `Proposition810.lean` (`isProjection_sumComb`/`isProjection_prodComb`/
`isProjection_arrowComb`, assembled as `isProjection_combinators`) and `Proposition810b.lean`
(`finitaryProjection_sumComb`/`finitaryProjection_prodComb`/`finitaryProjection_arrowComb`, plus the
three explicit isomorphisms `sumComb_elementIso`/`prodComb_elementIso`/`arrowComb_elementIso`,
assembled as `finitaryProjection_combinators`). Nothing was left unproved by *this* development —
Scott's own text left several cases as reader exercises (most likely the `+` and `→` cases, which
needed genuinely new `sumMap`/`expMap` bifunctor infrastructure beyond the "obvious" `×` case, per
`Proposition810b.lean`'s docstring), but this project closed all of them while proving Proposition
8.10 itself. This file is therefore a **pure citation**, assembling Proposition 8.10's two halves
into one headline statement under Exercise 8.18's name — no new proof content.

Axiom footprint: `⊆ {propext, Classical.choice, Quot.sound}`, identical to `Proposition810.lean`/
`Proposition810b.lean` (the `Classical.choice` is `U`'s own inherited footprint, not new here).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

/-- **Exercise 8.18 (Scott 1981, PRG-19), in full: Proposition 8.10, both halves, all three
combinators.** If `a, b : 𝒰 → 𝒰` are projections, then so are `a+b`, `a×b`, `a→b`
(`isProjection_combinators`); if moreover `a, b` are finitary, then so are `a+b`, `a×b`, `a→b`
(`finitaryProjection_combinators`) — and (packaged inside `IsFinitaryProjection`'s `IsFinitary`
witness) the fixed-point set of each is isomorphic to the corresponding construct applied to `D_a`,
`D_b` (`sumComb_elementIso`/`prodComb_elementIso`/`arrowComb_elementIso` in `Proposition810b.lean`).
No case of Proposition 8.10 is left unestablished. -/
theorem exercise_8_18 {a b : ApproximableMap U U} (ha : IsProjection a) (hb : IsProjection b) :
    (IsProjection (sumComb a b) ∧ IsProjection (prodComb a b) ∧ IsProjection (arrowComb a b)) ∧
      (IsFinitaryProjection a → IsFinitaryProjection b →
        IsFinitaryProjection (sumComb a b) ∧ IsFinitaryProjection (prodComb a b) ∧
          IsFinitaryProjection (arrowComb a b)) :=
  ⟨isProjection_combinators ha hb, fun hfa hfb => finitaryProjection_combinators hfa hfb⟩

end Scott1980.Neighborhood

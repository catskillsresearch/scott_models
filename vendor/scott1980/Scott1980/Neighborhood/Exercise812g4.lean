/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Exercise812eD
import Scott1980.Neighborhood.Exercise812f
import Scott1980.Neighborhood.Exercise812g1a
import Scott1980.Neighborhood.Exercise812g1b
import Scott1980.Neighborhood.Exercise812g2

/-!
# Exercise 8.12(g)(4) (Scott 1981, PRG-19, Lecture VIII) — final assembly: `U ≅ V`

The exercise's ultimate target: `U` and `V` are effectively isomorphic. A one-line instantiation of
`Exercise812d.lean`'s generic `effectiveIso812d` (`(d)(6)`'s `EffectiveIso` assembly), fed every
concrete `U`/`V` fact this development has built:

* `(e)(d)`/`(f)`: `U_isComputableDiff`/`V_isComputableDiff`, `splitX812e`/`isComputableSplit_812e`,
  `splitX812f`/`isComputableSplit_812f`;
* `(g)(3)`: `hxSplit812e : SplitSpec' V splitX812e`, `hySplit812f : SplitSpec' U splitX812f`
  (`Exercise812eD.lean`/`Exercise812f.lean`, completed above);
* `(c)`: `U_isPositive`/`U_diffClosed`/`U_noMinimal`, `V_isPositive`/`V_diffClosed`/`V_noMinimal`;
* `(g)(1)`: `U_master_nonempty`/`UX_zero`, `V_master_nonempty`/`VX_zero`;
* `(g)(2)`: `U_isComputableUnion`, `V_isComputableUnion`.

No new proof content — every subgoal `effectiveIso812d` demands was already discharged by one of
the above. -/

namespace Scott1980.Neighborhood

open Domain.Recursive NeighborhoodSystem Exercise718

/-- **Exercise 8.12, completed in full**: `U` and `V` are effectively isomorphic
neighbourhood systems. -/
noncomputable def effectiveIso812_UV : EffectiveIso UComputablePresentation VComputablePresentation :=
  effectiveIso812d UComputablePresentation VComputablePresentation U_isComputableDiff
    V_isComputableDiff splitX812e isComputableSplit_812e splitX812f isComputableSplit_812f
    U_isPositive U_diffClosed U_noMinimal hxSplit812e V_isPositive V_diffClosed V_noMinimal
    hySplit812f U_master_nonempty V_master_nonempty U_isComputableUnion V_isComputableUnion UX_zero
    VX_zero

end Scott1980.Neighborhood

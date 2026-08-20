/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Exercise812e
import Scott1980.Neighborhood.UBisection2
import Scott1980.Neighborhood.VDiff

/-!
# Exercise 8.12(f) (Scott 1981, PRG-19, Lecture VIII) — `V` satisfies the extension property
relative to `U`

The mirror image of `Exercise812eD.lean`'s `8.12(e)`: there `U` was the *prober* against `V`'s
canonical bisection (`SplitV.lean`'s `B812e`); here `V` is the *prober* against `U`'s canonical
bisection. Given `(e)(c)`'s generic `splitFromBisection`/`isComputableSplit_ofBisection`
(`Exercise812e.lean`), this is a one-line instantiation, fed:

* `VComputablePresentation` (`VComputablePresentation.lean`) as the prober `P`;
* `V_isComputableDiff` (`VDiff.lean`) as `P`'s `IsComputableDiff` witness — the missing
  prerequisite this development had to supply first (`U`'s side, `Udiff`/`U_isComputableDiff`, was
  already built for `(e)(d)`, but `V`'s side had never been instantiated);
* `UBisection2` (`UBisection2.lean`) as the target `U`'s `ComputableBisection` — **not**
  `SplitU.lean`'s `splitULeft`/`splitURight`, which split at the midpoint of `canonCode n`'s *first*
  presenting pair and so fail `ComputableBisection`'s `left_congr`/`right_congr` (two different
  canonical presenting lists of the same `U`-neighbourhood can have different first pairs). `UBisection2`
  instead splits at the midpoint of the presented set's own intrinsic `(min, max)` — genuine
  invariants of the set, not of its presentation — restoring well-definedness at no cost to any of
  `(e)(c)`'s other requirements.
* `V`'s already-`Pass` `IsPositive`/`NoMinimal`/`DiffClosed` facts (`Exercise812c.lean`), needed only
  for `isComputableSplit_ofBisection`'s correctness obligations (`(e)(c)`'s own congruence lemmas),
  exactly mirroring `(e)(d)`'s use of `U`'s analogous facts.
-/

namespace Scott1980.Neighborhood

open Domain.Recursive NeighborhoodSystem

/-- **`splitX812f`: the exercise's literal target split**, `V` as prober against `U`'s canonical
bisection (`UBisection2`). -/
noncomputable def splitX812f : Set ℕ → Set ℚ → Set ℕ → Set ℚ × Set ℚ :=
  ComputableBisection.splitFromBisection VComputablePresentation V_isComputableDiff UBisection2
    U_noMinimal

/-- **Exercise 8.12(f), completed in full**: `splitX812f` satisfies `IsComputableSplit`, the
mirror image of `Exercise812eD.lean`'s `isComputableSplit_812e`. `noncomputable def`, not
`theorem` — `IsComputableSplit` is a data-carrying structure (its `posIdx`/`negIdx` fields are
`ℕ`-valued functions), exactly as `isComputableSplit_812e` itself. -/
noncomputable def isComputableSplit_812f :
    IsComputableSplit VComputablePresentation UComputablePresentation splitX812f :=
  ComputableBisection.isComputableSplit_ofBisection VComputablePresentation V_isComputableDiff
    UBisection2 U_noMinimal V_isPositive V_noMinimal V_diffClosed

/-- **`8.12(g)(3)`, `V`-as-prober half**: `splitX812f` also satisfies `SplitSpec'`, the mirror
image of `Exercise812eD.lean`'s `hxSplit812e`. The extra hypothesis it needs, `∀ j, UX j ≠ ∅`, is
immediate from `U_mem_UX`/`U.mem`'s own `X.Nonempty` conjunct (`Definition87.lean` line 96). -/
theorem hySplit812f : SplitSpec' U splitX812f :=
  ComputableBisection.splitFromBisection_isSplitSpec' VComputablePresentation V_isComputableDiff
    UBisection2 U_noMinimal V_isPositive V_noMinimal V_diffClosed
    (fun j => (U_mem_UX j).2.1.ne_empty)

end Scott1980.Neighborhood

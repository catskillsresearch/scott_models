/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Theorem88f

/-!
# Theorem 8.8(b)(viii) — final assembly

`Theorem88e.lean` (Part 7(3)) built `D'' := DprimeUCode P`, the isomorphism `D ≅ᴰ D''`
(`isomorphic_DprimeUCode`), the subsystem relation `D'' ◁ U` (`DprimeUCode_subsystem`), and `D''`'s
own `ComputablePresentation` (`DprimeUCodePresentation`); `Theorem88f.lean` (Part 7(4)) showed the
projection pair witnessing `D'' ◁ U` (Proposition 6.12's `inj`/`proj`) is computable relative to
`DprimeUCodePresentation`/`UComputablePresentation`
(`DprimeUCode_projectionPair_isComputable`). This file packages all of it into the single headline
statement of **Theorem 8.8(b)**: if `D` is effectively given, the projection pair witnessing
`D ⊴ U` (Theorem 8.8(a)) can be taken computable.

No new mathematical content — every ingredient already exists; this is exactly `theorem_8_8_a`'s
statement (`Theorem88a.lean`) with `D'` replaced by a presented `D'` and the projection pair
additionally asserted computable.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem Domain.Recursive

/-- **Theorem 8.8(b) (Scott 1981, PRG-19), final assembly.** If `D` is effectively given (via a
`ComputablePresentation P`), the general universality of `U` (Theorem 8.8(a)) can be witnessed by a
`D' : NeighborhoodSystem ℚ` that is *itself* effectively given (`P' : ComputablePresentation D'`),
isomorphic to `D`, a subsystem of `U`, **and** whose projection pair `i := (D' ◁ U).inj`,
`j := (D' ◁ U).proj` (Proposition 6.12) is computable in both directions relative to `P'` and `U`'s
own presentation `UComputablePresentation`. -/
theorem theorem_8_8_b {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D) :
    ∃ (D' : NeighborhoodSystem ℚ) (P' : ComputablePresentation D') (h : D' ◁ U),
      (D ≅ᴰ D') ∧
        IsComputableMap P' UComputablePresentation h.inj ∧
        IsComputableMap UComputablePresentation P' h.proj :=
  ⟨DprimeUCode P, DprimeUCodePresentation P, DprimeUCode_subsystem P,
    isomorphic_DprimeUCode P, DprimeUCode_inj_isComputableMap P, DprimeUCode_proj_isComputableMap P⟩

end Scott1980.Neighborhood

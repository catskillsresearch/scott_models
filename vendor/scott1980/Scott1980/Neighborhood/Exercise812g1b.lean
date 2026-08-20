/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.LevelSetPrimrec

/-!
# Exercise 8.12(g)(1)(b) — the `V`-side small assembly prerequisites

Two small facts `effectiveIso812d` (`Exercise812d.lean`) needs beyond `(c)`/`(d)`/`(e)`/`(f)`'s own
headline lemmas, for the `V` side: `V.master.Nonempty` (`hD₁mne`) and `VX 0 = V.master` (`hY0`).

Mirrors `Exercise812g1a.lean`'s `U`-side facts exactly, but along `V`'s bitmask representation:
`V.master.Nonempty` is immediate from `V.master = Set.univ`; `VX_zero` unfolds `canonIdx 0` — since
`Nat.unpair 0 = (0, 0)` and `levelSet 0 0 = ∅` (no bits set in `0`), `canonIdx` hits its own
empty-input fallback branch (`canonIdx_eq_master_of_empty`), landing on `VmasterIdx`, whose
`VX`-image is already known to be `V.master` (`VX_VmasterIdx`).
-/

namespace Scott1980.Neighborhood

open Domain.Recursive NeighborhoodSystem

/-- `hD₁mne` for `V`: the master neighbourhood `V.master = Set.univ` is non-empty. -/
theorem V_master_nonempty : V.master.Nonempty := Set.univ_nonempty

/-- `levelSet 0 0 = ∅`: at level `0`, mask `0` has no set bits. -/
theorem levelSet_zero_zero : levelSet 0 0 = ∅ := by
  ext n; simp [levelSet, Nat.zero_testBit]

/-- `hY0`: index `0` presents `V`'s master neighbourhood. `Nat.unpair 0 = (0, 0)` and
`levelSet 0 0 = ∅`, so `canonIdx 0` falls back to `VmasterIdx = Nat.pair 0 1`
(`canonIdx_eq_master_of_empty`), whose `VX`-image is `V.master` (`VX_VmasterIdx`). -/
theorem VX_zero : VX 0 = V.master := by
  have hc0 : canonIdx 0 = VmasterIdx :=
    canonIdx_eq_master_of_empty (by rw [Nat.unpair_zero]; exact levelSet_zero_zero)
  rw [← VX_canonIdx 0, hc0]
  exact VX_VmasterIdx

end Scott1980.Neighborhood

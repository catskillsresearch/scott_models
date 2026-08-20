/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.UComputablePresentation

/-!
# Exercise 8.12(g)(1)(a) — the `U`-side small assembly prerequisites

Two small facts `effectiveIso812d` (`Exercise812d.lean`) needs beyond `(c)`/`(d)`/`(e)`/`(f)`'s own
headline lemmas, for the `U` side: `U.master.Nonempty` (`hD₀mne`) and `UX 0 = U.master` (`hX0`).

Both are short and mechanical, reusing existing machinery with no new mathematical content:
`U.master.Nonempty` is immediate from `U.master = Set.Ico 0 1`; `UX_zero` unfolds `UX_eq` at `n = 0`
(`decodeQPairList 0 = []` via `decodeList_zero`), so `canonList` hits its own empty-input fallback
branch (`canonList_eq_of_filter_eq_nil`), landing on the same `[(0,1)] ↦ U.master` computation
`U_mem_presentedIntervals_canonList` already performs inline.
-/

namespace Scott1980.Neighborhood

open Domain.Recursive NeighborhoodSystem

/-- `hD₀mne` for `U`: the master neighbourhood `U.master = Set.Ico 0 1` is non-empty. -/
theorem U_master_nonempty : U.master.Nonempty := ⟨0, by norm_num [U]⟩

/-- `hX0`: index `0` presents `U`'s master neighbourhood. `decodeQPairList 0 = []`
(`decodeList_zero`), so `canonList` falls back to its `[(0,1)]` branch, which presents
`U.master` exactly as in `U_mem_presentedIntervals_canonList`. -/
theorem UX_zero : UX 0 = U.master := by
  rw [UX_eq]
  have hL : decodeQPairList 0 = [] := by
    unfold decodeQPairList; rw [decodeList_zero]; rfl
  rw [hL, canonList_eq_of_filter_eq_nil (by simp), presentedIntervals_cons, presentedIntervals_nil,
    Set.union_empty]
  rfl

end Scott1980.Neighborhood

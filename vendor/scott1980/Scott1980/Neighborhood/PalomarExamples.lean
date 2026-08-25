/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Theorem88a
import Scott1980.Neighborhood.Example15
import Scott1980.Neighborhood.Exercise722Regular

/-!
# Palomar example embeddings

Concrete countable neighbourhood systems that instantiate `theorem_8_8`.
-/

namespace Scott1980.Neighborhood.Example15

/-- **New corollary for Example 1.5.** The finite powerset system is countable, so the first
sentence of Theorem 8.8 applies. Scott does not separately state this embedding. -/
theorem P4_embeds : neighborhoodSystem ⊴ U :=
  theorem_8_8 neighborhoodSystem

end Scott1980.Neighborhood.Example15

namespace Scott1980.Neighborhood.Exercise722

/-- Countability of the neighbourhoods of `S`, via the `SExpr` presentation.
Picking a preimage uses Mathlib's `Surjective.countable` (hence `Classical.choice`);
the syntax `SExpr` itself is countable choice-free. -/
instance Ssys_countable : Countable {S : Set (List Bool) // Ssys.mem S} := by
  classical
  let f (e : SExpr) : {S : Set (List Bool) // InS S} :=
    if h : (denote e).Nonempty then ⟨denote e, InS_denote_of_nonempty h⟩
    else ⟨Set.univ, InS.univ⟩
  have : Countable {S : Set (List Bool) // InS S} :=
    Function.Surjective.countable (f := f) fun ⟨X, hX⟩ => by
      obtain ⟨e, he⟩ := InS_exists_denote hX
      refine ⟨e, ?_⟩
      have hne : (denote e).Nonempty := he.symm ▸ hX.nonempty
      dsimp [f]
      rw [dif_pos hne]
      exact Subtype.ext he
  exact Countable.of_equiv ({S : Set (List Bool) // InS S})
    (Equiv.subtypeEquivRight fun _ => Ssys_mem.symm)

/-- **New corollary for Exercise 7.22.** Countability is `Ssys_countable` (via `SExpr`), so the
first sentence of Theorem 8.8 applies. Scott does not separately state this embedding. -/
theorem Ssys_embeds : Ssys ⊴ U :=
  theorem_8_8 Ssys

end Scott1980.Neighborhood.Exercise722

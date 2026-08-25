/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Basic
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-!
# Example 1.5 (Scott 1981, PRG-19, §1)

Scott's fourth worked example: tokens `Δ = {0, 1, 2, 3}` and `𝒟` the family of **all non-empty
subsets** of `Δ`.

> This system is a direct generalization of Example 1.2 … The verification that the present `𝒟`
> is a neighbourhood system rests on nothing more than the remark that sets are consistent in `𝒟`
> iff they have a non-empty intersection.

We encode tokens as `Fin 4`, take `mem X := X.Nonempty`, and `master := Set.univ`. Condition (ii)
of Definition 1.1 is immediate: a consistency witness `Z ⊆ X ∩ Y` that is itself non-empty makes
`X ∩ Y` non-empty.

* **Example 1.5** — `neighborhoodSystem`.
* **Factoid 1.5a** — `consistent_iff_inter_nonempty`: a finite prefix is consistent in `𝒟` iff its
  intersection is non-empty (Scott's "remark").

Unlike Examples 1.2–1.4 this construction needs no `fin_cases`/`decide`: it is `Set.Nonempty`
bookkeeping, so it audits **constructive** (`[propext, Quot.sound]`).
-/

namespace Scott1980.Neighborhood.Example15

open NeighborhoodSystem

/-- Tokens for Example 1.5: `Δ = {0, 1, 2, 3}`. -/
abbrev Token := Fin 4

/-- The master neighbourhood `Δ = {0, 1, 2, 3}`. -/
def master : Set Token := Set.univ

/-- Membership: the non-empty subsets of `Δ`. -/
def P4Mem (X : Set Token) : Prop := X.Nonempty

/-- `Δ` is non-empty. -/
theorem P4_master_mem : P4Mem master := by
  rw [master]; exact Set.univ_nonempty

/-- The master token set itself is non-empty. -/
theorem P4_master_nonempty : master.Nonempty := by
  exact ⟨0, Set.mem_univ 0⟩

/-- A non-empty witness inside `X ∩ Y` shows the intersection is a neighbourhood. -/
theorem P4_inter_mem {X Y Z : Set Token} (_hX : P4Mem X) (_hY : P4Mem Y)
    (hZ : P4Mem Z) (hZsub : Z ⊆ X ∩ Y) : P4Mem (X ∩ Y) :=
  hZ.mono hZsub

/-- Every neighbourhood is a subset of `Δ`. -/
theorem P4_sub_master {X : Set Token} (_h : P4Mem X) : X ⊆ master :=
  Set.subset_univ _

/-- **Example 1.5.** The neighbourhood system of all non-empty subsets of `Δ = {0,1,2,3}`. -/
def neighborhoodSystem : NeighborhoodSystem Token where
  mem := P4Mem
  master := master
  master_nonempty := P4_master_nonempty
  master_mem := P4_master_mem
  inter_mem := P4_inter_mem
  sub_master := P4_sub_master

/-- The neighbourhoods of Example 1.5 are exactly the non-empty subsets. -/
theorem mem_iff_nonempty (X : Set Token) : neighborhoodSystem.mem X ↔ X.Nonempty := Iff.rfl

/-- The neighbourhoods of Example 1.5 are a finite family, hence countable. -/
instance P4_countable : Countable {S : Set Token // neighborhoodSystem.mem S} :=
  inferInstance

/-- **Factoid 1.5a (Scott 1981, PRG-19).** In Example 1.5, "sets are consistent in `𝒟` iff they
have a non-empty intersection": a finite prefix `X₀, …, Xₙ₋₁` is consistent exactly when its
intersection `⋂_{i<n} Xᵢ` is non-empty. -/
theorem consistent_iff_inter_nonempty (X : ℕ → Set Token) (n : ℕ) :
    neighborhoodSystem.Consistent X n ↔ (neighborhoodSystem.interUpTo X n).Nonempty := by
  constructor
  · rintro ⟨Z, hZ, hsub⟩
    obtain ⟨z, hz⟩ := hZ
    exact ⟨z, hsub hz⟩
  · intro h
    exact ⟨_, h, subset_rfl⟩

end Scott1980.Neighborhood.Example15

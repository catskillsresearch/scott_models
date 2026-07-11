import Mathlib.Order.Hom.Basic
import Scott1972.ContinuousLattice.WayBelow
import Scott1980.Neighborhood.Basic

/-!
# Continuous lattices → neighbourhood systems (1972 → 1980)

For a continuous lattice `D`, Scott’s way-below neighbourhoods
`↟a = { z | a ≪ z }` form a `NeighborhoodSystem` on token set `D`.

Under `IsContinuousLattice D`, points embed as principal filters
`{ ↟a | a ≪ x }` with retraction by directed supremum, giving an
order-embedding `D ↪o |𝒟|`.

The 1972 `≪` development is classical (Scott topology).
-/

namespace ScottModels

open Scott1972.ContinuousLattice
open scoped Scott1972.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

/-- `↟a = { z | a ≪ z }`. -/
def wayBelowUp (a : D) : Set D := {z | a ≪ z}

theorem wayBelowUp_bot : wayBelowUp (⊥ : D) = (Set.univ : Set D) := by
  ext z
  exact ⟨fun _ => trivial, fun _ => bot_wayBelow z⟩

theorem wayBelowUp_inter (a b : D) :
    wayBelowUp a ∩ wayBelowUp b = wayBelowUp (a ⊔ b) := by
  ext z
  constructor
  · exact fun ⟨ha, hb⟩ => WayBelow.sup ha hb
  · intro h
    exact ⟨WayBelow.le_trans le_sup_left h, WayBelow.le_trans le_sup_right h⟩

/-- Neighbourhood system of all `↟a`. -/
def toNeighborhoodSystem : Scott1980.Neighborhood.NeighborhoodSystem D where
  mem X := ∃ a : D, X = wayBelowUp a
  master := Set.univ
  master_mem := ⟨⊥, wayBelowUp_bot.symm⟩
  inter_mem := by
    intro X Y _Z hX hY _hZ _hZsub
    obtain ⟨a, rfl⟩ := hX
    obtain ⟨b, rfl⟩ := hY
    exact ⟨a ⊔ b, wayBelowUp_inter a b⟩
  sub_master := fun {_} _ => Set.subset_univ _

/-- Principal filter of `↟`-neighbourhoods at `x`. -/
def toFilter (x : D) :
    (toNeighborhoodSystem : Scott1980.Neighborhood.NeighborhoodSystem D).Element where
  mem U := ∃ a : D, U = wayBelowUp a ∧ a ≪ x
  sub := by
    intro U h
    obtain ⟨a, ⟨rfl, _⟩⟩ := h
    exact ⟨a, rfl⟩
  master_mem := ⟨⊥, wayBelowUp_bot.symm, bot_wayBelow x⟩
  inter_mem := by
    intro U V hU hV
    obtain ⟨a, ⟨rfl, ha⟩⟩ := hU
    obtain ⟨b, ⟨rfl, hb⟩⟩ := hV
    exact ⟨a ⊔ b, ⟨wayBelowUp_inter a b, WayBelow.sup ha hb⟩⟩
  up_mem := by
    intro U V hU hV hUV
    obtain ⟨a, ⟨rfl, ha⟩⟩ := hU
    obtain ⟨b, rfl⟩ := hV
    exact ⟨b, ⟨rfl, hUV ha⟩⟩

theorem toFilter_mono {x y : D} (hxy : x ≤ y) : toFilter x ≤ toFilter y := by
  intro U hU
  obtain ⟨a, ⟨rfl, ha⟩⟩ := hU
  exact ⟨a, ⟨rfl, ha.trans_le hxy⟩⟩

theorem mem_wayBelowUp_toFilter {x a : D} :
    (toFilter x).mem (wayBelowUp a) ↔ a ≪ x := by
  constructor
  · intro h
    obtain ⟨b, ⟨heq, hb⟩⟩ := h
    have : x ∈ wayBelowUp b := hb
    rwa [← heq] at this
  · intro ha
    exact ⟨a, ⟨rfl, ha⟩⟩

section Continuous

variable (hD : IsContinuousLattice D)
include hD

/-- Retraction: `⊔ { a | ↟a ∈ f }`. -/
noncomputable def ofFilter
    (f : (toNeighborhoodSystem : Scott1980.Neighborhood.NeighborhoodSystem D).Element) : D :=
  sSup {a : D | f.mem (wayBelowUp a)}

theorem ofFilter_toFilter (x : D) : ofFilter (toFilter x) = x := by
  change sSup {a : D | (toFilter x).mem (wayBelowUp a)} = x
  have hset : {a : D | (toFilter x).mem (wayBelowUp a)} = {a | a ≪ x} := by
    ext a
    exact mem_wayBelowUp_toFilter
  rw [hset, hD.sSup_wayBelow x]

theorem toFilter_injective :
    Function.Injective
      (toFilter :
        D → (toNeighborhoodSystem : Scott1980.Neighborhood.NeighborhoodSystem D).Element) := by
  intro x y h
  rw [← ofFilter_toFilter hD x, ← ofFilter_toFilter hD y, h]

/-- Order-embedding of a continuous lattice into its `↟`-neighbourhood domain. -/
noncomputable def domainEmbedding :
    D ↪o (toNeighborhoodSystem : Scott1980.Neighborhood.NeighborhoodSystem D).Element where
  toFun := toFilter
  inj' := toFilter_injective hD
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      have : ofFilter (toFilter x) ≤ ofFilter (toFilter y) := by
        refine sSup_le fun a ha => ?_
        have ha' : a ≪ x := mem_wayBelowUp_toFilter.mp ha
        exact le_sSup (h (wayBelowUp a) ⟨a, ⟨rfl, ha'⟩⟩)
      simpa [ofFilter_toFilter hD] using this
    · exact fun hxy => toFilter_mono hxy

end Continuous

end ContinuousLatticeToNeighborhood

/-- Blueprint name. -/
abbrev continuousLattice_to_neighborhoodSystem {D : Type*} [CompleteLattice D]
    (_hD : IsContinuousLattice D) : Scott1980.Neighborhood.NeighborhoodSystem D :=
  ContinuousLatticeToNeighborhood.toNeighborhoodSystem

end ScottModels

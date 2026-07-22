/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott_models
-/

import Mathlib.Order.Hom.Basic
import Scott1972.ContinuousLattice.WayBelow
import Scott1980.Neighborhood.Basic

/-!
# Continuous lattices → neighbourhood systems (1972 → 1980)

For a continuous lattice `D`, Scott’s way-below neighbourhoods
`↟a = { z | a ≪ z }` form a `NeighborhoodSystem` on token set `D`.

Arbitrary filters need not be principal (`{ ↟a | a ≤ x }` is a filter with
`ofFilter = x` but properly contains `toFilter x`). The correct domain is the
**round** filters: `↟a ∈ f` implies `∃ b, a ≪ b ∧ ↟b ∈ f`. Under
`IsContinuousLattice`, `D ≃o` round filters via `toFilter` / `ofFilter`.
-/

namespace ScottModels

open Scott1972.ContinuousLattice
open Scott1980.Neighborhood
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

theorem wayBelowUp_anti {a b : D} (hab : a ≤ b) :
    wayBelowUp b ⊆ wayBelowUp a :=
  fun _ h => WayBelow.le_trans hab h

/-- Neighbourhood system of all `↟a`. -/
def toNeighborhoodSystem : NeighborhoodSystem D where
  mem X := ∃ a : D, X = wayBelowUp a
  master := Set.univ
  master_mem := ⟨⊥, wayBelowUp_bot.symm⟩
  inter_mem := by
    intro X Y _Z hX hY _hZ _hZsub
    obtain ⟨a, rfl⟩ := hX
    obtain ⟨b, rfl⟩ := hY
    exact ⟨a ⊔ b, wayBelowUp_inter a b⟩
  sub_master := fun {_} _ => Set.subset_univ _

/-- Filter of the `↟`-neighbourhood system on `D`. -/
abbrev Filter : Type _ :=
  (toNeighborhoodSystem : NeighborhoodSystem D).Element

/-- Principal filter of `↟`-neighbourhoods at `x`. -/
def toFilter (x : D) : Filter (D := D) where
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

/-- Roundness: `↟a ∈ f` is witnessed by a finer code `b` with `a ≪ b`. -/
def IsRound (f : Filter (D := D)) : Prop :=
  ∀ {a : D}, f.mem (wayBelowUp a) → ∃ b : D, a ≪ b ∧ f.mem (wayBelowUp b)

/-- Codes whose `↟`-neighbourhoods lie in the filter. -/
def codes (f : Filter (D := D)) : Set D :=
  {a : D | f.mem (wayBelowUp a)}

theorem mem_codes_iff {f : Filter (D := D)} {a : D} :
    a ∈ codes f ↔ f.mem (wayBelowUp a) :=
  Iff.rfl

theorem bot_mem_codes (f : Filter (D := D)) : (⊥ : D) ∈ codes f := by
  have : f.mem (wayBelowUp (⊥ : D)) := by
    rw [wayBelowUp_bot]
    exact f.master_mem
  exact this

theorem codes_nonempty (f : Filter (D := D)) : (codes f).Nonempty :=
  ⟨⊥, bot_mem_codes f⟩

theorem codes_directed (f : Filter (D := D)) : DirectedOn (· ≤ ·) (codes f) := by
  intro a ha b hb
  refine ⟨a ⊔ b, ?_, le_sup_left, le_sup_right⟩
  have : f.mem (wayBelowUp a ∩ wayBelowUp b) := f.inter_mem ha hb
  rwa [wayBelowUp_inter] at this

theorem codes_lower (f : Filter (D := D)) {a b : D} (hba : b ≤ a)
    (ha : a ∈ codes f) : b ∈ codes f :=
  f.up_mem ha ⟨b, rfl⟩ (wayBelowUp_anti hba)

/-- Retraction: `⊔` of codes present in the filter. -/
noncomputable def ofFilter (f : Filter (D := D)) : D :=
  sSup (codes f)

theorem mem_wayBelowUp_ofFilter_of_round {f : Filter (D := D)} (hr : IsRound f) {a : D} :
    f.mem (wayBelowUp a) ↔ a ≪ ofFilter f := by
  constructor
  · intro ha
    obtain ⟨b, hab, hb⟩ := hr ha
    exact (wayBelow_sSup_iff (codes_nonempty f) (codes_directed f)).2 ⟨b, hb, hab⟩
  · intro ha
    obtain ⟨b, hbS, hab⟩ := (wayBelow_sSup_iff (codes_nonempty f) (codes_directed f)).1 ha
    exact f.up_mem hbS ⟨a, rfl⟩ (wayBelowUp_anti hab.le)

theorem toFilter_ofFilter {f : Filter (D := D)} (hr : IsRound f) :
    toFilter (ofFilter f) = f := by
  refine NeighborhoodSystem.Element.ext (V := toNeighborhoodSystem) fun U => ?_
  constructor
  · intro hU
    obtain ⟨a, ⟨rfl, ha⟩⟩ := hU
    exact (mem_wayBelowUp_ofFilter_of_round hr).2 ha
  · intro hU
    obtain ⟨a, rfl⟩ := f.sub hU
    refine ⟨a, ⟨rfl, ?_⟩⟩
    exact (mem_wayBelowUp_ofFilter_of_round hr).1 hU

section Continuous

variable (hD : IsContinuousLattice D)
include hD

theorem toFilter_isRound (x : D) : IsRound (toFilter x) := by
  intro a ha
  have ha' : a ≪ x := mem_wayBelowUp_toFilter.mp ha
  obtain ⟨b, hab, hbx⟩ := wayBelow_interpolate hD ha'
  exact ⟨b, hab, mem_wayBelowUp_toFilter.mpr hbx⟩

theorem ofFilter_toFilter (x : D) : ofFilter (toFilter x) = x := by
  have hset : codes (toFilter x) = {a : D | a ≪ x} := by
    ext a
    exact mem_wayBelowUp_toFilter
  change sSup (codes (toFilter x)) = x
  rw [hset, hD.sSup_wayBelow x]

/-- Round filters of the `↟`-system. -/
abbrev RoundFilter : Type _ :=
  { f : Filter (D := D) // IsRound f }

/-- Order-isomorphism: continuous lattice ↔ round `↟`-filters. -/
noncomputable def domainOrderIso : D ≃o RoundFilter (D := D) where
  toFun x := ⟨toFilter x, toFilter_isRound hD x⟩
  invFun f := ofFilter (D := D) f.1
  left_inv x := ofFilter_toFilter hD x
  right_inv f := Subtype.ext (toFilter_ofFilter f.2)
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      have : ofFilter (toFilter x) ≤ ofFilter (toFilter y) := by
        refine sSup_le fun a ha => ?_
        have ha' : a ≪ x := mem_wayBelowUp_toFilter.mp ha
        exact le_sSup (h (wayBelowUp a) ⟨a, ⟨rfl, ha'⟩⟩)
      simpa [ofFilter_toFilter hD] using this
    · intro hxy
      exact toFilter_mono hxy

/-- Order-embedding into all filters (forgets roundness). -/
noncomputable def domainEmbedding :
    D ↪o Filter (D := D) where
  toFun := toFilter
  inj' := by
    intro x y h
    rw [← ofFilter_toFilter hD x, ← ofFilter_toFilter hD y, h]
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
    (_hD : IsContinuousLattice D) : NeighborhoodSystem D :=
  ContinuousLatticeToNeighborhood.toNeighborhoodSystem

end ScottModels

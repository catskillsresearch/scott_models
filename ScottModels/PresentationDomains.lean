/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott_models
-/

import Mathlib.Order.Hom.Basic
import ScottModels.InfoSysToNeighborhood
import ScottModels.InfoSysToIdealCompletion
import ScottModels.NeighborhoodToInfoSys
import ScottModels.ContinuousLatticeToNeighborhood
import ScottModels.IdealCompletionToContinuousLattice

/-!
# Presentation domain equivalences

## InfoSys / neighbourhood / ideal (constructive)

For any information system `A`:
`|A| ≃o` basic-open neighbourhood filters ≃o `Ideal (FiniteElement A)`.

Under a decidable `NbhdBasis`, the same triangle starts from `|𝒟|`.

## Continuous lattices (1972 corner)

Points of a continuous lattice `D` are **round** `↟`-filters, not arbitrary filters:
`D ≃o RoundFilter`. With `DecidableEq D`, the `↟`-system admits an `NbhdBasis`,
so round filters transport to a subtype of the induced InfoSys domain (and thence
into the ideal-completion triangle). The full (non-round) `|𝒟|` / `|A|` is properly
larger.
-/

namespace ScottModels

open Scott1982
open Scott1972.ContinuousLattice
open Scott1980.Neighborhood
open Order
open scoped Scott1972.ContinuousLattice
open ContinuousLatticeToNeighborhood

variable {α : Type*} [DecidableEq α]

/-- Neighbourhood filters of `|A|` ↔ ideals of finite elements (via `|A|`). -/
noncomputable def neighborhood_ideal_iso (A : InfoSys α) :
    (InfoSysToNeighborhood.toNeighborhoodSystem A).Element ≃o
      Ideal (InfoSysToIdealCompletion.FiniteElement A) :=
  (InfoSysToNeighborhood.domainOrderIso A).symm.trans
    (InfoSysToIdealCompletion.domainOrderIso A)

variable {ι β : Type*} [DecidableEq ι]

/-- Under a decidable neighbourhood basis, `|𝒟|` ↔ InfoSys domain ↔ ideal completion. -/
noncomputable def nbhdBasis_ideal_iso (B : NbhdBasis ι β) :
    B.system.Element ≃o Ideal (InfoSysToIdealCompletion.FiniteElement B.toInfoSys) :=
  B.domainOrderIso.trans (InfoSysToIdealCompletion.domainOrderIso B.toInfoSys)

/-- Constructive 1980↔1982↔ideal triangle for InfoSys domains. -/
noncomputable abbrev presentation_domains_equiv_infoSys (A : InfoSys α) :=
  neighborhood_ideal_iso A

/-! ## Continuous lattice presentations via round `↟`-filters -/

variable {D : Type*} [CompleteLattice D] [DecidableEq D]

/-- Decidable coding of the `↟`-neighbourhood system: tokens are elements of `D`. -/
def wayBelowNbhdBasis : NbhdBasis D D where
  system := toNeighborhoodSystem
  nbhd := wayBelowUp
  nbhd_mem := fun a => ⟨a, rfl⟩
  exhaustive := by
    intro X hX
    obtain ⟨a, rfl⟩ := hX
    exact ⟨a, rfl⟩
  botIdx := ⊥
  botIdx_eq := wayBelowUp_bot

theorem wayBelowNbhdBasis_system :
    (wayBelowNbhdBasis (D := D)).system = toNeighborhoodSystem :=
  rfl

/-- Roundness transported to InfoSys elements of the `↟`-basis. -/
def IsRoundInfoSysElement (e : (wayBelowNbhdBasis (D := D)).toInfoSys.Element) : Prop :=
  IsRound ((wayBelowNbhdBasis (D := D)).domainOrderIso.symm e)

abbrev RoundInfoSysElement : Type _ :=
  { e : (wayBelowNbhdBasis (D := D)).toInfoSys.Element // IsRoundInfoSysElement (D := D) e }

/-- Round `↟`-filters ↔ round elements of the coded InfoSys. -/
noncomputable def roundFilter_infoSys_iso :
    RoundFilter (D := D) ≃o RoundInfoSysElement (D := D) where
  toFun := fun f =>
    ⟨(wayBelowNbhdBasis (D := D)).domainOrderIso f.1, by
      change IsRound ((wayBelowNbhdBasis (D := D)).domainOrderIso.symm
        ((wayBelowNbhdBasis (D := D)).domainOrderIso f.1))
      rw [OrderIso.symm_apply_apply]
      exact f.2⟩
  invFun := fun e =>
    ⟨(wayBelowNbhdBasis (D := D)).domainOrderIso.symm e.1, e.2⟩
  left_inv := fun f => Subtype.ext <|
    (wayBelowNbhdBasis (D := D)).domainOrderIso.left_inv f.1
  right_inv := fun e => Subtype.ext <|
    (wayBelowNbhdBasis (D := D)).domainOrderIso.right_inv e.1
  map_rel_iff' := by
    intro f g
    exact (wayBelowNbhdBasis (D := D)).domainOrderIso.map_rel_iff

section Continuous

variable (hD : IsContinuousLattice D)
include hD

/-- **1972 ↔ round 1980:** continuous lattice ↔ round `↟`-filters. -/
noncomputable def continuousLattice_roundFilter_iso :
    D ≃o RoundFilter (D := D) :=
  ContinuousLatticeToNeighborhood.domainOrderIso hD

/-- **1972 ↔ round 1982:** continuous lattice ↔ round InfoSys elements of the `↟`-basis. -/
noncomputable def continuousLattice_roundInfoSys_iso :
    D ≃o RoundInfoSysElement (D := D) :=
  (continuousLattice_roundFilter_iso hD).trans roundFilter_infoSys_iso

/-- Round InfoSys elements ↔ ideals of finite elements that come from round InfoSys
elements (via the ideal-completion iso). -/
noncomputable def roundInfoSys_ideal_iso :
    RoundInfoSysElement (D := D) ≃o
      { I : Ideal (InfoSysToIdealCompletion.FiniteElement
          (wayBelowNbhdBasis (D := D)).toInfoSys) //
        IsRoundInfoSysElement (D := D)
          ((InfoSysToIdealCompletion.domainOrderIso
            (wayBelowNbhdBasis (D := D)).toInfoSys).symm I) } := by
  let A := (wayBelowNbhdBasis (D := D)).toInfoSys
  let ιE := InfoSysToIdealCompletion.domainOrderIso A
  refine {
    toFun := fun e => ⟨ιE e.1, by
      change IsRoundInfoSysElement (ιE.symm (ιE e.1))
      rw [OrderIso.symm_apply_apply]
      exact e.2⟩
    invFun := fun I => ⟨ιE.symm I.1, I.2⟩
    left_inv := fun e => Subtype.ext (ιE.left_inv e.1)
    right_inv := fun I => Subtype.ext (ιE.right_inv I.1)
    map_rel_iff' := by
      intro e₁ e₂
      exact ιE.map_rel_iff
  }

/-- **Blueprint:** three-presentation equivalence for continuous lattices.

`D ≃o RoundFilter ≃o RoundInfoSysElement`, with the `↟`-system’s `NbhdBasis`
supplying the 1980↔1982 coding. (Raw `|𝒟|` / full `|A|` remain larger.) -/
noncomputable def presentation_domains_equiv :
    D ≃o RoundInfoSysElement (D := D) :=
  continuousLattice_roundInfoSys_iso hD

/-- Extended form through ideal completion of finite elements of the `↟`-InfoSys. -/
noncomputable def presentation_domains_equiv_ideal :
    D ≃o
      { I : Ideal (InfoSysToIdealCompletion.FiniteElement
          (wayBelowNbhdBasis (D := D)).toInfoSys) //
        IsRoundInfoSysElement (D := D)
          ((InfoSysToIdealCompletion.domainOrderIso
            (wayBelowNbhdBasis (D := D)).toInfoSys).symm I) } :=
  (presentation_domains_equiv hD).trans (roundInfoSys_ideal_iso (D := D))

end Continuous

end ScottModels

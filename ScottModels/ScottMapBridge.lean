/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott_models
-/

import Mathlib.Order.Hom.Basic
import Scott1972.ContinuousLattice.FunctionSpaces
import Scott1982.Factoid46
import Scott1982.Factoid36
import Scott1982.Proposition53
import ScottModels.InfoSysConstructions
import ScottModels.PresentationDomains

/-!
# Construction cross-links — ApproximableMap ↔ ScottContinuous ↔ ScottMap

* **Factoid 4.6:** `ApproximableMap A B ≃o ScottContinuous A B` (1982).
* **1972 transport:** `ScottMap D D'` conjugates along `presentation_domains_equiv`
  (or the round-filter iso) to pointwise-ordered maps on the round presentation.
* Blueprint packaging: `infoSys_constructions_equiv` bundles the three 1982 domain
  isos with these cross-links.
-/

namespace ScottModels

open Scott1982
open Scott1982.Constructive
open Scott1982.InfoSys
open Scott1982.InfoSys.ApproximableMap
open Scott1972.ContinuousLattice
open ContinuousLatticeToNeighborhood

/-! ## Factoid 4.6 as an order isomorphism -/

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem scottContinuous_ext {A : InfoSys α} {B : InfoSys β}
    {f g : ScottContinuous A B} (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  obtain ⟨tf, mf, df⟩ := f
  obtain ⟨tg, mg, dg⟩ := g
  have : tf = tg := funext h
  subst this
  rfl

/-- Pointwise order on Scott-continuous maps of InfoSys domains. -/
instance instPartialOrderScottContinuous (A : InfoSys α) (B : InfoSys β) :
    PartialOrder (ScottContinuous A B) where
  le f g := ∀ x, f.toFun x ≤ g.toFun x
  le_refl _ _ := le_refl _
  le_trans _ _ _ hfg hgh x := le_trans (hfg x) (hgh x)
  le_antisymm _ _ hfg hgf :=
    scottContinuous_ext fun x => le_antisymm (hfg x) (hgf x)

theorem ofScottContinuous_toScottContinuous {A : InfoSys α} {B : InfoSys β}
    (f : ApproximableMap A B) :
    ofScottContinuous (toScottContinuous f) = f := by
  refine ApproximableMap.ext fun u v => ?_
  constructor
  · intro ⟨hu, hv, hsub⟩
    exact (f.rel_iff_closure_le hu hv).2
      (B.closure_le_element (f.toElement (A.closure u hu)) hv hsub)
  · intro hrel
    refine ⟨f.rel_dom hrel, f.rel_cod hrel, ?_⟩
    intro y hy
    have hv : v ∈ B.Con := f.rel_cod hrel
    have hu : u ∈ A.Con := f.rel_dom hrel
    exact (f.rel_iff_closure_le hu hv).1 hrel (B.subset_closure hv (Finset.mem_coe.1 hy))

theorem toScottContinuous_ofScottContinuous {A : InfoSys α} {B : InfoSys β}
    (g : ScottContinuous A B) :
    toScottContinuous (ofScottContinuous g) = g :=
  scottContinuous_ext fun x => toElement_ofScottContinuous g x

/-- **Factoid 4.6.** Approximable maps ↔ Scott-continuous maps of domains. -/
noncomputable def approximableMap_scottContinuous_equiv (A : InfoSys α) (B : InfoSys β) :
    ApproximableMap A B ≃o ScottContinuous A B where
  toFun := toScottContinuous
  invFun := ofScottContinuous
  left_inv := ofScottContinuous_toScottContinuous
  right_inv := toScottContinuous_ofScottContinuous
  map_rel_iff' := by
    intro f g
    exact (le_iff_toElement_le f g).symm

/-! ## ScottMap conjugation along the round presentation -/

variable {D E : Type*} [CompleteLattice D] [CompleteLattice E]

/-- Conjugate a Scott map along order isomorphisms of the underlying lattices. -/
noncomputable def conjScottMapFun {D' E' : Type*} [LE D'] [LE E']
    (ιD : D ≃o D') (ιE : E ≃o E') (f : ScottMap D E) : D' → E' :=
  ⇑ιE ∘ (f : D → E) ∘ ⇑ιD.symm

theorem conjScottMapFun_le_iff {D' E' : Type*} [PartialOrder D'] [PartialOrder E']
    (ιD : D ≃o D') (ιE : E ≃o E') {f g : ScottMap D E} :
    (∀ x : D', conjScottMapFun ιD ιE f x ≤ conjScottMapFun ιD ιE g x) ↔ f ≤ g := by
  constructor
  · intro h
    rw [ScottMap.le_def]
    intro x
    have hx : ιE (f x) ≤ ιE (g x) := by
      simpa [conjScottMapFun, OrderIso.symm_apply_apply] using h (ιD x)
    exact ιE.map_rel_iff.mp hx
  · intro hfg x
    exact ιE.monotone (hfg (ιD.symm x))

/-- Scott maps packaged as their conjugates along given presentation isos. -/
structure ConjScottMap {D' E' : Type*} [PartialOrder D'] [PartialOrder E']
    (ιD : D ≃o D') (ιE : E ≃o E') where
  scott : ScottMap D E

namespace ConjScottMap

variable {D' E' : Type*} [PartialOrder D'] [PartialOrder E']
variable (ιD : D ≃o D') (ιE : E ≃o E')

noncomputable instance : CoeFun (ConjScottMap ιD ιE) (fun _ => D' → E') where
  coe g := conjScottMapFun ιD ιE g.scott

theorem ext {f g : ConjScottMap ιD ιE} (h : f.scott = g.scott) : f = g := by
  cases f; cases g; congr

noncomputable instance : PartialOrder (ConjScottMap ιD ιE) where
  le f g := ∀ x, conjScottMapFun ιD ιE f.scott x ≤ conjScottMapFun ιD ιE g.scott x
  le_refl _ _ := le_refl _
  le_trans _ _ _ hfg hgh x := le_trans (hfg x) (hgh x)
  le_antisymm f g hfg hgf := by
    refine ext ιD ιE ?_
    exact le_antisymm
      ((conjScottMapFun_le_iff ιD ιE).1 hfg)
      ((conjScottMapFun_le_iff ιD ιE).1 hgf)

/-- **1972 ↔ round presentation:** Scott maps ≃ conjugates along the given isos. -/
noncomputable def orderIso : ScottMap D E ≃o ConjScottMap ιD ιE where
  toFun f := ⟨f⟩
  invFun g := g.scott
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro f g
    exact conjScottMapFun_le_iff ιD ιE

end ConjScottMap

section ContinuousRoundFilter

variable (hD : IsContinuousLattice D) (hE : IsContinuousLattice E)
include hD hE

/-- Conjugation along round `↟`-filters (no `DecidableEq` needed). -/
noncomputable abbrev scottMap_roundFilter_iso :
    ScottMap D E ≃o
      ConjScottMap (continuousLattice_roundFilter_iso hD)
        (continuousLattice_roundFilter_iso hE) :=
  ConjScottMap.orderIso (continuousLattice_roundFilter_iso hD)
    (continuousLattice_roundFilter_iso hE)

end ContinuousRoundFilter

section ContinuousRoundInfoSys

variable (hD : IsContinuousLattice D) (hE : IsContinuousLattice E)
variable [DecidableEq D] [DecidableEq E]
include hD hE

/-- Conjugation along round InfoSys elements of the `↟`-basis. -/
noncomputable abbrev scottMap_roundInfoSys_iso :
    ScottMap D E ≃o
      ConjScottMap (presentation_domains_equiv hD) (presentation_domains_equiv hE) :=
  ConjScottMap.orderIso (presentation_domains_equiv hD) (presentation_domains_equiv hE)

end ContinuousRoundInfoSys

/-! ## Blueprint packaging

Bundled 1982 construction domain isos + 1972/1982 function-space cross-links. -/
namespace infoSys_constructions_equiv

noncomputable abbrev product := @infoSys_product_domain_equiv
noncomputable abbrev sum := @infoSys_sum_domain_equiv
noncomputable abbrev functionSpace := @infoSys_function_space_domain_equiv
noncomputable abbrev approximable_scottContinuous := @approximableMap_scottContinuous_equiv
noncomputable abbrev scottMap_roundFilter := @scottMap_roundFilter_iso
noncomputable abbrev scottMap_roundInfoSys := @scottMap_roundInfoSys_iso

end infoSys_constructions_equiv

end ScottModels

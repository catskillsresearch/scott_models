import Mathlib.Order.Hom.Basic
import Scott1982.Theorem72

/-!
# Construction equivalence — products (first slice of `infoSys_constructions_equiv`)

1982: `|A × B| ≃o |A| × |B|` via `pairElements` / `fstMap.toElement` / `sndMap.toElement`
(Prop 6.2 apparatus in `Proposition62` / `Theorem72`).

1972 counterpart (already in sibling): products of continuous lattices are continuous
(`Scott1972.ContinuousLattice.proposition_2_9_a`).
-/

namespace ScottModels

open Scott1982
open Scott1982.Constructive
open Scott1982.InfoSys
open Scott1982.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

/-- Split a product-domain element into its two projections. -/
def unpair (z : (productSystem A B).Element) : A.Element × B.Element :=
  ((fstMap A B).toElement z, (sndMap A B).toElement z)

theorem unpair_pairElements (x : A.Element) (y : B.Element) :
    unpair A B (pairElements A B x y) = (x, y) := by
  simp [unpair, fstMap_pairElements, sndMap_pairElements]

theorem pairElements_unpair (z : (productSystem A B).Element) :
    pairElements A B ((fstMap A B).toElement z) ((sndMap A B).toElement z) = z :=
  element_eq_of_fst_snd A B _ z (fstMap_pairElements A B _ _) (sndMap_pairElements A B _ _)

theorem pairElements_mono {x₁ x₂ : A.Element} {y₁ y₂ : B.Element}
    (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    pairElements A B x₁ y₁ ≤ pairElements A B x₂ y₂ := by
  intro p hp
  exact ⟨fun hbot => hx (hp.1 hbot), fun hbot => hy (hp.2 hbot)⟩

theorem unpair_mono {z₁ z₂ : (productSystem A B).Element} (hz : z₁ ≤ z₂) :
    unpair A B z₁ ≤ unpair A B z₂ := by
  constructor
  · exact (fstMap A B).toElement_mono hz
  · exact (sndMap A B).toElement_mono hz

/-- **Product domain iso (1982).** `|A × B| ≃o |A| × |B|`. -/
noncomputable def productDomainIso :
    A.Element × B.Element ≃o (productSystem A B).Element where
  toFun := fun p => pairElements A B p.1 p.2
  invFun := unpair A B
  left_inv := fun p => unpair_pairElements A B p.1 p.2
  right_inv := pairElements_unpair A B
  map_rel_iff' := by
    intro p q
    constructor
    · intro h
      simpa [unpair, fstMap_pairElements, sndMap_pairElements] using unpair_mono A B h
    · intro h
      exact pairElements_mono A B h.1 h.2

end InfoSysConstructions

/-- Blueprint-facing name for the 1982 product domain isomorphism. -/
noncomputable abbrev infoSys_product_domain_equiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) :
    A.Element × B.Element ≃o (productSystem A B).Element :=
  InfoSysConstructions.productDomainIso A B

end ScottModels

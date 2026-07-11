import Mathlib.Order.Hom.Basic
import Mathlib.Order.Hom.WithTopBot
import Mathlib.Data.Sum.Order
import Mathlib.Order.Ideal
import Scott1982.Factoid24
import Scott1982.Factoid81
import Scott1982.Proposition54
import ScottModels.InfoSysToNeighborhood
import ScottModels.InfoSysToIdealCompletion
import ScottModels.PresentationDomains
import ScottModels.InfoSysConstructions
import ScottModels.ScottMapBridge

/-!
# Worked example — S-expression / tree domain `T ≅ A + (T × T)`

Scott 1982 Factoid 8.1 (`treeSystem`) over the ℕ lower-bound atom system
(Factoid 2.4), walked through the Part IV bridges: information system →
neighbourhood filters → ideal completion, plus identity approximable maps as
Scott-continuous maps (Factoid 4.6).
-/

namespace ScottModels

open Scott1982
open Scott1982.Constructive
open Scott1982.InfoSys
open Scott1982.InfoSys.ApproximableMap
open Order

/-! ## Atom system (Factoid 2.4, named) -/

/-- Scott’s ℕ lower-bound information system (Factoid 2.4), as a named definition. -/
def lowerBoundSystem : InfoSys ℕ where
  bot := 0
  Con := Set.univ
  Ent := Factoid24.lowerBoundEnt
  con_subset := by
    intro u v _ _
    exact Set.mem_univ v
  con_sing := by
    intro _
    exact Set.mem_univ _
  ent_con := by
    intro u a _
    exact Set.mem_univ _
  ent_bot := by
    intro u _
    exact Or.inl rfl
  ent_refl := by
    intro u a _ ha
    exact Or.inr ⟨a, ha, le_rfl⟩
  ent_trans := by
    intro u v c _ _ hvEnt huEnt
    rcases huEnt with rfl | ⟨n, hn, hcn⟩
    · exact Or.inl rfl
    · rcases hvEnt n hn with rfl | ⟨k, hk, hnk⟩
      · exact Or.inl (Nat.le_zero.mp hcn)
      · exact Or.inr ⟨k, hk, le_trans hcn hnk⟩

/-! ## S-expression system -/

/-- Tree / S-expression information system over lower-bound atoms. -/
abbrev SexSys : InfoSys (TreeToken ℕ) :=
  treeSystem lowerBoundSystem

/-- Official right-hand side `A + (T × T)`. -/
abbrev SexRhs : InfoSys (SumToken ℕ (ProdToken SexSys SexSys)) :=
  treeRhs lowerBoundSystem

theorem sexRhs_eq_sum_product :
    SexRhs = sumSystem lowerBoundSystem (productSystem SexSys SexSys) :=
  treeRhs_eq_sum_product lowerBoundSystem

/-- Unfolding tokens into the sum-of-product carrier (Factoid 8.1). -/
theorem sexUnfold_atom (n : ℕ) :
    treeUnfold lowerBoundSystem (.atom n) = SumToken.left n :=
  treeUnfold_atom lowerBoundSystem n

/-! ## Concrete finite elements -/

/-- Closure of a singleton atom token `{atom n}`. -/
noncomputable def sexAtom (n : ℕ) : SexSys.Element :=
  SexSys.closure {TreeToken.atom n} (SexSys.con_sing _)

theorem sexAtom_mem_self (n : ℕ) : TreeToken.atom n ∈ (sexAtom n).carrier :=
  SexSys.subset_closure (SexSys.con_sing _) (Finset.mem_singleton_self _)

/-! ## 1982 → 1980: basic-open neighbourhood filters -/

/-- `|T| ≃o` filters of basic opens `[u]`. -/
noncomputable abbrev sexNeighborhoodIso :
    SexSys.Element ≃o (InfoSysToNeighborhood.toNeighborhoodSystem SexSys).Element :=
  InfoSysToNeighborhood.domainOrderIso SexSys

/-! ## 1982 → ideal completion -/

/-- `|T| ≃o Ideal (FiniteElement T)`. -/
noncomputable abbrev sexIdealIso :
    SexSys.Element ≃o Ideal (InfoSysToIdealCompletion.FiniteElement SexSys) :=
  InfoSysToIdealCompletion.domainOrderIso SexSys

/-- Neighbourhood filters ≃ ideals of finite elements (constructive triangle). -/
noncomputable abbrev sexNeighborhoodIdealIso :=
  neighborhood_ideal_iso SexSys

/-! ## Domain equation at the level of domains (1982 constructions) -/

/--
`WithBot (|A| ⊕ (|T| × |T|)) ≃o |A + (T × T)|`, composing the Part IV product and
separated-sum isos with Factoid 8.1’s RHS.
-/
noncomputable def sexDomainEquationIso :
    WithBot (lowerBoundSystem.Element ⊕ (SexSys.Element × SexSys.Element)) ≃o
      SexRhs.Element :=
  let ιProd := InfoSysConstructions.productDomainIso SexSys SexSys
  let ιSum := InfoSysConstructions.sumDomainIso lowerBoundSystem (productSystem SexSys SexSys)
  let mid :=
    (OrderIso.refl lowerBoundSystem.Element).sumCongr ιProd |>.withBotCongr
  mid.trans ιSum

/-! ## Morphisms: identity is Scott-continuous (Factoid 4.6) -/

/-- Identity approximable map on `T`, as a Scott-continuous endomap. -/
noncomputable abbrev sexIdScottContinuous : ScottContinuous SexSys SexSys :=
  (approximableMap_scottContinuous_equiv SexSys SexSys) (idMap SexSys)

theorem sexId_toElement (x : SexSys.Element) :
    sexIdScottContinuous.toFun x = x :=
  idMap_toElement SexSys x

end ScottModels

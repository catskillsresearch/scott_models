import ScottModels.InfoSysToNeighborhood
import ScottModels.InfoSysToIdealCompletion
import ScottModels.NeighborhoodToInfoSys
import ScottModels.ContinuousLatticeToNeighborhood
import ScottModels.IdealCompletionToContinuousLattice

/-!
# Presentation domain equivalences (partial)

Composes the completed constructive legs. Full `presentation_domains_equiv` with the
1972 continuous-lattice corner still needs `|𝒟| ≃o D` (round filters) beyond the
existing `domainEmbedding`.
-/

namespace ScottModels

open Scott1982
open Order

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

/-- Blueprint placeholder: constructive 1980↔1982↔ideal triangle for InfoSys domains.
The 1972 corner remains an embedding (`domainEmbedding`) pending round ideals. -/
noncomputable abbrev presentation_domains_equiv_infoSys (A : InfoSys α) :=
  neighborhood_ideal_iso A

end ScottModels

import ScottModels.InfoSysToNeighborhood
import ScottModels.InfoSysToIdealCompletion
import ScottModels.NeighborhoodToInfoSys
import ScottModels.ContinuousLatticeToNeighborhood
import ScottModels.IdealCompletionToContinuousLattice

/-!
# Presentation domain equivalences (partial)

Composes the completed constructive legs (1980↔1982↔ideal). The 1972 corner is
`D ≃o RoundFilter` of the `↟`-system (`ContinuousLatticeToNeighborhood.domainOrderIso`),
not an iso onto raw `|𝒟|`. Full `presentation_domains_equiv` still needs to identify
that round-filter domain with the 1980/1982 presentations.
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

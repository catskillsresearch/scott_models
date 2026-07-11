import ScottModels.NeighborhoodToInfoSys
import ScottModels.InfoSysToNeighborhood
import ScottModels.ContinuousLatticeToNeighborhood
import ScottModels.InfoSysToIdealCompletion
import ScottModels.IdealCompletionToContinuousLattice

/-!
# Equivalence theorems (Part IV)

Bridges between Scott's 1972 continuous-lattice presentation, 1980 neighbourhood systems
(PRG-19), and 1982 information systems. Sibling packages are finished; this module holds
the cross-presentation maps. See `arxiv.md` / `HANDOFF.md`.

## Status

* `neighborhoodSystem_to_infoSys` — **done** (`NeighborhoodToInfoSys.lean`)
* `infoSys_to_neighborhoodSystem` — **done** (`InfoSysToNeighborhood.lean`)
* `continuousLattice_to_neighborhoodSystem` — **done** (`ContinuousLatticeToNeighborhood.lean`;
  `D ≃o RoundFilter`, not raw `|𝒟|`)
* `infoSys_to_idealCompletion` — **done** (`InfoSysToIdealCompletion.lean`;
  `|A| ≃o Ideal (FiniteElement A)`)
* `idealCompletion_to_continuousLattice` — **done** (`IdealCompletionToContinuousLattice.lean`;
  algebraic complete lattice ⇒ `IsContinuousLattice`; classical `≪`)
* `presentation_domains_equiv` — **partial** (`PresentationDomains.lean`; constructive
  triangle; CL corner is round-filter iso)
* `infoSys_constructions_equiv` — **partial** (`InfoSysConstructions.lean`; product done;
  sum / function space not yet)
-/

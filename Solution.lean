/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import ScottModels.NeighborhoodToInfoSys
import ScottModels.InfoSysToNeighborhood
import ScottModels.ContinuousLatticeToNeighborhood
import ScottModels.PresentationDomains
import ScottModels.WorkedExampleSExpr

/-!
# Solutions to the Challenge

The declarations of `Challenge.lean`, proved. Importing the `ScottModels`
bridge modules supplies

* `neighborhoodSystem_to_infoSys` / `NbhdBasis.toInfoSys`
* `infoSys_to_neighborhoodSystem` / `InfoSysToNeighborhood.toNeighborhoodSystem`
* `InfoSysToNeighborhood.domainOrderIso` (`|A| ≃o` basic-open filters)
* `presentation_domains_equiv` (`D ≃o RoundInfoSysElement`)
* `sexNeighborhoodIso` / `sexIdealIso` / `sexDomainEquationIso` (Factoid 8.1
  instance `T ≅ A + (T × T)`)

and the supporting names those types mention (`NbhdBasis`, `InfoSys`,
`NeighborhoodSystem`, `IsContinuousLattice`, `RoundFilter`, `IsRound`,
`wayBelowNbhdBasis`, `domainOrderIso`, `Element`, `TreeToken`, `treeSystem`,
`FiniteElement`, `lowerBoundSystem`), with the same names and
types as in the Challenge module. Comparator compares those declarations.

There is no `sorry` in the `ScottModels/` proof modules. The compared
1980 ↔ 1982 maps, `presentation_domains_equiv`, and the S-expression
carrier isos use `propext` and `Quot.sound` only. `sexDomainEquationIso`
uses `Classical.choice` via the 1982 sum trichotomy. `Classical.choice`
is also permitted for 1972 topological `≪` elsewhere and is listed in
`comparator.json`.
-/

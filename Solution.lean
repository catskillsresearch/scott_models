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
  instance: `|T| ≃o` filters, `|T| ≃o Ideal(K(T))`, and
  `|T| ≃o |A + (T × T)|`)

and the supporting names those types mention (`NbhdBasis`, `InfoSys`,
`NeighborhoodSystem`, `IsContinuousLattice`, `RoundFilter`, `IsRound`,
`wayBelowNbhdBasis`, `domainOrderIso`, `Element`, `TreeToken`, `treeSystem`,
`FiniteElement`, `lowerBoundSystem`), with the same names and
types as in the Challenge module. Comparator compares those declarations
and the `exists_*` theorems (`Nonempty` of each compared `OrderIso`).

There is no `sorry` in the `ScottModels/` proof modules. The compared
1980 ↔ 1982 maps, `presentation_domains_equiv`, and the S-expression
carrier isos — including `sexDomainEquationIso` (`|T| ≃o |A + (T × T)|`
via `treeUnfold`) — use `propext` and `Quot.sound` only.
`Classical.choice` is permitted for 1972 topological `≪` elsewhere and
is listed in `comparator.json`.
-/

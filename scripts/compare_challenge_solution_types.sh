#!/usr/bin/env bash
# Diff Challenge vs Solution declaration types for every comparator.json name.
# Palomar Comparator compares exported types, including exact universe parameter
# names and instance paths. A green `lake build` does not imply a match.
set -euo pipefail
cd "$(dirname "$0")/.."

NAMES=(
  ScottModels.exists_presentation_domains_equiv
  ScottModels.exists_sexNeighborhoodIso
  ScottModels.exists_sexIdealIso
  ScottModels.exists_sexDomainEquationIso
  ScottModels.neighborhoodSystem_to_infoSys
  ScottModels.infoSys_to_neighborhoodSystem
  ScottModels.InfoSysToNeighborhood.domainOrderIso
  ScottModels.presentation_domains_equiv
  ScottModels.sexNeighborhoodIso
  ScottModels.sexIdealIso
  ScottModels.sexDomainEquationIso
  ScottModels.NbhdBasis.toInfoSys
  ScottModels.NbhdBasis.domainOrderIso
  ScottModels.InfoSysToNeighborhood.toNeighborhoodSystem
  ScottModels.wayBelowNbhdBasis
  ScottModels.ContinuousLatticeToNeighborhood.toNeighborhoodSystem
  ScottModels.IsRoundInfoSysElement
  Scott1982.InfoSys.instPartialOrderElement
  Scott1980.Neighborhood.NeighborhoodSystem.instPartialOrderElement
  Scott1982.InfoSys.treeSystem
  Scott1982.InfoSys.treeRhs
  ScottModels.lowerBoundSystem
  ScottModels.SexSys
  ScottModels.SexRhs
  ScottModels.InfoSysToIdealCompletion.FiniteElement
  Scott1982.InfoSys.closure
  Scott1982.InfoSys.instDecidableEqTreeToken
  Scott1982.InfoSys.instDecidableEqSumToken
  Scott1982.InfoSys.instDecidableEqProdToken
  Scott1972.ContinuousLattice.IsContinuousLattice
  Scott1972.ContinuousLattice.WayBelow
  Scott1972.ContinuousLattice.ScottOpen
)

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

write_lean() {
  local module="$1" out="$2"
  {
    echo "import ${module}"
    echo "set_option pp.all true"
    echo "set_option pp.explicit true"
    echo "set_option pp.universes true"
    echo "set_option pp.funBinderTypes true"
    for n in "${NAMES[@]}"; do
      echo "#check ${n}"
    done
  } >"${out}"
}

write_lean Challenge "${tmp}/ChallengeTypes.lean"
write_lean Solution "${tmp}/SolutionTypes.lean"

lake env lean "${tmp}/ChallengeTypes.lean" 2>/dev/null \
  | grep -vE 'LEAN_PATH|trace:|warning:|declaration uses' \
  >"${tmp}/challenge.txt" || true
lake env lean "${tmp}/SolutionTypes.lean" 2>/dev/null \
  | grep -vE 'LEAN_PATH|trace:|warning:|declaration uses' \
  >"${tmp}/solution.txt" || true

echo "== Challenge (pp.all, exact universe names) =="
cat "${tmp}/challenge.txt"
echo
echo "== Solution (pp.all, exact universe names) =="
cat "${tmp}/solution.txt"
echo
if diff -u "${tmp}/challenge.txt" "${tmp}/solution.txt"; then
  echo "OK: Challenge and Solution types match exactly."
else
  echo "FAIL: type/universe/instance mismatch — Palomar Comparator will reject this."
  exit 1
fi

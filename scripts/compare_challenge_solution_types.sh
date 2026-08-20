#!/usr/bin/env bash
# Diff Challenge vs Solution types for every comparator.json name.
# Palomar Comparator compares exported types syntactically (pp.all / instance
# names). A green `lake build` does not imply a match.
set -euo pipefail
cd "$(dirname "$0")/.."

NAMES=(
  ScottModels.neighborhoodSystem_to_infoSys
  ScottModels.infoSys_to_neighborhoodSystem
  ScottModels.InfoSysToNeighborhood.domainOrderIso
  ScottModels.presentation_domains_equiv
  ScottModels.NbhdBasis.toInfoSys
  ScottModels.NbhdBasis.domainOrderIso
  ScottModels.InfoSysToNeighborhood.toNeighborhoodSystem
  ScottModels.wayBelowNbhdBasis
  ScottModels.ContinuousLatticeToNeighborhood.toNeighborhoodSystem
  ScottModels.IsRoundInfoSysElement
  Scott1982.InfoSys.instPartialOrderElement
  Scott1980.Neighborhood.NeighborhoodSystem.instPartialOrderElement
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

# Drop universe-name noise (u_1 vs u_4) so instance-name mismatches stand out.
normalize() {
  sed -E 's/\.\{u_[0-9]+(,[ ]*u_[0-9]+)*\}//g; s/u_[0-9]+/u/g'
}

normalize <"${tmp}/challenge.txt" >"${tmp}/challenge.norm"
normalize <"${tmp}/solution.txt" >"${tmp}/solution.norm"

echo "== Challenge (pp.all, universes normalized) =="
cat "${tmp}/challenge.norm"
echo
echo "== Solution (pp.all, universes normalized) =="
cat "${tmp}/solution.norm"
echo
if diff -u "${tmp}/challenge.norm" "${tmp}/solution.norm"; then
  echo "OK: Challenge and Solution types match (after universe-name normalize)."
else
  echo "FAIL: type/instance mismatch — Palomar Comparator will reject this."
  exit 1
fi

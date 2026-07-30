#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

status=0
boundary='EverettianDecoherence/Core/UpstreamAPI.lean'
expected_first='import EverettianProbability.API.ConditionalMainResults'
expected_second='import EverettianProbability.API.ExactFiniteMainResults'

mapfile -t imports < <(grep -nE '^[[:space:]]*import[[:space:]]+' "$boundary" || true)
if [ "${#imports[@]}" -ne 2 ] ||
  [ "${imports[0]#*:}" != "$expected_first" ] ||
  [ "${imports[1]#*:}" != "$expected_second" ]; then
  printf 'BOUNDARY_IMPORTS_INVALID=%s\n' "$boundary"
  status=1
fi

while IFS=: read -r file line text; do
  [ "$file" = "$boundary" ] && continue
  printf 'DIRECT_UPSTREAM_IMPORT=%s:%s:%s\n' "$file" "$line" "$text"
  status=1
done < <(grep -rnE '^[[:space:]]*import[[:space:]]+EverettianProbability\.' EverettianDecoherence EverettianDecoherence.lean 2>/dev/null || true)

while IFS=: read -r file line text; do
  printf 'FORBIDDEN_UPSTREAM_IMPORT=%s:%s:%s\n' "$file" "$line" "$text"
  status=1
done < <(grep -rnE '^[[:space:]]*import[[:space:]]+EverettianProbability\.(ExactFinite|Diachronic|PhysicalRefinement|Refinement|BornCalibration|API\.ExactFinitePhysicalRichness)' EverettianDecoherence EverettianDecoherence.lean 2>/dev/null || true)

if [ "$status" -eq 0 ]; then
  echo 'UPSTREAM_API_BOUNDARY=PASS'
else
  echo 'UPSTREAM_API_BOUNDARY=FAIL'
  exit 1
fi

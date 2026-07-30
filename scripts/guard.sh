#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

SRC_DIRS=(EverettianDecoherence EverettianDecoherence.lean)
AXIOM_HITS=$(grep -rnE '(^|[^[:alnum:]_])axiom[[:space:]]' "${SRC_DIRS[@]}" 2>/dev/null | wc -l | tr -d ' ' || true)
NATIVE_DECIDE_HITS=$(grep -rn 'native_decide' "${SRC_DIRS[@]}" 2>/dev/null | wc -l | tr -d ' ' || true)
MAXHEARTBEATS_ZERO_HITS=$(grep -rnE 'maxHeartbeats[[:space:]]+0\b' "${SRC_DIRS[@]}" 2>/dev/null | wc -l | tr -d ' ' || true)
SORRY_COUNT=$(grep -rno '\bsorry\b' "${SRC_DIRS[@]}" 2>/dev/null | wc -l | tr -d ' ' || true)
SORRY_ANNOTATION_MISSING=0

while IFS=: read -r file line _; do
  [ -n "$file" ] || continue
  previous=$(sed -n "$((line - 1))p" "$file")
  if ! printf '%s\n' "$previous" | grep -qE '^[[:space:]]*--[[:space:]]+SATISFIABILITY:'; then
    echo "UNANNOTATED_SORRY=$file:$line"
    SORRY_ANNOTATION_MISSING=$((SORRY_ANNOTATION_MISSING + 1))
  fi
done < <(grep -rn '\bsorry\b' "${SRC_DIRS[@]}" 2>/dev/null || true)

NONTRIVIALITY_WARNINGS=0
while IFS=: read -r premise_file premise_name; do
  [ -n "$premise_file" ] || continue
  witness_file="$(dirname "$premise_file")/NonTriviality.lean"
  if [ ! -f "$witness_file" ] || ! grep -qF "$premise_name" "$witness_file"; then
    echo "NONTRIVIALITY_MISSING=$premise_file:$premise_name"
    NONTRIVIALITY_WARNINGS=$((NONTRIVIALITY_WARNINGS + 1))
  fi
done < <(find EverettianDecoherence -name '*.lean' -type f -exec awk '
  /\/--/ { in_doc = 1; premise = index($0, "PREMISE") > 0 }
  in_doc {
    if (index($0, "PREMISE") > 0) premise = 1
    if (index($0, "-/") > 0) { in_doc = 0; if (premise) awaiting = 1 }
    next
  }
  awaiting {
    if ($0 ~ /^[[:space:]]*$/) next
    if ($0 ~ /^[[:space:]]*(structure|def)[[:space:]]+/) {
      line = $0
      sub(/^[[:space:]]*/, "", line)
      sub(/^(structure|def)[[:space:]]+/, "", line)
      split(line, parts, /[^[:alnum:]_]/)
      print FILENAME ":" parts[1]
    }
    awaiting = 0
  }
' {} +)

SORRY_BUDGET=$(tr -d '[:space:]' < SORRY_BUDGET)
run_guard() {
  local command=$1 result=$2
  if bash "$command"; then
    printf -v "$result" '%s' PASS
  else
    printf -v "$result" '%s' FAIL
  fi
}
run_guard scripts/check_upstream_api_boundary.sh UPSTREAM_API_BOUNDARY_RESULT
run_guard scripts/check_dependency_pins.sh DEPENDENCY_PINS_RESULT
run_guard scripts/check_repository_terminology.sh REPOSITORY_TERMINOLOGY_RESULT
run_guard scripts/check_agent_harness.sh AGENT_HARNESS_RESULT
run_guard scripts/check_bilingual_docs.sh BILINGUAL_DOCS_RESULT
run_guard scripts/check_line_limits.sh LINE_LIMITS_RESULT

echo "AXIOM_HITS=$AXIOM_HITS"
echo "NATIVE_DECIDE_HITS=$NATIVE_DECIDE_HITS"
echo "MAXHEARTBEATS_ZERO_HITS=$MAXHEARTBEATS_ZERO_HITS"
echo "SORRY_COUNT=$SORRY_COUNT"
echo "SORRY_ANNOTATION_MISSING=$SORRY_ANNOTATION_MISSING"
echo "NONTRIVIALITY_WARNINGS=$NONTRIVIALITY_WARNINGS"
echo "SORRY_BUDGET=$SORRY_BUDGET"
echo "UPSTREAM_API_BOUNDARY_RESULT=$UPSTREAM_API_BOUNDARY_RESULT"
echo "DEPENDENCY_PINS_RESULT=$DEPENDENCY_PINS_RESULT"
echo "REPOSITORY_TERMINOLOGY_RESULT=$REPOSITORY_TERMINOLOGY_RESULT"
echo "AGENT_HARNESS_RESULT=$AGENT_HARNESS_RESULT"
echo "BILINGUAL_DOCS_RESULT=$BILINGUAL_DOCS_RESULT"
echo "LINE_LIMITS_RESULT=$LINE_LIMITS_RESULT"

if [ "$AXIOM_HITS" -eq 0 ] && [ "$NATIVE_DECIDE_HITS" -eq 0 ] &&
  [ "$MAXHEARTBEATS_ZERO_HITS" -eq 0 ] && [ "$SORRY_ANNOTATION_MISSING" -eq 0 ] &&
  [ "$SORRY_COUNT" -le "$SORRY_BUDGET" ] && [ "$UPSTREAM_API_BOUNDARY_RESULT" = PASS ] &&
  [ "$DEPENDENCY_PINS_RESULT" = PASS ] && [ "$REPOSITORY_TERMINOLOGY_RESULT" = PASS ] &&
  [ "$AGENT_HARNESS_RESULT" = PASS ] && [ "$BILINGUAL_DOCS_RESULT" = PASS ] &&
  [ "$LINE_LIMITS_RESULT" = PASS ]; then
  echo 'GUARD_RESULT=PASS'
else
  echo 'GUARD_RESULT=FAIL'
  exit 1
fi

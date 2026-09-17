#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

before=$(git status --porcelain)
bash scripts/guard.sh

mapfile -t LEAN_FILES < <(
  {
    [ -f EverettianDecoherence.lean ] && printf '%s\n' EverettianDecoherence.lean
    find EverettianDecoherence -type f -name '*.lean'
  } | sort
)

TARGETS=()
for f in "${LEAN_FILES[@]}"; do
  target="${f%.lean}"
  target="${target//\//.}"
  TARGETS+=("$target")
done

lake clean
lake build "${TARGETS[@]}"
lake build

git diff --check

after=$(git status --porcelain)
if [ "$before" != "$after" ]; then
  echo 'VALIDATION_MODIFIED_TRACKED_STATE=FAIL'
  exit 1
fi

echo "FULL_VALIDATED_LEAN_MODULE_COUNT=${#LEAN_FILES[@]}"
echo 'FULL_VALIDATION_RESULT=PASS'
echo 'VALIDATION_RESULT=PASS'

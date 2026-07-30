#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

VALIDATION_MODE="${VALIDATION_MODE:-auto}"
case "$VALIDATION_MODE" in
  auto|incremental|full) ;;
  *)
    echo 'VALIDATION_CONFIGURATION=FAIL'
    exit 1
    ;;
esac

if [ ! -s VALIDATION_STEP ]; then
  echo 'VALIDATION_CONFIGURATION=FAIL'
  exit 1
fi
step="$(tr -d '[:space:]' < VALIDATION_STEP)"
if ! [[ "$step" =~ ^[1-9][0-9]*$ ]]; then
  echo 'VALIDATION_CONFIGURATION=FAIL'
  exit 1
fi
echo "VALIDATION_STEP=$step"

if [ "$VALIDATION_MODE" = auto ]; then
  if [ $((step % 10)) -eq 0 ]; then
    effective_mode=full
  else
    effective_mode=incremental
  fi
else
  effective_mode="$VALIDATION_MODE"
fi

if [ "$effective_mode" = full ]; then
  echo 'VALIDATION_MODE=FULL'
  exec bash scripts/validate_full.sh
fi

echo 'VALIDATION_MODE=INCREMENTAL'

before=$(git status --porcelain)
bash scripts/guard.sh

gather_lean_paths() {
  {
    git diff --name-only -- EverettianDecoherence.lean EverettianDecoherence 2>/dev/null || true
    git diff --name-only --cached -- EverettianDecoherence.lean EverettianDecoherence 2>/dev/null || true
    git ls-files --others --exclude-standard -- EverettianDecoherence.lean EverettianDecoherence 2>/dev/null || true
  } | grep '\.lean$' || true
}

CHANGED="$(gather_lean_paths | sort -u)"
if [ -z "$CHANGED" ]; then
  CHANGED="$(git diff --name-only HEAD~1 HEAD -- EverettianDecoherence.lean EverettianDecoherence 2>/dev/null | grep '\.lean$' || true)"
fi

EXISTING=()
while IFS= read -r f; do
  [ -n "$f" ] || continue
  [ -f "$f" ] || continue
  EXISTING+=("$f")
done <<< "$CHANGED"

TARGETS=()
for f in "${EXISTING[@]:-}"; do
  [ -n "$f" ] || continue
  target="${f%.lean}"
  target="${target//\//.}"
  TARGETS+=("$target")
done

if [ "${#TARGETS[@]}" -gt 0 ]; then
  lake build "${TARGETS[@]}"
fi

lake build EverettianDecoherence.Audit.MainResults
lake build EverettianDecoherence
lake build

git diff --check

after=$(git status --porcelain)
if [ "$before" != "$after" ]; then
  echo 'VALIDATION_MODIFIED_TRACKED_STATE=FAIL'
  exit 1
fi

echo "VALIDATED_LEAN_MODULE_COUNT=${#EXISTING[@]}"
echo 'VALIDATION_RESULT=PASS'

#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

FRENCH_PATTERN='saint[[:space:]_-]*g''raal'
ENGLISH_PATTERN='holy[[:space:]_-]*g''rail'

if rg -n -i --hidden \
  --glob '!/.git/**' \
  --glob '!/.lake/**' \
  --glob '!/build/**' \
  --glob '!**/*.olean' \
  "${FRENCH_PATTERN}|${ENGLISH_PATTERN}" .; then
  echo 'REPOSITORY_TERMINOLOGY=FAIL'
  exit 1
fi

echo 'REPOSITORY_TERMINOLOGY=PASS'

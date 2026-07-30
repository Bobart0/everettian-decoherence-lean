#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

status=0
while IFS= read -r file; do
  if ! grep -qE '^## (Français|French|English|Anglais)$|\*\*FR\.\*\*.*\*\*EN\.\*\*' "$file"; then
    echo "BILINGUAL_MARKERS_MISSING=$file"
    status=1
  elif ! grep -qE '^## (English|Anglais)$|\*\*EN\.\*\*' "$file"; then
    echo "ENGLISH_MARKER_MISSING=$file"
    status=1
  fi
done < <(find . -path './.git' -prune -o -path './.lake' -prune -o -path './build' -prune -o -name '*.md' -type f -print)

if [ "$status" -eq 0 ]; then
  echo 'BILINGUAL_DOCS=PASS'
else
  echo 'BILINGUAL_DOCS=FAIL'
  exit 1
fi

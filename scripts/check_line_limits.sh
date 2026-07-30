#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

status=0
while IFS= read -r file; do
  lines=$(wc -l < "$file")
  if [ "$lines" -gt 1500 ]; then
    echo "LINE_LIMIT_EXCEEDED=$file:$lines"
    status=1
  fi
done < <(find . -path './.git' -prune -o -path './.lake' -prune -o -path './build' -prune -o \( -name '*.lean' -o -name '*.md' -o -name '*.sh' \) -type f -print)

if [ "$status" -eq 0 ]; then
  echo 'LINE_LIMITS=PASS'
else
  echo 'LINE_LIMITS=FAIL'
  exit 1
fi

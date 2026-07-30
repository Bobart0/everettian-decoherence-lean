#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

status=0
fail() { printf '%s\n' "$1"; status=1; }

[ "$(tr -d '[:space:]' < lean-toolchain)" = 'leanprover/lean4:v4.32.0-rc1' ] || fail 'TOOLCHAIN_PIN_INVALID'
[ "$(tr -d '[:space:]' < VERSION)" = '0.1.0-dev' ] || fail 'VERSION_INVALID'
[ "$(tr -d '[:space:]' < SORRY_BUDGET)" = '0' ] || fail 'SORRY_BUDGET_INVALID'
[ "$(grep -c '^\[\[require\]\]$' lakefile.toml)" -eq 1 ] || fail 'REQUIRE_BLOCK_COUNT_INVALID'
grep -qx 'name = "everettian_probability"' lakefile.toml || fail 'REQUIRE_NAME_INVALID'
grep -qx 'git = "https://github.com/Bobart0/everettian-probability-lean.git"' lakefile.toml || fail 'REQUIRE_GIT_INVALID'
grep -qx 'rev = "v2.0.0"' lakefile.toml || fail 'REQUIRE_REV_INVALID'

if [ ! -f lake-manifest.json ]; then
  fail 'LAKE_MANIFEST_MISSING'
elif ! python - <<'PY'
import json
from pathlib import Path

data = json.loads(Path("lake-manifest.json").read_text(encoding="utf-8"))
needle = "3129833f3207272eddf9437bd7a3806437b7f87d"
repo = "https://github.com/Bobart0/everettian-probability-lean.git"

def walk(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)

packages = [item for item in walk(data) if isinstance(item, dict)]
if not any(
    item.get("name") == "everettian_probability"
    and needle in json.dumps(item, sort_keys=True)
    and repo in json.dumps(item, sort_keys=True)
    for item in packages
):
    raise SystemExit(1)
PY
then
  fail 'LAKE_MANIFEST_PIN_INVALID'
fi

if [ "$status" -eq 0 ]; then
  echo 'DEPENDENCY_PINS=PASS'
else
  echo 'DEPENDENCY_PINS=FAIL'
  exit 1
fi

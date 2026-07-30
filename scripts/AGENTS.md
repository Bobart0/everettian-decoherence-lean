# Script instructions

## Français

Les scripts sont POSIX Bash, utilisent `set -euo pipefail`, n'accèdent pas
au réseau dans une garde et ne modifient pas automatiquement le dépôt. Ils
émettent des diagnostics avant l'échec, des sorties PASS/FAIL stables, et ne
contournent aucune garde.

## English

Scripts are POSIX Bash, use `set -euo pipefail`, make no network access in a
guard, and never modify the repository automatically. They emit diagnostics
before failure, stable PASS/FAIL output, and do not bypass any guard.

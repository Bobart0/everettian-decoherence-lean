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

## Politique de validation incrémentale

**FR.** `scripts/validate.sh` valide de façon incrémentale par défaut,
tous les dix incréments de code déclenchant automatiquement une
reconstruction complète via `scripts/validate_full.sh`. `VALIDATION_STEP`
doit être incrémenté à chaque futur incrément de code. Toute modification
de dépendance, de toolchain, de `lakefile.toml`, de frontière d'API ou de
préparation de release force le mode complet. La validation utilise
`lake build` et son cache ; elle ne réélabore jamais systématiquement tous
les anciens fichiers avec `lake env lean`. Une validation incrémentale
n'autorise jamais l'omission de `guard.sh`, des agrégateurs
(`EverettianDecoherence`, `EverettianDecoherence.Audit.MainResults`) ou du
build global incrémental.

## Incremental validation policy

**EN.** `scripts/validate.sh` validates incrementally by default, with
every tenth code increment automatically triggering a full rebuild via
`scripts/validate_full.sh`. `VALIDATION_STEP` must be incremented on every
future code increment. Any dependency, toolchain, `lakefile.toml`, API
boundary, or release-preparation change forces full mode. Validation uses
`lake build` and its cache; it never systematically re-elaborates every
past file with `lake env lean`. Incremental validation never allows
omitting `guard.sh`, the aggregators (`EverettianDecoherence`,
`EverettianDecoherence.Audit.MainResults`), or the incremental global
build.

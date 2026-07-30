# Lean source instructions

## Français

Les imports amont passent uniquement par `Core/UpstreamAPI.lean`; aucun
import interne amont n'est permis. Chaque module porte un docstring bilingue.
Toute prémisse exige des témoins positif et négatif. Aucune revendication
physique ne dépasse la signature. Les audits ne sont jamais des dépendances de
production.

## English

Upstream imports go only through `Core/UpstreamAPI.lean`; no upstream
internal import is permitted. Every module has a bilingual docstring. Every
premise needs positive and negative witnesses. No physical claim exceeds its
signature. Audits are never production dependencies.

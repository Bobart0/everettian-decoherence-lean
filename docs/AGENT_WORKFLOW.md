# Agent workflow

## Français

1. Vérifier HEAD, origin et arbre propre.
2. Lire les AGENTS applicables et le prompt.
3. Inspecter l'API amont et modifier seulement les fichiers autorisés.
4. Compiler la cible, lancer audit, `lake build`, `scripts/guard.sh` et
   `git diff --check`.
5. Inspecter le diff, créer un commit atomique, pousser seulement si autorisé,
   puis fournir un rapport reproductible.

En cas de blocage : ne pas changer l'énoncé ni augmenter les heartbeats sans
analyse ; rapporter le but exact, signatures recherchées, tentatives et
blocages.

## English

1. Check HEAD, origin, and clean tree.
2. Read applicable AGENTS files and the increment prompt.
3. Inspect the upstream API and change only authorized files.
4. Compile the target; run audit, `lake build`, `scripts/guard.sh`, and
   `git diff --check`.
5. Inspect the diff, make an atomic commit, push only when authorized, then
   provide a reproducible report.

When blocked: do not change the statement or raise heartbeats without analysis;
report the exact goal, sought signatures, attempts, and blockers.

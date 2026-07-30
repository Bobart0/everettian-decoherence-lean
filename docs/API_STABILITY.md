# API stability

## Français

Aucune API locale n'est stable à ED0. La version est pré-1.0 de
développement ; seul le contrat de dépendance amont est figé. Toute API stable
future exigera un fichier `Audit/*APIContract.lean`. Aucune compatibilité
locale n'est encore promise.

## English

No local API is stable at ED0. This is a pre-1.0 development version; only the
upstream dependency contract is frozen. Every future stable API will require
an `Audit/*APIContract.lean` file. No local compatibility is promised yet.

ED1 names remain experimental before a future release, although their results
are audited; stabilization still requires a dedicated API contract.

## ED2B

**FR.** ED2B ne fournit aucune API locale stable. Ses noms restent
expérimentaux et ses résultats sont audités ; aucune optimalité n'est garantie.
Une stabilisation future distinguera explicitement les bornes ED2A et ED2B.

**EN.** ED2B provides no stable local API. Its names remain experimental and
its results are audited; no optimality is guaranteed. A future stabilization
will explicitly distinguish the ED2A and ED2B bounds.

# API stability

## Français

La version locale reste pré-1.0 de développement. Aucune API locale n'est
stable. Les résultats ED1–ED3B sont formalisés et audités, mais leurs noms
restent expérimentaux : aucune compatibilité locale n'est promise. Une
stabilisation future exigera un contrat d'API dédié
(`Audit/*APIContract.lean`) et distinguera explicitement chaque étape.

### Distinctions sémantiques à préserver

- générique / sensible à Born (« Born-sensitive ») ;
- statewise / uniforme ;
- uniforme sur les états / uniforme sur les perspectives ;
- défaut statewise nul / commutation globale ;
- préservation algébrique / stabilité dynamique ;
- préservation approchée des records / décohérence.

## English

The local version remains pre-1.0 development. No local API is stable. The
ED1–ED3B results are formalized and audited, but their names remain
experimental: no local compatibility is promised. A future stabilization will
require a dedicated API contract (`Audit/*APIContract.lean`) and will
explicitly distinguish each stage.

### Semantic distinctions to preserve

- generic / Born-sensitive;
- statewise / uniform;
- uniform over states / uniform over perspectives;
- zero statewise defect / global commutation;
- algebraic preservation / dynamical stability;
- approximate record preservation / decoherence.

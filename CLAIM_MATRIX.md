# Claim matrix

## Français

| Élément | Statut | Justification |
|---|---|---|
| Imports des deux façades stables amont | VERIFIED BY COMPILATION | `Core/UpstreamAPI.lean` |
| Tag amont épinglé | VERIFIED BY MANIFEST | `lake-manifest.json` |
| Audit d'axiomes amont | VERIFIED | `Audit/UpstreamAPIContract.lean` |
| Résultat local de décorrélation | NOT CLAIMED | `docs/PROGRAM_STATUS.md` |
| Dynamique de système ouvert | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Canal quantique | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Facteur tensoriel système/environnement | NOT ASSUMED | `AGENTS.md` |
| Sélection de base | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| API locale stable | NONE | `docs/API_STABILITY.md` |
| Release locale | NONE | `MILESTONES.md` |
| Géométrie L1 des profils finis | FORMALIZED AND AUDITED | `Metrics/FiniteProfileL1.lean` |
| Distance nulle équivalente à `SameRecord` | FORMALIZED AND AUDITED | `Metrics/RecordProfileL1.lean` |
| Borne état-vers-record ED2A | FORMALIZED AND AUDITED | `Metrics/StateRecordPerturbation.lean` |
| Borne ED2B sans facteur de cardinalité | FORMALIZED AND AUDITED | `Metrics/StateRecordDimensionFree.lean` |
| Optimalité de la constante de perturbation | NOT CLAIMED | `docs/ED2B_DIMENSION_FREE_PERTURBATION.md` |
| Extension aux états mixtes | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Extension à un POVM arbitraire | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Défaut de commutation statewise ED3A | FORMALIZED AND AUDITED | `Approximation/ProjectorCommutator.lean` — algébrique, indépendant de Born |
| Transfert ED3A vers `recordProfileL1` | FORMALIZED AND AUDITED | `Approximation/ApproximateRecordPreservation.lean` — BORN-SENSITIVE |
| Commutateurs comme `ContinuousLinearMap` | FORMALIZED AND AUDITED | `Approximation/OperatorNormProjectorCommutator.lean` |
| Profil de normes d'opérateur | FORMALIZED AND AUDITED | `Approximation/OperatorNormProjectorCommutator.lean` |
| Agrégat L2 uniforme ED3B | FORMALIZED AND AUDITED | `Approximation/OperatorNormProjectorCommutator.lean` — indépendant de l'état pour `D` et `U` fixés |
| Défaut statewise contrôlé par ED3B | FORMALIZED AND AUDITED | `Approximation/OperatorNormProjectorCommutator.lean` |
| Borne normalisée uniforme avec constante 2 | FORMALIZED AND AUDITED | `Approximation/UniformRecordPreservation.lean` |
| Défaut uniforme nul ssi commutation globale | FORMALIZED AND AUDITED | `Approximation/OperatorNormProjectorCommutator.lean` |
| Défaut uniforme nul implique `SameRecord` pour tout état | FORMALIZED AND AUDITED | `Approximation/UniformRecordPreservation.lean` |
| Uniformité sur les perspectives | NOT FORMALIZED | `docs/ED3B_OPERATOR_NORM_UNIFORMIZATION.md` |
| Indépendance du nombre de cellules de l'agrégat d'opérateurs | NOT FORMALIZED | `docs/ED3B_OPERATOR_NORM_UNIFORMIZATION.md` |
| Composition de transformations | NOT FORMALIZED | `docs/SCIENTIFIC_ROADMAP.md` |
| Itération et accumulation d'erreurs | NOT FORMALIZED | `docs/SCIENTIFIC_ROADMAP.md` |
| Dynamique temporelle | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Système ouvert | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Canal | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| État mixte | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Décohérence | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Sélection de base émergente | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Redondance environnementale | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |

## English

| Item | Status | Evidence |
|---|---|---|
| Two stable upstream facade imports | VERIFIED BY COMPILATION | `Core/UpstreamAPI.lean` |
| Pinned upstream tag | VERIFIED BY MANIFEST | `lake-manifest.json` |
| Upstream axiom audit | VERIFIED | `Audit/UpstreamAPIContract.lean` |
| Local decoherence result | NOT CLAIMED | `docs/PROGRAM_STATUS.md` |
| Open-system dynamics | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Quantum channel | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| System/environment tensor factor | NOT ASSUMED | `AGENTS.md` |
| Basis selection | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Stable local API | NONE | `docs/API_STABILITY.md` |
| Local release | NONE | `MILESTONES.md` |
| Finite-profile L1 geometry | FORMALIZED AND AUDITED | `Metrics/FiniteProfileL1.lean` |
| Zero distance equivalent to `SameRecord` | FORMALIZED AND AUDITED | `Metrics/RecordProfileL1.lean` |
| ED2A state-to-record bound | FORMALIZED AND AUDITED | `Metrics/StateRecordPerturbation.lean` |
| ED2B bound without a cardinality factor | FORMALIZED AND AUDITED | `Metrics/StateRecordDimensionFree.lean` |
| Optimal perturbation constant | NOT CLAIMED | `docs/ED2B_DIMENSION_FREE_PERTURBATION.md` |
| Mixed-state extension | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Arbitrary POVM extension | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| ED3A statewise commutation defect | FORMALIZED AND AUDITED | `Approximation/ProjectorCommutator.lean` — algebraic, Born-independent |
| ED3A transfer to `recordProfileL1` | FORMALIZED AND AUDITED | `Approximation/ApproximateRecordPreservation.lean` — BORN-SENSITIVE |
| Commutators as `ContinuousLinearMap` | FORMALIZED AND AUDITED | `Approximation/OperatorNormProjectorCommutator.lean` |
| Operator-norm profile | FORMALIZED AND AUDITED | `Approximation/OperatorNormProjectorCommutator.lean` |
| ED3B uniform L2 aggregate | FORMALIZED AND AUDITED | `Approximation/OperatorNormProjectorCommutator.lean` — independent of the state for fixed `D` and `U` |
| Statewise defect controlled by ED3B | FORMALIZED AND AUDITED | `Approximation/OperatorNormProjectorCommutator.lean` |
| Normalized uniform bound with constant 2 | FORMALIZED AND AUDITED | `Approximation/UniformRecordPreservation.lean` |
| Zero uniform defect iff global commutation | FORMALIZED AND AUDITED | `Approximation/OperatorNormProjectorCommutator.lean` |
| Zero uniform defect implies `SameRecord` for every state | FORMALIZED AND AUDITED | `Approximation/UniformRecordPreservation.lean` |
| Uniformity over perspectives | NOT FORMALIZED | `docs/ED3B_OPERATOR_NORM_UNIFORMIZATION.md` |
| Cell-count independence of the operator aggregate | NOT FORMALIZED | `docs/ED3B_OPERATOR_NORM_UNIFORMIZATION.md` |
| Composition of transformations | NOT FORMALIZED | `docs/SCIENTIFIC_ROADMAP.md` |
| Iteration and error accumulation | NOT FORMALIZED | `docs/SCIENTIFIC_ROADMAP.md` |
| Time dynamics | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Open system | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Channel | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Mixed state | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Decoherence | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Emergent basis selection | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Environmental redundancy | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |

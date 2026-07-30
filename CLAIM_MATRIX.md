# Claim matrix

## Français

| Élément | Statut | Justification |
|---|---|---|
| Imports des deux façades stables amont | VERIFIED BY COMPILATION | `Core/UpstreamAPI.lean` |
| Tag amont épinglé | VERIFIED BY MANIFEST | `lake-manifest.json` |
| Audit d'axiomes amont | VERIFIED | `Audit/UpstreamAPIContract.lean` |
| Résultat local de décorrélation | NOT CLAIMED | `docs/PROGRAM_STATUS.md` |
| Robustesse quantitative locale | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Dynamique de système ouvert | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Canal quantique | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Facteur tensoriel système/environnement | NOT ASSUMED | `AGENTS.md` |
| Sélection de base | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| API locale stable | NONE | `docs/API_STABILITY.md` |
| Release locale | NONE | `MILESTONES.md` |

## English

| Item | Status | Evidence |
|---|---|---|
| Two stable upstream facade imports | VERIFIED BY COMPILATION | `Core/UpstreamAPI.lean` |
| Pinned upstream tag | VERIFIED BY MANIFEST | `lake-manifest.json` |
| Upstream axiom audit | VERIFIED | `Audit/UpstreamAPIContract.lean` |
| Local decoherence result | NOT CLAIMED | `docs/PROGRAM_STATUS.md` |
| Local quantitative robustness | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Open-system dynamics | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Quantum channel | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| System/environment tensor factor | NOT ASSUMED | `AGENTS.md` |
| Basis selection | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Stable local API | NONE | `docs/API_STABILITY.md` |
| Local release | NONE | `MILESTONES.md` |
| finiteProfileL1 | FORMALIZED AND AUDITED | `Metrics/FiniteProfileL1.lean` |
| recordProfileL1 | FORMALIZED AND AUDITED | `Metrics/RecordProfileL1.lean` |
| Zero distance iff SameRecord | FORMALIZED AND AUDITED | `Metrics/RecordProfileL1.lean` |
| Exact record orbit implies zero distance | FORMALIZED AND AUDITED | `Metrics/RecordProfileL1.lean` |
| Born-sensitive quantitative transfer layer | FORMALIZED | `docs/ED1_RECORD_PROFILE_GEOMETRY.md` |
| State perturbation, projector commutation | NOT FORMALIZED | `docs/SCIENTIFIC_ROADMAP.md` |
| Algebraic decoherence, stable and redundant records | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Dimension-free pure-state record-profile bound | FORMALIZED AND AUDITED | `Metrics/StateRecordDimensionFree.lean` |
| Normalized-state bound with constant 2 | FORMALIZED AND AUDITED | `Metrics/StateRecordDimensionFree.lean` |
| Dependence on record-cell count in strongest current bound | REMOVED | The best formalized bound no longer depends on it; no optimum is characterized. |
| Optimal perturbation constant | NOT CLAIMED | `docs/ED2B_DIMENSION_FREE_PERTURBATION.md` |
| Mixed-state extension | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Arbitrary POVM extension | NOT FORMALIZED | `docs/SCOPE_AND_LIMITATIONS.md` |
| Approximate commutation | NOT FORMALIZED | `docs/SCIENTIFIC_ROADMAP.md` |
| Dynamical record stability | NOT FORMALIZED | `docs/SCIENTIFIC_ROADMAP.md` |
| Decoherence theorem | NOT FORMALIZED | `docs/PROGRAM_STATUS.md` |

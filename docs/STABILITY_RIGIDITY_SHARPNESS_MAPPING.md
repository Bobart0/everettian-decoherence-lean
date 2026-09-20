# Stability, rigidity, and sharpness: paper ↔ Lean map

## Français

Ce document prépare la rédaction d'un article de mathématiques quantitatives
sur le front ouvert après T5, sans le renommer T6 et sans rouvrir ED5–ED12.
Titre de travail : *Sharp quantitative stability of finite projective records
under approximately commuting unitary transformations*.

Le noyau scientifique est NON BORN-SENSITIVE : il porte sur les normes
d'opérateur de commutateurs de projecteurs, l'enveloppe finie des cuts, la
rigidité des cas de saturation, la stabilité quantitative des quasi-saturants
et une famille explicite de sharpness. Il n'établit aucune dynamique
temporelle, aucune décohérence ni aucune émergence de perspective.

| Rôle dans le papier | Contenu mathématique | Déclaration Lean principale | Fichier Lean | Audit |
|---|---|---|---|---|
| Enveloppe des cuts | \(C_{\max}^2 \le \delta^2/2\) | `maxSubsetCommutatorOpNorm_sq_le_half_globalSq` | `Approximation/CutEnvelope.lean` | `Audit/StabilityRigiditySharpness.lean` |
| Rigidité exacte | pour \(\delta>0\), saturation ssi exactement deux cellules sont actives | `maxCut_saturation_iff_exactlyTwoActiveCellCommutators` | `Approximation/ExactTwoCellActiveRigidity.lean` | idem |
| Modulus de stabilité | \(\tau \le 2\eta + 36\eta/((1-3\eta)\rho^2)\) pour \(0\le\eta\le1/5\), \(\delta\ge\rho>0\) | `twoCellCommutatorConcentratedWithin_of_maxCut_near_saturated` | `Approximation/CutEnvelopeStability.lean` | idem |
| Corollaire linéaire | \(\tau \le \eta(2+72/\rho^2)\) pour \(\eta\le1/6\) | `twoCellCommutatorConcentratedWithin_linear_of_maxCut_near_saturated` | `Approximation/CutEnvelopeStability.lean` | idem |
| Formule rang 1 | identité exacte du budget d'une cellule rang 1 | `perspectiveProjectorCommutatorOpNormProfile_sq_rankOne` | `Approximation/RankOneCellCommutatorFormula.lean` | idem |
| Budget global de la famille | formule exacte de \(\delta_{n,m}^2\) | `stabilitySharpness_globalSq` | `Approximation/StabilitySharpness/GlobalBudget.lean` | idem |
| Cut maximal de la famille | \(C_{\max}=s_m\) | `stabilitySharpness_maxCut_eq_s` | `Approximation/StabilitySharpness/MaxCut.lean` | idem |
| Paramètre de quasi-saturation | formule exacte de \(\eta_{n,m}\) | `stabilitySharpnessEta_exact` | `Approximation/StabilitySharpness/EtaTail.lean` | idem |
| Queue top-two | formule exacte de \(\tau_{n,m}\) | `stabilitySharpnessTau_exact` | `Approximation/StabilitySharpness/EtaTail.lean` | idem |
| Ratio exact | \(\tau_{n,m}/\eta_{n,m}=(2-d_m B_n^2)/(2d_m A_n^2)\) | `stabilitySharpnessTau_div_Eta_exact` | `Approximation/StabilitySharpness/EtaTail.lean` | idem |
| Limite à \(m\) fixé | \(\tau/\eta \to 1/d_m\) | `stabilitySharpnessTau_div_Eta_tendsto_inv_D` | `Approximation/StabilitySharpness/Asymptotics.lean` | idem |
| Échelle du défaut | \(\delta_{n,m}^2\to2s_m^2\) | `stabilitySharpness_delta_sq_tendsto_two_s_sq` | `Approximation/StabilitySharpness/Asymptotics.lean` | idem |
| Sharpness d'échelle | la limite itérée de \((\tau/\eta)\delta^2\) vaut \(4\) | `stabilitySharpnessScaleLimit_tendsto_four` | `Approximation/StabilitySharpness/Asymptotics.lean` | idem |

La façade de production est
`EverettianDecoherence.Approximation.StabilitySharpness`. L'audit de
dépendances fondationnelles est
`EverettianDecoherence.Audit.StabilityRigiditySharpness`, agrégé par
`Audit/MainResults.lean`. Le statut « audité » doit être compris comme
compilation réussie de cette surface d'audit dans la CI de la branche finale.

## English

This document prepares a quantitative-mathematics paper around the front
opened after T5, without renaming it T6 and without reopening ED5–ED12.
Working title: *Sharp quantitative stability of finite projective records
under approximately commuting unitary transformations*.

The scientific core is NON BORN-SENSITIVE. It concerns operator norms of
projector commutators, the finite cut envelope, exact rigidity at saturation,
quantitative stability of near-saturators, and an explicit sharpness family.
It establishes no time dynamics, decoherence, or emergence of a perspective.

| Paper role | Mathematical content | Main Lean declaration | Lean file | Audit |
|---|---|---|---|---|
| Cut envelope | \(C_{\max}^2 \le \delta^2/2\) | `maxSubsetCommutatorOpNorm_sq_le_half_globalSq` | `Approximation/CutEnvelope.lean` | `Audit/StabilityRigiditySharpness.lean` |
| Exact rigidity | for \(\delta>0\), saturation iff exactly two cells are active | `maxCut_saturation_iff_exactlyTwoActiveCellCommutators` | `Approximation/ExactTwoCellActiveRigidity.lean` | same |
| Stability modulus | \(\tau \le 2\eta + 36\eta/((1-3\eta)\rho^2)\) for \(0\le\eta\le1/5\), \(\delta\ge\rho>0\) | `twoCellCommutatorConcentratedWithin_of_maxCut_near_saturated` | `Approximation/CutEnvelopeStability.lean` | same |
| Linear corollary | \(\tau \le \eta(2+72/\rho^2)\) for \(\eta\le1/6\) | `twoCellCommutatorConcentratedWithin_linear_of_maxCut_near_saturated` | `Approximation/CutEnvelopeStability.lean` | same |
| Rank-one formula | exact rank-one cell budget identity | `perspectiveProjectorCommutatorOpNormProfile_sq_rankOne` | `Approximation/RankOneCellCommutatorFormula.lean` | same |
| Family global budget | exact formula for \(\delta_{n,m}^2\) | `stabilitySharpness_globalSq` | `Approximation/StabilitySharpness/GlobalBudget.lean` | same |
| Family maximal cut | \(C_{\max}=s_m\) | `stabilitySharpness_maxCut_eq_s` | `Approximation/StabilitySharpness/MaxCut.lean` | same |
| Near-saturation parameter | exact formula for \(\eta_{n,m}\) | `stabilitySharpnessEta_exact` | `Approximation/StabilitySharpness/EtaTail.lean` | same |
| Top-two tail | exact formula for \(\tau_{n,m}\) | `stabilitySharpnessTau_exact` | `Approximation/StabilitySharpness/EtaTail.lean` | same |
| Exact ratio | \(\tau_{n,m}/\eta_{n,m}=(2-d_m B_n^2)/(2d_m A_n^2)\) | `stabilitySharpnessTau_div_Eta_exact` | `Approximation/StabilitySharpness/EtaTail.lean` | same |
| Fixed-\(m\) limit | \(\tau/\eta \to 1/d_m\) | `stabilitySharpnessTau_div_Eta_tendsto_inv_D` | `Approximation/StabilitySharpness/Asymptotics.lean` | same |
| Defect scale | \(\delta_{n,m}^2\to2s_m^2\) | `stabilitySharpness_delta_sq_tendsto_two_s_sq` | `Approximation/StabilitySharpness/Asymptotics.lean` | same |
| Scale sharpness | the iterated limit of \((\tau/\eta)\delta^2\) is \(4\) | `stabilitySharpnessScaleLimit_tendsto_four` | `Approximation/StabilitySharpness/Asymptotics.lean` | same |

The production facade is
`EverettianDecoherence.Approximation.StabilitySharpness`. The foundational
dependency audit is
`EverettianDecoherence.Audit.StabilityRigiditySharpness`, aggregated by
`Audit/MainResults.lean`. “Audited” means that this audit surface compiles
successfully in the final branch CI.

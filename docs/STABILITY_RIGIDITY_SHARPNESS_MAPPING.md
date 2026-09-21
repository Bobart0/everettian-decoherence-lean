# Stability, rigidity, and sharpness: paper ↔ Lean map

## Français

Ce document prépare la rédaction d'un article de mathématiques quantitatives
sur le front ouvert après T5, sans le renommer T6 et sans rouvrir ED5–ED12.
Titre du manuscrit v12 : *Rigidity and Scale-Sharp Stability for Gaps of Finite Orthogonal Decompositions*.

Le noyau scientifique est NON BORN-SENSITIVE : il porte sur les normes
d'opérateur de commutateurs de projecteurs, l'enveloppe finie des cuts, la
rigidité des cas de saturation, la stabilité quantitative des quasi-saturants
et une famille explicite de sharpness. Il n'établit aucune dynamique
temporelle, aucune décohérence ni aucune émergence de perspective.

| Rôle dans le papier | Contenu mathématique | Déclaration Lean principale | Fichier Lean | Audit |
|---|---|---|---|---|
| Enveloppe des cuts | \(C_{\max}^2 \le \delta^2/2\) | `maxSubsetCommutatorOpNorm_sq_le_half_globalSq` | `Approximation/CutEnvelope.lean` | `Audit/StabilityRigiditySharpness.lean` |
| Rigidité exacte | pour \(\delta>0\), saturation ssi exactement deux cellules sont actives | `maxCut_saturation_iff_exactlyTwoActiveCellCommutators` | `Approximation/ExactTwoCellActiveRigidity.lean` | idem |
| Modulus de stabilité v12 | \(\tau \le 2\eta + 18\eta/((1-3\eta)\rho^2)\) pour \(0\le\eta\le1/5\), \(\delta\ge\rho>0\) | `twoCellCommutatorConcentratedWithin18_of_maxCut_near_saturated` | `Approximation/CutEnvelopeStabilitySharp.lean` | idem |
| Corollaire linéaire v12 | \(\tau \le \eta(2+36/\rho^2)\) pour \(\eta\le1/6\) | `twoCellCommutatorConcentratedWithin18_linear_of_maxCut_near_saturated` | `Approximation/CutEnvelopeStabilitySharp.lean` | idem |
| Coefficient asymptotique général | pour \(\delta^2\to0\), \(\eta\to0\), toute constante \(c>8\) contrôle finalement la queue absolue par \(c\eta\), uniformément en dimension/cardinalité | `eventually_two_cell_tail_le_of_small_defect` | `Approximation/V12AsymptoticEight.lean` | idem |
| Optimalité du 8 | une sous-famille explicite vérifie \(\delta^2\tau/\eta\to8\) | `stabilitySharpnessScaledRatioV12_zero_tendsto_eight` | `Approximation/StabilitySharpness/V12SharpConstants.lean` | idem |
| Régime ultra-near | si en plus \(\eta/\delta^2\to0\), toute constante \(c>4\) contrôle finalement la queue absolue par \(c\eta\) | `eventually_two_cell_tail_le_of_ultra_near` | `Approximation/V12UltraNearFour.lean` | idem |
| Optimalité du 4 ultra-near | une sous-famille explicite vérifie \(\eta/\delta^2\to0\) et \(\delta^2\tau/\eta\to4\) | `stabilitySharpnessScaledRatioV12_diag_tendsto_four`, `stabilitySharpnessEta_div_deltaSq_diag_tendsto_zero` | `Approximation/StabilitySharpness/V12SharpConstants.lean` | idem |
| Réalisation continue C3 | construction explicite de \(U_{d,x}=Q_xR_dQ_x^*\) pour \(0\le x\le1\), \(0\le d\le2\) | `v12TwoParamRotationMatrix_mem_unitary`, `v12TwoParamRotation` | `Approximation/StabilitySharpness/V12TwoParameterGeometry.lean` | idem |
| Profil exact des trois gaps | \(p_0=f_d(1-x)\), \(p_1=f_d(x)\), \(p_2=f_d(1)\), \(f_d(y)=2dy-d^2y^2\) | `v12TwoParamCell0_budget_sq`, `v12TwoParamCell1_budget_sq`, `v12TwoParamCell2_budget_sq` | `Approximation/StabilitySharpness/V12TwoParameterGeometry.lean` | idem |
| Invariants continus | \(A_{d,x}=4d-2d^2+2x(1-x)d^2\), \(G_{\max}^2=f_d(1)\), \(E_{d,x}=2x(1-x)d^2\), queue absolue \(=f_d(\min\{x,1-x\})\) | `v12TwoParam_globalSq`, `v12TwoParam_maxCut_sq_eq_gap_one`, `v12TwoParam_envelopeDefect`, `v12TwoParam_min_cell_budget_eq_tail` | `Approximation/StabilitySharpness/V12TwoParameterInvariants.lean` | idem |
| Interpolation continue sharp | pour \(x\in(0,1)\) fixé et \(d\to0\), \(A\to0\), \(\eta\to0\) et \(A\tau/\eta\to4/\max\{x,1-x\}\) | `v12TwoParamGlobal_tendsto_zero`, `v12TwoParamEta_tendsto_zero`, `v12TwoParamScaledRatio_tendsto_fixed_x` | `Approximation/StabilitySharpness/V12TwoParameterAsymptotics.lean` | idem |
| Chemin symétrique continu | \(x=1/2\) : \(A\tau/\eta=8-5d+\tfrac34d^2\to8\) | `v12TwoParamScaledRatio_half_exact`, `v12TwoParamScaledRatio_half_tendsto_eight` | `Approximation/StabilitySharpness/V12TwoParameterAsymptotics.lean` | idem |
| Chemin ultra-near continu | \(x=d\) : \(\eta/A\to0\) et \(A\tau/\eta\to4\) | `v12TwoParamEtaOverGlobal_diag_tendsto_zero`, `v12TwoParamScaledRatio_diag_tendsto_four` | `Approximation/StabilitySharpness/V12TwoParameterAsymptotics.lean` | idem |
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
v12 manuscript title: *Rigidity and Scale-Sharp Stability for Gaps of Finite Orthogonal Decompositions*.

The scientific core is NON BORN-SENSITIVE. It concerns operator norms of
projector commutators, the finite cut envelope, exact rigidity at saturation,
quantitative stability of near-saturators, and an explicit sharpness family.
It establishes no time dynamics, decoherence, or emergence of a perspective.

| Paper role | Mathematical content | Main Lean declaration | Lean file | Audit |
|---|---|---|---|---|
| Cut envelope | \(C_{\max}^2 \le \delta^2/2\) | `maxSubsetCommutatorOpNorm_sq_le_half_globalSq` | `Approximation/CutEnvelope.lean` | `Audit/StabilityRigiditySharpness.lean` |
| Exact rigidity | for \(\delta>0\), saturation iff exactly two cells are active | `maxCut_saturation_iff_exactlyTwoActiveCellCommutators` | `Approximation/ExactTwoCellActiveRigidity.lean` | same |
| v12 stability modulus | \(\tau \le 2\eta + 18\eta/((1-3\eta)\rho^2)\) for \(0\le\eta\le1/5\), \(\delta\ge\rho>0\) | `twoCellCommutatorConcentratedWithin18_of_maxCut_near_saturated` | `Approximation/CutEnvelopeStabilitySharp.lean` | same |
| v12 linear corollary | \(\tau \le \eta(2+36/\rho^2)\) for \(\eta\le1/6\) | `twoCellCommutatorConcentratedWithin18_linear_of_maxCut_near_saturated` | `Approximation/CutEnvelopeStabilitySharp.lean` | same |
| General asymptotic coefficient | if \(\delta^2\to0\) and \(\eta\to0\), every \(c>8\) eventually bounds the absolute two-cell tail by \(c\eta\), uniformly in dimension/cardinality | `eventually_two_cell_tail_le_of_small_defect` | `Approximation/V12AsymptoticEight.lean` | same |
| Sharpness of 8 | an explicit subfamily satisfies \(\delta^2\tau/\eta\to8\) | `stabilitySharpnessScaledRatioV12_zero_tendsto_eight` | `Approximation/StabilitySharpness/V12SharpConstants.lean` | same |
| Ultra-near regime | if additionally \(\eta/\delta^2\to0\), every \(c>4\) eventually bounds the absolute two-cell tail by \(c\eta\) | `eventually_two_cell_tail_le_of_ultra_near` | `Approximation/V12UltraNearFour.lean` | same |
| Ultra-near sharpness of 4 | an explicit subfamily satisfies \(\eta/\delta^2\to0\) and \(\delta^2\tau/\eta\to4\) | `stabilitySharpnessScaledRatioV12_diag_tendsto_four`, `stabilitySharpnessEta_div_deltaSq_diag_tendsto_zero` | `Approximation/StabilitySharpness/V12SharpConstants.lean` | same |
| Continuous C3 realization | explicit construction of \(U_{d,x}=Q_xR_dQ_x^*\) for \(0\le x\le1\), \(0\le d\le2\) | `v12TwoParamRotationMatrix_mem_unitary`, `v12TwoParamRotation` | `Approximation/StabilitySharpness/V12TwoParameterGeometry.lean` | same |
| Exact three-gap profile | \(p_0=f_d(1-x)\), \(p_1=f_d(x)\), \(p_2=f_d(1)\), \(f_d(y)=2dy-d^2y^2\) | `v12TwoParamCell0_budget_sq`, `v12TwoParamCell1_budget_sq`, `v12TwoParamCell2_budget_sq` | `Approximation/StabilitySharpness/V12TwoParameterGeometry.lean` | same |
| Continuous invariants | \(A_{d,x}=4d-2d^2+2x(1-x)d^2\), \(G_{\max}^2=f_d(1)\), \(E_{d,x}=2x(1-x)d^2\), absolute tail \(=f_d(\min\{x,1-x\})\) | `v12TwoParam_globalSq`, `v12TwoParam_maxCut_sq_eq_gap_one`, `v12TwoParam_envelopeDefect`, `v12TwoParam_min_cell_budget_eq_tail` | `Approximation/StabilitySharpness/V12TwoParameterInvariants.lean` | same |
| Continuous sharp interpolation | for fixed \(x\in(0,1)\) and \(d\to0\), \(A\to0\), \(\eta\to0\), and \(A\tau/\eta\to4/\max\{x,1-x\}\) | `v12TwoParamGlobal_tendsto_zero`, `v12TwoParamEta_tendsto_zero`, `v12TwoParamScaledRatio_tendsto_fixed_x` | `Approximation/StabilitySharpness/V12TwoParameterAsymptotics.lean` | same |
| Continuous symmetric path | \(x=1/2\): \(A\tau/\eta=8-5d+\tfrac34d^2\to8\) | `v12TwoParamScaledRatio_half_exact`, `v12TwoParamScaledRatio_half_tendsto_eight` | `Approximation/StabilitySharpness/V12TwoParameterAsymptotics.lean` | same |
| Continuous ultra-near path | \(x=d\): \(\eta/A\to0\) and \(A\tau/\eta\to4\) | `v12TwoParamEtaOverGlobal_diag_tendsto_zero`, `v12TwoParamScaledRatio_diag_tendsto_four` | `Approximation/StabilitySharpness/V12TwoParameterAsymptotics.lean` | same |
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

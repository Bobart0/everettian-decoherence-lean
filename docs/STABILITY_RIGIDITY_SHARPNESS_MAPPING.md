# Stability, rigidity, and small-scale sharpness: manuscript v19 ↔ Lean

This file is the theorem-to-code map for the LAA manuscript
*Rigidity, Stability, and Small-Scale Sharpness for Gaps of Finite Orthogonal Decompositions* (v19).

The front is algebraic and **NON BORN-SENSITIVE**. It concerns finite orthogonal
projective decompositions, unitary conjugation, projector commutators, maximal
cuts, inverse stability, and explicit sharpness families. It adds no time
dynamics, decoherence, emergent basis, or new physical milestone.

## Status legend

- **EXACT** — the Lean declaration states the manuscript quantity/result directly.
- **EQUIVALENT** — Lean uses an equivalent eventual formulation (for example
  every (c>8) eventually works instead of explicit limsup notation).
- **COMPONENTS** — all proof-bearing ingredients are machine-checked, but the
  manuscript's outer order-theoretic packaging is not a single Lean object.

## Core theorem chain

| Manuscript claim | Main Lean declaration(s) | Status | Lean file |
|---|---|---:|---|
| (G_{\max}^2\le\delta^2/2) | `maxSubsetCommutatorOpNorm_sq_le_half_globalSq` | EXACT | `Approximation/CutEnvelope.lean` |
| Positive-defect equality iff exactly two cells are active | `maxCut_saturation_iff_exactlyTwoActiveCellCommutators` | EXACT | `Approximation/ExactTwoCellActiveRigidity.lean` |
| Exact optimal top-two tail (\tau) | `optimalTwoCellTail`, `optimalTwoCellTailFraction` | EXACT | `Approximation/OptimalTwoCellTail.lean` |
| Finite stability with coefficient (18) | `optimalTwoCellTailFraction_le_18_expanded` | EXACT | `Approximation/StabilitySharpness/PublicationFacingTail.lean` |
| General small-scale coefficient (8) | `eventually_globalSq_mul_optimalTau_le_of_small_defect` | EQUIVALENT | same |
| Ultra-near coefficient (4) | `eventually_globalSq_mul_optimalTau_le_of_ultra_near` | EQUIVALENT | same |
| Exact normalized (\eta) and (\tau) | `exactMaxCutEta`, `exactTwoCellTau` | EXACT | `Approximation/ExactStabilityParameters.lean` |
| Pointwise finite slope bound for (\tau/\eta) | `exactTwoCellSlope_le_18` | EXACT | same |

## Continuous three-cell sharpness family

| Manuscript claim | Main Lean declaration(s) | Status |
|---|---|---:|
| Explicit (\mathbb C^3) unitary family | `v12TwoParamRotationMatrix_mem_unitary`, `v12TwoParamRotation` | EXACT |
| Three exact cell gaps | `v12TwoParamCell0_budget_sq`, `v12TwoParamCell1_budget_sq`, `v12TwoParamCell2_budget_sq` | EXACT |
| Exact (A,G_{\max}^2,E), top-two tail | `v12TwoParam_globalSq`, `v12TwoParam_maxCut_sq_eq_gap_one`, `v12TwoParam_envelopeDefect`, `v12TwoParam_min_cell_budget_eq_tail` | EXACT |
| Fixed-(x) interpolation | `v12TwoParamScaledRatio_tendsto_fixed_x` | EXACT |
| Symmetric path gives (8) | `v12TwoParamScaledRatio_half_tendsto_eight` | EXACT |
| Ultra-near path gives (4), with (\eta/A\to0) | `v12TwoParamScaledRatio_diag_tendsto_four`, `v12TwoParamEtaOverGlobal_diag_tendsto_zero` | EXACT |

These declarations live under
`Approximation/StabilitySharpness/V12TwoParameter*.lean`.

## Fixed-positive-budget proposition

The manuscript defines (F_{A_0}(\varepsilon)) by a supremum over all
admissible finite-dimensional pairs and
(C_{\mathrm{fix}}(A_0)=\lim_{\varepsilon\downarrow0}F_{A_0}(\varepsilon)).

The literal cross-dimensional `sSup`/limit wrapper is **not** introduced as a
Lean object. The proof-bearing content is machine-checked:

| Proof ingredient | Lean declaration | Status |
|---|---|---:|
| Fixed positive budget and (\eta\to0) force the ultra-near regime | `fixedPositiveBudget_forces_ultraNear` | EXACT |
| Finite local slope upper estimate | `exactTwoCellSlope_le_18` | EXACT |
| Three-cell path has (A\to4d-2d^2) | `v19FixedBudgetGlobal_tendsto_base` | EXACT |
| Three-cell lower slope (\tau/\eta\to1/d) | `v19FixedBudgetSlopePath_tendsto_inv` | EXACT |
| (A_0/d\to4) lower-asymptotic mechanism | `v18FixedBudgetScaledLower_tendsto_four` | EXACT |
| Diagonal extraction forces (A\to0,\eta\to0,\eta/A\to0) | `fixedBudgetDiagonal_budget_tendsto_zero`, `fixedBudgetDiagonal_eta_tendsto_zero`, `fixedBudgetDiagonal_forces_ultraNear` | EXACT |
| Coefficient-(4) diagonal contradiction mechanism | `eventually_two_cell_tail_le_of_fixedBudgetDiagonal` | EQUIVALENT |

Thus the mathematical inequalities and asymptotic constant (4) are formally
supported; only the outer definition/existence of the single function
(C_{\mathrm{fix}}) remains manuscript-level packaging.

## Diffuse (2m)-cell family

| Manuscript equation/result | Lean declaration | Status |
|---|---|---:|
| Uniform modes are orthonormal | `diffuseModes_orthonormal` | EXACT |
| Plane rotation and identity on the orthogonal complement | `diffuseRotation_apply_left`, `diffuseRotation_apply_right`, `diffuseRotation_apply_of_orthogonal` | EXACT |
| Coordinate diagonal (\langle e_i,Ue_i\rangle=1-d/m) | `diffuseLeftFamily_diagonal`, `diffuseRightFamily_diagonal` | EXACT |
| (p_i=2d/m-d^2/m^2) | `diffuseAnyCell_budget_sq` + `v18DiffuseCellBudget` | EXACT |
| (A=\delta^2=4d-2d^2/m) | `diffuseGlobal_budget_sq_exact` | EXACT |
| (G_{\max}^2=\sin^2\theta=2d-d^2) | `diffuseMaxCut_sq_eq` | EXACT |
| (E=2d^2(1-1/m)) | `diffuseEnvelopeDefect_exact` | EXACT |
| (\tau=1-1/m) | `diffuseOptimalTwoCellTailFraction_eq_tau` | EXACT |
| (A\tau/\eta=8(1-d/(2m))^2) | `diffuseScaledRatio_exact` | EXACT |
| Exact geometric (\eta/A) identity | `diffuse_exactEta_over_globalSq_eq` | EXACT |
| Universal (\liminf\eta_n/\delta_n^2\ge1/8) when (\tau_n\to1) | `eventually_lt_exactEta_over_globalSq_of_tau_tendsto_one` | EQUIVALENT |
| Attainment for (m_n\to\infty,\theta_n\to0) | `diffuse_completeDiffusion_attains_eighth` | EXACT |

The tangent/Taylor expansions in the discussion remain ordinary manuscript
analysis; no separate formal power-series theorem is claimed.

## Audit and archive scope

The production facade is
`EverettianDecoherence.Approximation.StabilitySharpness`.
The publication-facing audit is
`EverettianDecoherence.Audit.StabilityRigiditySharpness`, imported by
`Audit/MainResults.lean`. The audit checks the new declarations and prints
axiom dependencies for the principal finite, asymptotic, fixed-budget, diffuse,
and threshold results.

The historical archival release `v0.1.0` (Zenodo DOI
`10.5281/zenodo.22879172`) predates this v19 catch-up and must not be cited as
containing the added diffuse/fixed-budget formalization. A new archival
checkpoint should be minted after the final merged commit is green.

## Français — résumé de portée

Le rattrapage v19 formalise les paramètres exacts (\eta,\tau), les versions
publication-facing des constantes (18,8,4), les ingrédients complets de la
proposition à budget fixé, la famille diffuse géométrique (2m)-cellules et le
seuil sharp (1/8). La seule différence de représentation substantielle est
l'absence d'un objet Lean unique
(C_{\mathrm{fix}}(A_0)=\lim_{\varepsilon\downarrow0}\sup\cdots) ; les
lemmes qui portent sa preuve sont séparément machine-checkés.

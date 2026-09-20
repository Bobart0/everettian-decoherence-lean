# Mathematical audit — manuscript v0.4 vs Lean

Reference manuscript: `paper/stability_rigidity_sharpness_v05_submission.tex`

Reference Lean head inherited by the paper branch:
`81eb3ff53f6219749b84491513ff437fe7c545c1`.

Status legend:
- **EXACT**: manuscript statement is the same mathematical statement, modulo notation.
- **DERIVED**: immediate algebraic reformulation of an audited Lean statement.
- **EXPOSITORY**: proof narrative / motivation, not itself a Lean declaration.

| Manuscript item | Status | Lean declaration / justification |
|---|---|---|
| `p_i = ||[P_i,U]||_op^2`, `delta^2 = sum_i p_i` | EXACT | `cellCommutatorOpNormSq`; `sum_cellCommutatorOpNormSq_eq_globalSq` |
| Cut complement has same commutator norm | EXACT | `recordSubsetProjectorCommutatorCLM_opNorm_compl` |
| `C_S^2 <= sum_{i in S} p_i` | EXACT | `recordSubsetProjectorCommutatorCLM_opNorm_sq_le_subsetSq` |
| `C_S^2 <= sum_{i notin S} p_i` | EXACT | `recordSubsetProjectorCommutatorCLM_opNorm_sq_le_complSq` |
| `C_max^2 <= delta^2/2` | EXACT | `maxSubsetCommutatorOpNorm_sq_le_half_globalSq` |
| One-sided cut concentration with `2e + 18e/(C^2-e)` | EXACT | `exists_cell_concentration_of_cut` |
| Bilateral cut concentration with `2E + 18E/(C^2-E)` | EXACT | `exists_two_cell_concentration_of_cut` |
| Near-saturation condition `C_max^2 >= (1-eta) delta^2/2` | DERIVED | Algebraically equivalent to the hypothesis of `twoCellCommutatorConcentratedWithin_of_maxCut_near_saturated` |
| `tau <= 2 eta + 36 eta / ((1-3 eta) rho^2)` | EXACT / notation | `twoCellCommutatorConcentratedWithin_of_maxCut_near_saturated`; manuscript `tau` is the normalized optimal two-cell tail |
| Linear form `tau <= eta (2 + 72/rho^2)` for `eta <= 1/6` | EXACT / notation | `twoCellCommutatorConcentratedWithin_linear_of_maxCut_near_saturated` |
| Saturation iff exactly two active cells for `delta>0` | EXACT | `maxCut_saturation_iff_exactlyTwoActiveCellCommutators` |
| Rank-one identity `||[P_e,U]||_op^2 = 1-|<e,Ue>|^2` | EXACT | `perspectiveProjectorCommutatorOpNormProfile_sq_rankOne` |
| Three cell budgets `p_0,p_1,p_2` | EXACT | `stabilitySharpnessCell0_budget_sq`, `stabilitySharpnessCell1_budget_sq`, `stabilitySharpnessCell2_budget_sq` |
| `delta_nm^2 = 2 s_m^2 + 2 d_m^2 A_n^2 B_n^2` | EXACT | `stabilitySharpness_globalSq` |
| `C_max(n,m)=s_m` | EXACT | `stabilitySharpness_maxCut_eq_s` |
| Formula for `eta_nm` | EXACT | `stabilitySharpnessEta_exact` |
| Formula for retained-pair `tau_nm` | EXACT | `stabilitySharpnessTau_exact` |
| `tau_nm/eta_nm = (2-d_m B_n^2)/(2 d_m A_n^2)` | EXACT | `stabilitySharpnessTau_div_Eta_exact` |
| Fixed-`m` limit `tau/eta -> 1/d_m` | EXACT | `stabilitySharpnessTau_div_Eta_tendsto_inv_D` |
| Fixed-`m` limit `delta^2 -> 2 s_m^2` | EXACT | `stabilitySharpness_delta_sq_tendsto_two_s_sq` |
| `2s_m^2/d_m = 4-2d_m` | EXACT / algebra | `stabilitySharpnessScaleLimit_eq_four_sub_two_D` |
| Iterated scaled limit equals `4` | EXACT | `stabilitySharpnessScaleLimit_tendsto_four` |
| Claim that inverse-square scale is necessary up to constants | DERIVED | Follows from the exact ratio and iterated limit above |
| Literature/priority statements | EXPOSITORY | Must be supported by external literature audit, not Lean |
| Discussion of decoherence / physical interpretation | EXPOSITORY | Explicit scope limitation; not a formal theorem |

## Notes requiring continued editorial care

1. The manuscript's scalar `tau` is an optimal normalized two-cell tail. Lean's principal stability theorem uses the division-free predicate `TwoCellCommutatorConcentratedWithin`; equivalence is valid for positive `delta`.
2. The sharpness-family `stabilitySharpnessTau` is exactly the canonical optimal top-two tail: `stabilitySharpnessTopTwoTail_eq_Tau` proves that cell 1 has the smallest of the three budgets, so retaining cells 0 and 2 is optimal.
3. Constants 36 and 72 are certified but are **not** claimed optimal.
4. The constant 4 is a limit for the explicit sharpness family, not a universal optimal stability constant.
5. No Born-rule, decoherence, time-dynamics, or preferred-basis theorem is claimed by this paper.

# Mathematical audit — manuscript v0.7 vs Lean

Reference manuscript: `paper/stability_rigidity_sharpness_v07_submission.tex`

Reference Lean head inherited by the paper branch:
`81eb3ff53f6219749b84491513ff437fe7c545c1`.

Status legend:
- **EXACT**: same mathematical statement as a checked Lean declaration, modulo notation.
- **DERIVED**: immediate mathematical reformulation of checked declarations.
- **EXTERNAL**: standard interpretation or definition supported by the literature.
- **EXPOSITORY**: motivation or proof narrative, not itself a Lean declaration.

| Manuscript item | Status | Lean declaration / justification |
|---|---|---|
| `p_i = ||[P_i,U]||_op^2`, `delta^2 = sum_i p_i` | EXACT | `cellCommutatorOpNormSq`; `sum_cellCommutatorOpNormSq_eq_globalSq` |
| `Q_i = U P_i U^*` and `||[P_i,U]|| = ||P_i-Q_i||` | DERIVED | Right multiplication of `[P_i,U]` by the unitary `U^*`; norm preservation |
| `C_S = ||P_S-Q_S||` | DERIVED | Same unitary-right-multiplication identity for the aggregate projector |
| `C_max = D_op(P,Q)` for `Q_i=UP_iU^*` | DERIVED + EXTERNAL | Derived from preceding identity; `D_op` subset-max formula is standard in the measurement literature |
| Matched-rank PVM pair admits `Q_i=UP_iU^*` for one unitary `U` | DERIVED | Choose unitary isomorphisms `P_iH -> Q_iH` cellwise and take their orthogonal direct sum |
| `D_op(P,Q)^2 <= (1/2) sum_i ||P_i-Q_i||^2` for matched-rank PVMs | DERIVED | Operational-distance identities + `maxSubsetCommutatorOpNorm_sq_le_half_globalSq` |
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
| Formula for `tau_nm` | EXACT | `stabilitySharpnessTau_exact` |
| `tau_nm` is the optimal top-two tail | EXACT | `stabilitySharpnessTopTwoTail_eq_Tau`, using the two cell-budget ordering lemmas |
| `tau_nm/eta_nm = (2-d_m B_n^2)/(2 d_m A_n^2)` | EXACT | `stabilitySharpnessTau_div_Eta_exact` |
| Fixed-`m` limit `tau/eta -> 1/d_m` | EXACT | `stabilitySharpnessTau_div_Eta_tendsto_inv_D` |
| Fixed-`m` limit `delta^2 -> 2 s_m^2` | EXACT | `stabilitySharpness_delta_sq_tendsto_two_s_sq` |
| `2s_m^2/d_m = 4-2d_m` | EXACT / algebra | `stabilitySharpnessScaleLimit_eq_four_sub_two_D` |
| Iterated scaled limit equals `4` | EXACT | `stabilitySharpnessScaleLimit_tendsto_four` |
| Inverse-square scale necessary up to constants | DERIVED | Consequence of exact ratio and iterated limit |
| Generic POVM estimate `D_op <= (1/2) sum_i ||M_i-N_i||` | DERIVED | Uses `sum_i(M_i-N_i)=0` and triangle inequality; not part of Lean surface |
| Literature / priority statements | EXPOSITORY | External literature audit; deliberately not a theorem of the formalization |

## Editorial guardrails

1. The operational-distance corollary is a **derived reformulation**, not a separately formalized Lean theorem at the reference head.
2. The manuscript scalar `tau` is the optimal normalized two-cell tail; Lean's primary stability predicate is division-free and is equivalent when `delta>0`.
3. In the sharpness family, `stabilitySharpnessTau` is exactly the optimal top-two tail, not merely a selected-pair tail.
4. Constants 36 and 72 are certified but are not claimed optimal.
5. The constant 4 is an asymptotic obstruction realized by the explicit family, not a claimed universal best stability constant.
6. No Born-rule, decoherence, time-dynamics, or preferred-basis theorem is claimed by this paper.
7. The literature audit supports conservative wording such as “a targeted search did not identify”; it does not justify an absolute historical-priority claim.

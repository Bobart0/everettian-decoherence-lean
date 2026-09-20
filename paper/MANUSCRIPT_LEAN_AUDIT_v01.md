# Manuscript ↔ Lean audit — stability / rigidity / sharpness

Reference manuscript: \`paper/stability_rigidity_sharpness_v05_audited.tex\`

Formal reference head from which the paper branch was forked:
\`81eb3ff53f6219749b84491513ff437fe7c545c1\`.

Status convention:

- **DIRECT**: the paper statement is the mathematical rendering of a named Lean declaration.
- **DERIVED**: the statement is a short ordinary mathematical consequence of DIRECT declarations, but is not itself packaged under that exact paper statement in Lean.
- **EXPOSITORY**: notation, interpretation, or a compressed proof explanation rather than a distinct formal claim.

## 1. Setup and notation

| Paper item | Lean source | Status | Audit note |
|---|---|---|---|
| Cell budget \(p_i=\|[P_i,U]\|_{\mathrm{op}}^2\) | \`cellCommutatorOpNormSq\` | DIRECT | Exact definition. |
| Global budget \(\delta^2=\sum_i p_i\) | \`sum_cellCommutatorOpNormSq_eq_globalSq\` | DIRECT | Exact identity. |
| Finite cut maximum \(C_{\max}\) | \`maxSubsetCommutatorOpNorm\` | DIRECT | Maximum over the powerset; attainment is \`exists_subsetCommutatorOpNorm_eq_max\`. |
| General optimal two-cell tail \(\tau\) | paper definition; robust Lean predicate \`TwoCellCommutatorConcentratedWithin\` | DERIVED | Lean avoids division and does not define this global minimum. Under \(\delta>0\), the paper definition is equivalent to the existential tail bound used by Lean. |
| Coordinate-free finite-dimensional \(H\) | Lean uses canonical spaces \(H_n\) | DERIVED | The paper is invariant under unitary coordinate change. The explicit transport to an arbitrary abstract finite-dimensional Hilbert space is not separately packaged as a Lean theorem. |

## 2. Cut envelope

| Paper item | Lean source | Status | Audit note |
|---|---|---|---|
| \(C_S^2\le\sum_{i\in S}p_i\) | \`recordSubsetProjectorCommutatorCLM_opNorm_sq_le_subsetSq\` | DIRECT | Exact. |
| \(C_S^2\le\sum_{i\notin S}p_i\) | \`recordSubsetProjectorCommutatorCLM_opNorm_sq_le_complSq\` | DIRECT | Exact. |
| Complement cut has same norm | \`recordSubsetProjectorCommutatorCLM_opNorm_compl\` | DIRECT | Exact. |
| \(C_{\max}^2\le\delta^2/2\) | \`maxSubsetCommutatorOpNorm_sq_le_half_globalSq\` | DIRECT | Exact publication theorem. |

## 3. One-sided inverse concentration

| Paper item | Lean source | Status | Audit note |
|---|---|---|---|
| Incoming/outgoing block maximum formula | \`recordSubsetProjectorCommutatorCLM_opNorm_eq_max_cross\` | DIRECT | Exact. |
| Cross blocks are contractions | \`recordSubsetIncomingCLM_opNorm_le_one\`, \`recordSubsetOutgoingCLM_opNorm_le_one\` | DIRECT | Supports \(C_S\le1\). |
| Witness \(z_c=U^*P_cUv\) | \`incomingWitnessCellVector\` | DIRECT | Exact. |
| \(r_c=\|z_c\|^2,\ \alpha_c=p_c-r_c\) | \`incomingWitnessR\`, \`incomingWitnessAlpha\` | DIRECT | Exact. |
| \(\alpha_c\ge0\) | \`incomingWitnessAlpha_nonneg_of_mem\` | DIRECT | Exact under unit complementary witness hypotheses. |
| \(\sum\alpha_c=A_S-C_S^2=e_S\) in the maximizing block orientation | \`sum_incomingWitnessAlpha_eq_budget_sub_incoming\` + norm witness | DIRECT | Exact after substituting the maximizing-block equality. |
| Bad-cell mass \(\le2e_S\) | \`sum_bad_incomingWitnessP_le_two_mul_alpha_sum\` | DIRECT | Exact. |
| Normalized orthonormal family \(\xi_c\) | \`incomingWitnessXi_orthonormal\` | DIRECT | Exact. |
| Gram encoding \(p_cp_d=|\langle\zeta_c,\zeta_d\rangle|^2\) | \`incomingWitnessZeta_gram\` | DIRECT | Exact for distinct active good cells. |
| \(\sum\|\zeta_c-\xi_c\|^2\le2e_S\) | \`sum_incomingWitnessXi_sub_Zeta_norm_sq_le\` | DIRECT | Exact. |
| Generic spread bound \(6q+3q^2\) | \`gram_offDiagonal_spread_le\` | DIRECT | Exact. |
| Linearized spread \(\le18e_S\) | \`gram_offDiagonal_spread_le_18\` | DIRECT | Exact. |
| Dominant active-good tail \(\le18e_S/L\) | \`exists_dominant_of_gram_close_18\` | DIRECT | Exact. |
| One-sided cut tail \(A_S-p_i\le2e_S+18e_S/(C_S^2-e_S)\) | \`exists_cell_concentration_of_cut\` | DIRECT | Exact, with incoming/outgoing orientation handled formally. |

## 4. Bilateral and scale-sensitive stability

| Paper item | Lean source | Status | Audit note |
|---|---|---|---|
| \(e_S+e_T=E=\delta^2-2C^2\) | proof inside \`exists_two_cell_concentration_of_cut\` | DIRECT | Exact scalar identity. |
| \(A-p_i-p_j\le2E+18E/(C^2-E)\) | \`exists_two_cell_concentration_of_cut\` | DIRECT | Exact. |
| \(E\le\eta A\), \(\eta\le1/5\) implies applicability | \`exists_two_cell_concentration_of_cut_eta\` | DIRECT | Exact. |
| Absolute eta bound \(A-p_i-p_j\le2\eta A+36\eta/(1-3\eta)\) | \`exists_two_cell_concentration_of_cut_eta\` | DIRECT | Exact. |
| Scale-sensitive relative modulus | \`exists_two_cell_concentration_of_cut_eta_rho\` | DIRECT | Exact. |
| \(\Phi_\rho(\eta)=2\eta+36\eta/((1-3\eta)\rho^2)\) | \`twoCellStabilityModulus\` | DIRECT | Algebraically identical to the Lean parenthesization. |
| Main cut-envelope stability theorem | \`twoCellCommutatorConcentratedWithin_of_maxCut_near_saturated\` | DIRECT | Exact. Paper hypothesis \(C_{\max}^2\ge(1-\eta)\delta^2/2\) is algebraically equivalent to Lean's \(2(1-\eta)\delta^2\le(2C_{\max})^2\). |
| Linear corollary \(\tau\le\eta(2+72/\rho^2)\) for \(\eta\le1/6\) | \`twoCellCommutatorConcentratedWithin_linear_of_maxCut_near_saturated\` | DIRECT | Exact. |
| \(\Phi_\rho(\eta)\to0\) at fixed \(\rho>0\) | elementary from explicit formula | DERIVED | No issue; not required as a separate formal declaration. |

## 5. Exact rigidity

| Paper item | Lean source | Status | Audit note |
|---|---|---|---|
| Support on two cells from exact saturation | \`cellCommutatorSupportedOnTwo_of_maxCut_saturation\` | DIRECT | Lean obtains this as the \(\eta=0,\rho=\delta\) stability case, matching the paper. |
| Two-cell support implies exact saturation | \`maxCut_saturation_of_cellCommutatorSupportedOnTwo\` | DIRECT | Exact. |
| Positive-defect saturation iff exactly two cells are active | \`maxCut_saturation_iff_exactlyTwoActiveCellCommutators\` | DIRECT | Exact publication theorem. |
| Each of the two active budgets equals \(\delta^2/2\) under saturation | proof inside \`exactlyTwoActiveCellCommutators_of_maxCut_saturation\` | DIRECT | The paper derives the same fact using singleton cuts. |

## 6. Rank-one identity and explicit three-cell family

| Paper item | Lean source | Status | Audit note |
|---|---|---|---|
| Rank-one identity \(\|[P_e,U]\|_{\mathrm{op}}^2=1-|\langle e,Ue\rangle|^2\) | \`perspectiveProjectorCommutatorOpNormProfile_sq_rankOne\` | DIRECT | Exact. |
| Pell recurrence and \(p_n^2+1=2q_n^2\) | \`sharpnessPellPair\`, \`sharpnessP_sq_add_one_eq_two_mul_Q_sq\` | DIRECT | Exact. |
| \(A_n=(a_n+b_n)/\sqrt2,\ B_n=(a_n-b_n)/\sqrt2\) | \`stabilitySharpnessA\`, \`stabilitySharpnessB\` | DIRECT | Exact. |
| \(A_n^2+B_n^2=1\) | \`stabilitySharpnessA_sq_add_B_sq\` | DIRECT | Exact. |
| \(B_n=1/(\sqrt2 q_n)\) | \`stabilitySharpnessB_eq_inv\` | DIRECT | Exact. |
| \(B_n\to0,\ A_n^2\to1\) | \`stabilitySharpnessB_tendsto_zero\`, \`stabilitySharpnessA_sq_tendsto_one\` | DIRECT | Exact. |
| \(c_m^2+s_m^2=1,\ d_m=1-c_m,\ s_m^2=2d_m-d_m^2\) | \`iterationSharpnessC_sq_add_S_sq\`, \`stabilitySharpnessD\`, proof in asymptotics | DIRECT | Exact. |
| \(U_{n,m}=Q_nR_mQ_n^*\) | \`stabilitySharpnessRotationMatrix\` | DIRECT | Exact. |
| Three cell budgets \(p_0,p_1,p_2\) | \`stabilitySharpnessCell0_budget_sq\`, \`stabilitySharpnessCell1_budget_sq\`, \`stabilitySharpnessCell2_budget_sq\` | DIRECT | Exact. |
| Global budget \(\delta_{n,m}^2=2s_m^2+2d_m^2A_n^2B_n^2\) | \`stabilitySharpness_globalSq\` | DIRECT | Exact. |
| \(C_{\max}(n,m)=s_m\) | \`stabilitySharpness_maxCut_eq_s\` | DIRECT | Exact. |
| Exact \(\eta_{n,m}\) formula | \`stabilitySharpnessEta_exact\` | DIRECT | Exact. |

## 7. Optimality of the two-cell tail in the sharpness family

This is the manuscript point corrected in v0.5.

| Paper item | Lean source | Status | Audit note |
|---|---|---|---|
| \(p_1\le p_0\) | \`stabilitySharpnessCell1_budget_le_cell0\` | DIRECT | Exact. |
| \(p_1\le p_2\) | \`stabilitySharpnessCell1_budget_le_cell2\` | DIRECT | Exact. |
| Therefore omitting cell 1 is the optimal top-two tail | \`stabilitySharpnessTopTwoTail_eq_Tau\` | DIRECT | Exact. This bridges the paper's general optimal \(\tau\) with \`stabilitySharpnessTau\`. |
| Exact tail formula | \`stabilitySharpnessTau_exact\` | DIRECT | Explicitly identified with the optimal two-cell tail in v0.5. |
| Exact ratio \(\tau/\eta=(2-dB^2)/(2dA^2)\) | \`stabilitySharpnessTau_div_Eta_exact\` | DIRECT | Exact. |

## 8. Sharpness asymptotics

| Paper item | Lean source | Status | Audit note |
|---|---|---|---|
| Fixed \(m\): \(\tau/\eta\to1/d_m\) | \`stabilitySharpnessTau_div_Eta_tendsto_inv_D\` | DIRECT | Exact. |
| Fixed \(m\): \(\delta^2\to2s_m^2\) | \`stabilitySharpness_delta_sq_tendsto_two_s_sq\` | DIRECT | Exact. |
| Fixed-\(m\) product limit | \`stabilitySharpness_scaled_ratio_tendsto_scaleLimit\` | DIRECT | Exact. |
| Scale limit \(=4-2d_m\) | \`stabilitySharpnessScaleLimit_eq_four_sub_two_D\` | DIRECT | Exact. |
| \(m\to\infty\): scale limit \(\to4\) | \`stabilitySharpnessScaleLimit_tendsto_four\` | DIRECT | Exact. |
| Quantified obstruction: for every \(c<4\) and \(\varepsilon>0\), some family member has \(0<\eta<\varepsilon\), \(0<\delta^2<\varepsilon\), and \((\tau/\eta)\delta^2>c\) | `stabilitySharpness_scaled_ratio_tendsto_scaleLimit`, `stabilitySharpnessScaleLimit_tendsto_four`, `stabilitySharpness_delta_sq_tendsto_two_s_sq`, `stabilitySharpnessEta_exact` | DERIVED | Obtained by first taking \(m\) large, then \(n\) large. This is not packaged as one named Lean theorem. |
| No scale-independent \(\tau\le K\eta\), and no \(\tau\le\eta g(\delta)\) with \(g(\delta)=o(\delta^{-2})\) | quantified obstruction above | DERIVED | Logical consequence of the positive lower bound on \((\tau/\eta)\delta^2\) along arbitrarily small-defect members. |
| “inverse-square scale is necessary up to constants” | preceding limits and quantified obstruction | DERIVED | Precise interpretation of the formally checked asymptotics; it does not assert that the coefficient 4 is the best universal stability constant. |

## 9. Companion transfer bound

| Paper item | Lean source | Status | Audit note |
|---|---|---|---|
| \(\|r_D(Ux)-r_D(x)\|_1\le\sqrt2\,\delta\) for normalized \(x\) | \`recordProfileL1_unitary_le_sqrt_two_mul_operatorNormCommutatorL2\` | DIRECT | Exact. This statement is Born-sensitive, unlike the core stability theorem. |
| Optimality of \(\sqrt2\) | \`isUniversalUniformTransferCoefficient_iff_sqrt_two_le\` | DIRECT | Exact. |

## 10. Scope statements

- The stability / rigidity / sharpness core is **NON BORN-SENSITIVE** in the Lean dependency structure.
- No theorem in the audited core asserts time evolution, decoherence, environment-induced selection, or emergence of a preferred perspective.
- The full record-transfer inequality mentioned in the companion section is Born-sensitive and is explicitly separated from the operator-theoretic core.
- Bibliographic novelty is **not** a Lean property and remains subject to the independent literature audit.

## Audit conclusion

After the v0.5 corrections and the v0.6 priority/sharpness refinement, no mismatch has been found between the main
quantitative statements in the manuscript and the publication-facing Lean
surface.

The two qualifications that should remain visible in the paper are:

1. the Lean development checks canonical finite-dimensional coordinate
   Hilbert spaces; the fully abstract finite-dimensional formulation in the
   paper is obtained by the standard unitary-coordinate identification;
2. the “necessity up to constants” sentence is a mathematical interpretation
   of the formally checked asymptotic limit, rather than a separately named
   impossibility theorem in Lean.

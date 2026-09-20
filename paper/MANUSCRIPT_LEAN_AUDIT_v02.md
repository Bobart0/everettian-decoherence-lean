# Manuscript ↔ Lean audit v02 — gap recast

Reference manuscript: \`paper/stability_rigidity_sharpness_v10_gap_recast.tex\`.

Formal reference head from which the manuscript branch was forked:
\`81eb3ff53f6219749b84491513ff437fe7c545c1\`.

## Status convention

- **DIRECT** — the mathematical statement is represented by a named Lean declaration (up to notation).
- **DERIVED** — a short ordinary consequence or coordinate/unitary reformulation of DIRECT declarations.
- **PAPER-ONLY** — a new analytic presentation/generalization proved in the manuscript but not separately encoded by the current Lean artifact.
- **EXPOSITORY** — interpretation, notation, or literature positioning rather than a distinct formal claim.

## 1. Gap formulation

| v0.10 item | Lean source | Status | Audit note |
|---|---|---|---|
| \(Q_i=UP_iU^*\) and \(\|P_i-Q_i\|=\|[P_i,U]\|\) | commutator definitions / elementary unitary algebra | DERIVED | Multiply \([P_i,U]\) on the right by \(U^*\). The gap formulation is an equivalent coordinate-free presentation of the unitary problem. |
| \(p_i=\|P_i-Q_i\|^2\) | \`cellCommutatorOpNormSq\` after the preceding identity | DERIVED | Same numerical profile. |
| \(\delta^2=\sum_i p_i\) | \`sum_cellCommutatorOpNormSq_eq_globalSq\` | DERIVED | Exact after the gap/commutator identification. |
| \(G_S=\|P_S-Q_S\|=\|[P_S,U]\|\) | subset commutator definitions | DERIVED | Same identification for a coarsened projector. |
| \(G_{\max}\) | \`maxSubsetCommutatorOpNorm\` | DERIVED | Same maximum under gap notation. |
| optimal two-cell tail \(\tau\) | \`TwoCellCommutatorConcentratedWithin\` + paper definition | DERIVED | Lean uses the division-free existential formulation; for \(\delta>0\) it is equivalent to the paper's normalized minimum. |

## 2. Envelope

| v0.10 item | Lean source | Status | Audit note |
|---|---|---|---|
| Cut bounds for a unitary, \(G_S^2\le\sum_{i\in S}p_i\) and complement analogue | \`recordSubsetProjectorCommutatorCLM_opNorm_sq_le_subsetSq\`, \`recordSubsetProjectorCommutatorCLM_opNorm_sq_le_complSq\` | DIRECT/DERIVED | DIRECT in unitary commutator notation; DERIVED in gap notation. |
| \(G_{\max}^2\le\delta^2/2\) | \`maxSubsetCommutatorOpNorm_sq_le_half_globalSq\` | DIRECT/DERIVED | Exact unitary theorem, rephrased as a gap theorem. |
| Proposition 3.1 for an arbitrary linear operator \(T\) | none | PAPER-ONLY | v0.10 strengthens the elementary envelope layer beyond the Lean unitary specialization. Its proof is fully given in the manuscript. |

## 3. Gram and one-sided concentration layer

| v0.10 item | Lean source | Status | Audit note |
|---|---|---|---|
| generic Gram spread \(6q+3q^2\) | \`gram_offDiagonal_spread_le\` | DIRECT | v0.10 now gives the full paper proof. |
| linearization to \(18e\) when \(q\le2e\), \(e\le1/2\) | \`gram_offDiagonal_spread_le_18\` | DIRECT | Exact. |
| witness \(z_c=U^*P_cUv\) | \`incomingWitnessCellVector\` | DIRECT | Exact. |
| \(r_c=\|z_c\|^2\), \(\alpha_c=p_c-r_c\) | \`incomingWitnessR\`, \`incomingWitnessAlpha\` | DIRECT | Exact. |
| \(\sum\alpha_c=e\), \(\alpha_c\ge0\) | \`sum_incomingWitnessAlpha_eq_budget_sub_incoming\`, \`incomingWitnessAlpha_nonneg_of_mem\` | DIRECT | Exact after choosing a norm-attaining incoming witness. |
| bad-cell mass \(\le2e\) | \`sum_bad_incomingWitnessP_le_two_mul_alpha_sum\` | DIRECT | Exact. |
| \(\xi_c=z_c/\sqrt{r_c}\) orthonormal | \`incomingWitnessXi\`, \`incomingWitnessXi_orthonormal\` | DIRECT | Exact. |
| \(\zeta_c=P_cz_c/\sqrt{r_c}+\sqrt{p_c}\,v\) | \`incomingWitnessZeta\` | DIRECT | v0.10 now writes the formula explicitly. |
| \(p_cp_d=|\langle\zeta_c,\zeta_d\rangle|^2\) | \`incomingWitnessZeta_gram\` | DIRECT | Exact. |
| \(\sum\|\zeta_c-\xi_c\|^2\le2e\) | \`sum_incomingWitnessXi_sub_Zeta_norm_sq_le\` | DIRECT | Exact; v0.10 includes the residual calculation. |
| one-sided tail \(A_S-p_i\le2e+18e/(G^2-e)\) | \`exists_cell_concentration_of_cut\` | DIRECT | Exact in unitary notation. |

## 4. Bilateral and quantitative stability

| v0.10 item | Lean source | Status | Audit note |
|---|---|---|---|
| \(e_S+e_T=E=\delta^2-2G^2\) | proof inside \`exists_two_cell_concentration_of_cut\` | DIRECT | Exact. |
| \(A-p_i-p_j\le2E+18E/(G^2-E)\) | \`exists_two_cell_concentration_of_cut\` | DIRECT | Exact. |
| absolute eta bound \(A-p_i-p_j\le2\eta A+36\eta/(1-3\eta)\) | \`exists_two_cell_concentration_of_cut_eta\` | DIRECT | Exact. |
| v0.10 intrinsic normalized theorem \(\tau\le2\eta+36\eta/((1-3\eta)\delta^2)\) | preceding absolute theorem + \(\tau\) definition | DERIVED | This is the stronger/natural paper statement obtained by dividing the DIRECT absolute inequality by \(A=\delta^2>0\). |
| uniform positive-scale corollary with \(\delta\ge\rho\) | \`exists_two_cell_concentration_of_cut_eta_rho\`, \`twoCellCommutatorConcentratedWithin_of_maxCut_near_saturated\` | DIRECT/DERIVED | Same bound under gap notation. |
| linear corollary \(\tau\le\eta(2+72/\rho^2)\), \(\eta\le1/6\) | \`twoCellCommutatorConcentratedWithin_linear_of_maxCut_near_saturated\` | DIRECT/DERIVED | Exact after notation change. |

## 5. Exact rigidity

| v0.10 item | Lean source | Status | Audit note |
|---|---|---|---|
| saturation implies support on two cells | \`cellCommutatorSupportedOnTwo_of_maxCut_saturation\` | DIRECT/DERIVED | Rephrased as two nonzero cell gaps. |
| two-cell support implies saturation | \`maxCut_saturation_of_cellCommutatorSupportedOnTwo\` | DIRECT/DERIVED | Exact. |
| positive-defect saturation iff exactly two cells active | \`maxCut_saturation_iff_exactlyTwoActiveCellCommutators\` | DIRECT/DERIVED | Exact theorem after gap identification. |
| each active budget equals \(\delta^2/2\) | proof inside \`exactlyTwoActiveCellCommutators_of_maxCut_saturation\` | DIRECT/DERIVED | The paper also gives the short singleton-cut argument. |

## 6. Rank-one formula and scale obstruction

| v0.10 item | Lean source | Status | Audit note |
|---|---|---|---|
| rank-one identity \(\|P_e-UP_eU^*\|^2=1-|\langle e,Ue\rangle|^2\) | \`perspectiveProjectorCommutatorOpNormProfile_sq_rankOne\` + gap identity | DERIVED | Lean checks the commutator form directly. |
| discrete 3-cell exact budget formulas | \`stabilitySharpnessCell0_budget_sq\`, \`stabilitySharpnessCell1_budget_sq\`, \`stabilitySharpnessCell2_budget_sq\`, \`stabilitySharpness_globalSq\`, \`stabilitySharpness_maxCut_eq_s\` | DIRECT | These are the machine-checked sharpness mechanism. |
| optimality of the top-two tail in the discrete family | \`stabilitySharpnessTopTwoTail_eq_Tau\` | DIRECT | Exact. |
| discrete limiting constant \(4\) | \`stabilitySharpnessScaleLimit_tendsto_four\` and supporting declarations | DIRECT | Exact iterated-limit formal theorem. |
| v0.10 continuous one-parameter family \(t\downarrow0\) | none as a single Lean family | PAPER-ONLY | Same \(3\times3\) rotation mechanism with \(A^2=1-t\), \(B^2=t\), \(d=t\), \(s^2=2t-t^2\); all matrices and formulas are displayed and proved directly in the manuscript. |
| continuous limit \(\delta_t^2(\tau_t/\eta_t)\to4\) | none for this exact curve | PAPER-ONLY | Analytic one-variable calculation. It matches the limiting constant of the checked discrete specialization but is not claimed to be machine-checked. |
| impossibility of a scale-independent \(K\) or \(o(\delta^{-2})\) modulus | continuous limit (paper) / discrete formal limit (Lean) | DERIVED/PAPER-ONLY | Logical consequence of either obstruction family; not a separately named Lean impossibility theorem. |

## 7. Formalization-scope statement in v0.10

The manuscript now states only that:
- the **unitary** envelope/stability/rigidity chain is machine-checked;
- the rank-one identity is machine-checked;
- a **discrete specialization** of the three-cell scale obstruction is machine-checked.

It explicitly states that two v0.10 presentation improvements are not literal Lean declarations:
1. the arbitrary-operator extension of the elementary cut envelope;
2. the continuous one-parameter sharpness curve.

The prior Busch/Gleason/Naimark/Wigner/Riedel/Kent catalogue has been removed from the paper's abstract, keywords, and formal-verification section. Those upstream results remain part of the broader repository stack but are not used as indexing material for this LAA manuscript.

## 8. Mathematical scope

- The gap/stability/rigidity/sharpness core is **non-Born-sensitive**.
- No dynamical, decoherence, measurement-selection, or preferred-basis claim is made.
- The new gap language is an equivalent finite-dimensional geometric representation of the unitary core.
- Bibliographic novelty is not a Lean property and is tracked separately in the priority audit.

## Audit conclusion

For v0.10, the central theorem chain remains traceable to the same CI-verified Lean head. The two substantive editorial generalizations introduced by the adversarial rewrite are isolated and proved in the paper rather than being mislabeled as machine-checked.

No mismatch has been identified between the v0.10 unitary/gap results and the corresponding publication-facing Lean declarations.

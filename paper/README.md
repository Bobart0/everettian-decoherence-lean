# Stability / rigidity / sharpness paper

Primary target: **Linear Algebra and its Applications (LAA)**.

## Current reference manuscript

- \`stability_rigidity_sharpness_v10_gap_recast.tex\`: current reference manuscript after the adversarial LAA-style audit and gap-metric recast.
- \`references_v04.bib\`: current bibliography, expanded to principal-angle, projection-geometry, fixed-commutator, and pinching literature.
- \`MANUSCRIPT_LEAN_AUDIT_v02.md\`: v0.10 theorem-by-theorem traceability against Lean, explicitly separating DIRECT, DERIVED, and PAPER-ONLY statements.
- \`PRIORITY_AUDIT_v02_GAP_RECAST.md\`: renewed novelty search under the intrinsic gap/coarsening formulation.
- \`PRIORITY_AUDIT_v01.md\` and \`MANUSCRIPT_LEAN_AUDIT_v01.md\`: retained as historical audits.
- \`highlights_v02.txt\`: historical highlights; these must be rewritten before submission because the v0.10 framing and title have changed.

Earlier manuscript states v01--v09 are retained for provenance.

## Current title

**Rigidity and Scale-Sharp Stability for Gaps of Finite Orthogonal Decompositions**

## What changed in v0.10

The manuscript is now formulated intrinsically for two labelled orthogonal
resolutions \((P_i)\) and \((Q_i)\) with matching cell ranks.  The identity
\[
\|P_i-Q_i\|_{\mathrm{op}}=\|[P_i,U]\|_{\mathrm{op}},
\qquad Q_i=UP_iU^*,
\]
connects the new gap formulation to the existing unitary formalization.

The main editorial/mathematical changes are:

1. the elementary cut envelope is isolated and generalized in the paper to an arbitrary finite-dimensional linear operator \(T\);
2. the main stability theorem is stated intrinsically in the observed defect \(\delta\), with the \(\delta\ge\rho\) form demoted to a corollary;
3. the Gram-stability and one-sided concentration proof is written out in full, including the comparison vectors and the \(6q+3q^2\) estimate;
4. the Pell-based published sharpness presentation is replaced by a one-parameter \(3\times3\) real orthogonal family \(t\downarrow0\);
5. the title now says **scale-sharp**, avoiding any implication that the universal constants \(36\) or \(72\) are optimal;
6. related work is reorganized around principal angles, gap geometry, projection commutators, pinching, and almost-commuting operators;
7. Busch/Gleason/Kent and the broader quantum-foundations catalogue are removed from the abstract and keywords; Lean is presented as a verification artifact rather than as the mathematical subject.

## Main v0.10 theorem chain

For
\[
p_i=\|P_i-Q_i\|_{\mathrm{op}}^2,\qquad
\delta^2=\sum_i p_i,\qquad
G_{\max}=\max_{S\subseteq I}\|P_S-Q_S\|_{\mathrm{op}},
\]
the manuscript proves
\[
G_{\max}^2\le\frac{\delta^2}{2}.
\]

For \(\delta>0\), equality holds if and only if exactly two cell gaps are nonzero.

If
\[
G_{\max}^2\ge(1-\eta)\frac{\delta^2}{2},
\qquad
0\le\eta\le\frac15,
\]
then the optimal relative tail after retaining two cells satisfies
\[
\tau\le
2\eta+\frac{36\eta}{(1-3\eta)\delta^2}.
\]

The one-parameter three-cell family satisfies
\[
\delta_t^2\to0,\qquad
\eta_t\to0,\qquad
\delta_t^2\frac{\tau_t}{\eta_t}\to4,
\]
so the inverse-square defect-scale dependence is necessary up to constants.

## Lean scope

The CI-verified Lean head underlying the manuscript branch is
\`81eb3ff53f6219749b84491513ff437fe7c545c1\`.

The v0.10 paper accurately distinguishes:
- the machine-checked unitary envelope/stability/rigidity chain;
- the machine-checked rank-one identity and discrete three-cell scale obstruction;
- the paper-only arbitrary-\(T\) extension of the elementary envelope;
- the paper-only continuous one-parameter reparametrization of the sharpness mechanism.

See \`MANUSCRIPT_LEAN_AUDIT_v02.md\` for exact status by statement.

## Priority status

The renewed search under gap, principal-angle, projection-difference,
coarsening, pinching, and finite-family terminology found no direct predecessor
for the combined package:
- matched-coarsening envelope;
- exact two-cell equality rigidity;
- dimension- and cardinality-free near-equality concentration;
- inverse-square three-cell scale obstruction.

The elementary envelope remains exposed to a residual folklore risk under
older block-operator or pinching terminology, so v0.10 makes no priority claim
for that lemma alone.

## Submission-candidate checks

The v0.10 source has been compiled by the standard GitHub Actions paper
workflow and visually inspected in generic article format.  The principal
pages checked include:
- title/abstract/keywords;
- arbitrary-operator envelope;
- Gram lemma and one-sided concentration;
- intrinsic stability theorem;
- exact rigidity;
- one-parameter sharpness family;
- formal-verification scope;
- related work and bibliography.

The final promotion build should remain free of unresolved references and
typographic overflow before submission.

## Remaining pre-submission work

1. Freeze a final v0.10 build after the documentation commits and inspect its log.
2. Check current LAA/Elsevier author guidelines and required submission files.
3. Apply the final LAA/Elsevier class/template if required by the portal.
4. Create a tagged archival formalization release and persistent DOI, then replace/supplement the raw commit reference.
5. Rewrite highlights for the gap formulation.
6. Prepare cover letter, declarations, code/data availability wording, and portal metadata.

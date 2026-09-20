# Submission metadata — Linear Algebra and its Applications

## Manuscript

**Title**  
Sharp Quantitative Stability of Finite Projective Records under Approximately Commuting Unitary Transformations

**Article type**  
Regular research article

**Author**  
Bertrand Dalimier

**Affiliation**  
Independent Researcher

**Corresponding author**  
Bertrand Dalimier

**E-mail**  
TBD in submission portal

**ORCID**  
TBD / add if applicable

## Abstract

Let \((P_i)_{i\in I}\) be a finite orthogonal projective decomposition of a finite-dimensional complex Hilbert space and let \(U\) be unitary. Write \(a_i=\|[P_i,U]\|_{\mathrm{op}}\) for the cellwise commutator defects, \(\delta^2=\sum_i a_i^2\) for their global quadratic budget, and
\[
C_{\max}=\max_{S\subseteq I}\|[P_S,U]\|_{\mathrm{op}},
\qquad P_S=\sum_{i\in S}P_i,
\]
for the finite cut envelope. We prove the sharp universal estimate \(C_{\max}^2\le\delta^2/2\). When \(\delta>0\), equality holds if and only if exactly two cells have nonzero commutator defect. We then establish an inverse stability theorem: if
\[
C_{\max}^2\ge(1-\eta)\frac{\delta^2}{2},
\qquad 0\le\eta\le\frac15,\qquad \delta\ge\rho>0,
\]
then two cells capture all but a relative fraction
\[
2\eta+\frac{36\eta}{(1-3\eta)\rho^2}
\]
of the global quadratic budget. For \(\eta\le1/6\) this is bounded by \(\eta(2+72/\rho^2)\). Finally, an explicit three-cell family shows that the inverse-square scale dependence is necessary up to constants: in an iterated near-saturation regime, \((\tau/\eta)\delta^2\to4\). All principal statements and the sharpness construction have been formally verified in Lean 4.

## Keywords

- projector commutators
- quantitative stability
- rigidity
- near equality
- unitary operators
- formal verification

## 2020 Mathematics Subject Classification

- **15A60** — Norms and inequalities (primary)
- **15A45** — Miscellaneous inequalities involving matrices
- **47A63** — Operator inequalities

## Highlights

- A sharp cut bound controls aggregate projector commutators.
- Equality occurs exactly when two cells carry all commutator defect.
- Near equality forces dimension-free concentration onto two cells.
- The stability modulus necessarily depends on the inverse defect scale.
- An explicit three-cell family proves the scale dependence is sharp.

## Scope statement

The paper is a finite-dimensional matrix/operator study of a complete family
of orthogonal projections and one unitary operator. Its core results are a
sharp operator-norm inequality, an equality classification, a dimension-free
near-equality theorem, and an explicit finite-dimensional sharpness family.

An equivalent matched-rank PVM formulation is
\[
D_{\mathrm{op}}(P,Q)^2
\le \frac12\sum_i\|P_i-Q_i\|_{\mathrm{op}}^2,
\]
with exact equality rigidity and quantitative near-equality stability.

## Reproducibility / code

The principal results have a companion Lean 4 formalization. The paper branch
was forked from formalization head
\`81eb3ff53f6219749b84491513ff437fe7c545c1\`, for which GitHub Actions run
#218 passed the full library build and dedicated audit surface.

Before submission, replace the raw commit reference by a tagged archival
release and persistent identifier if available.

## Declarations already included in manuscript

- Generative-AI / AI-assisted-technologies declaration.
- AI-assisted formalization workflow description.

## Items to confirm in the submission portal

- Corresponding-author e-mail.
- ORCID, if applicable.
- Funding statement.
- Competing-interests declaration.
- Confirmation of submission exclusivity / prior publication status.
- Final code-availability URL or archival DOI.

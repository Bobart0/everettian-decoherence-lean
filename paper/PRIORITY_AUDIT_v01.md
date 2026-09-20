# Priority / related-work audit — v0.1

Date: 2026-09-20

Manuscript branch: \`paper-post-t5-stability\`

This note records the targeted literature search used to calibrate the
submission claims. It is an editorial audit, not a proof of historical
novelty.

## Result to be compared

For finite mutually orthogonal projections \((P_i)_{i\in I}\) summing to the
identity and a unitary \(U\), set
\[
p_i=\|[P_i,U]\|_{\rm op}^2,\qquad
\delta^2=\sum_i p_i,
\]
and
\[
C_{\max}=\max_{S\subseteq I}
\left\|\left[\sum_{i\in S}P_i,U\right]\right\|_{\rm op}.
\]

The paper proves:
1. \(C_{\max}^2\le\delta^2/2\), with sharp constant.
2. For \(\delta>0\), equality iff exactly two cells are active.
3. A dimension-free quantitative near-equality theorem with explicit
   \(\eta,\rho\) modulus.
4. A three-cell family proving inverse-square defect-scale dependence is
   necessary up to constants, with iterated scaled limit \(4\).

Equivalently, for \(Q_i=UP_iU^*\),
\[
C_{\max}=D_{\rm op}(P,Q),\qquad
\|[P_i,U]\|_{\rm op}=\|P_i-Q_i\|_{\rm op},
\]
so for matched-rank finite PVMs:
\[
D_{\rm op}(P,Q)^2
\le \frac12\sum_i\|P_i-Q_i\|_{\rm op}^2.
\]

## Search fronts and findings

### Projection geometry and invariant subspaces

Classical background includes Halmos (1969), *Two Subspaces*, and
Davis--Kahan (1970), *The Rotation of Eigenvectors by a Perturbation. III*.
These give canonical geometry and perturbation theory for subspaces and
projection pairs. The targeted search did not identify the finite cut
functional above together with its equality and near-equality structure.

### Commutator inequalities and projection pairs

Relevant works include Bhatia--Davis--Kittaneh (1991), Kittaneh (2007),
Li (2004), and Conde (2022). Conde explicitly studies norm inequalities and
extremal behavior for commutators and anticommutators associated with two
orthogonal projections. This is a direct neighbor and remains cited.

The manuscript instead studies a complete finite orthogonal decomposition,
all aggregate cuts, and a global \(\ell^2\) budget. No matching theorem was
identified in this search front for
\[
\max_S\left\|\left[\sum_{i\in S}P_i,U\right]\right\|_{\rm op}^2
\le \frac12\sum_i\|[P_i,U]\|_{\rm op}^2
\]
together with the two-active-cell equality classification and quantitative
near-equality theorem.

### Almost commuting operators / nearby commuting approximants

Relevant works include Voiculescu (1983), Exel--Loring (1989, 1991),
Lin (1997), Friis--Rørdam (1996), Hastings (2009),
Marcoux--Popov--Radjavi (2013), Dor-On--Hall--Kachkovskiy (2025), and
Herrera (2024, 2026).

These solve a different inverse problem: operators are perturbed to a
commuting configuration. In this manuscript the projections and unitary
remain fixed; near equality constrains the internal distribution of their
existing commutator defects.

### Operational distance between quantum measurements

For finite POVMs \(M=(M_i)\), \(N=(N_i)\), the operational distance used in
measurement theory is
\[
D_{\rm op}(M,N)
=\max_{S}\left\|\sum_{i\in S}(M_i-N_i)\right\|_\infty.
\]

Relevant works include Navascués--Popescu (2014),
Puchała--Pawela--Krawiec--Kukulski (2018), and
Maciejewski--Zimborás--Oszmaniec (2020). The 2020 paper explicitly records
the subset-max operator-norm formula and its discrimination interpretation.

For \(Q_i=UP_iU^*\), the manuscript's cut envelope is exactly
\(D_{\rm op}(P,Q)\). A generic triangle argument gives
\[
D_{\rm op}(M,N)
\le \frac12\sum_i\|M_i-N_i\|_{\rm op}
\]
because \(\sum_i(M_i-N_i)=0\). The matched-rank PVM result in the manuscript
is instead a sharp \(\ell^2\)-type estimate with a dimension-free constant,
followed by equality and stability theory.

The targeted search did not identify
\[
D_{\rm op}(P,Q)^2
\le\frac12\sum_i\|P_i-Q_i\|_{\rm op}^2
\]
for matched-rank PVMs together with the exact equality classification and
quantitative near-equality theorem.

## Search terms used

Representative queries included:
- operational distance projective measurements / PVM max subset operator norm;
- commutator orthogonal projections operator norm equality stability;
- sum commutators projections unitary operator norm l2 inequality;
- near equality projections commutator operator norm stability;
- operational distance POVM max subset operator norm;
- measurement discrimination operational distance POVM operator norm;
- exact \(\ell^2\) / square-sum variants of the finite cut inequality.

## Second-pass citation-chain result

A second citation-chain pass was run on 2026-09-20, targeting
projective-measurement operational distance, operator-norm square-sum bounds,
projection-commutator equality cases, and near-equality stability. It
recovered additional uses of operational distance and recent two-projection
norm literature, but did **not** identify the matched-rank PVM \(\ell^2\)
inequality above or its equality / near-equality classification.

This is a targeted negative search result, not a proof of absolute historical
novelty.

## Claim calibration

Safe wording:
- “We prove ...” followed by the precise theorem.
- “A targeted literature search did not identify a prior result combining
  this finite-family envelope, its equality classification, the
  dimension-free near-equality theorem, and the scale-sharp three-cell
  family.”
- “The result is distinct from commuting-approximant stability.”

Avoid without a stronger bibliographic audit:
- “first ever,” or “previously unknown” as an absolute historical statement;
- implying novelty of operational distance itself;
- implying novelty of projection-pair commutator geometry.

## Current assessment

No overlap found in the targeted search invalidates the manuscript's central
claim set. The operational-distance connection strengthens the paper's
positioning and makes measurement-distance literature part of the mandatory
related work.

If submission is delayed substantially, repeat the recent-literature and
citation-chain search immediately before submission.

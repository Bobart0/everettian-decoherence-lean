# Priority / related-work audit — v0.1

Date: 2026-09-20

Manuscript branch: `paper-post-t5-stability`

This note records the targeted literature search used to calibrate the
submission claims. It is an editorial audit, not a proof of historical
novelty.

## Result to be compared

For finite mutually orthogonal projections ((P_i)_{iin I}) summing to the
identity and a unitary (U), set
[
  p_i=|[P_i,U]|_{m op}^2,qquad
  delta^2=sum_i p_i,
]
and
[
  C_{max}=max_{Ssubseteq I}
    left|left[sum_{iin S}P_i,Uight]ight|_{m op}.
]

The paper proves:
1. (C_{max}^2ledelta^2/2), with sharp constant.
2. For (delta>0), equality iff exactly two cells are active.
3. A dimension-free quantitative near-equality theorem with explicit
   (eta,ho) modulus.
4. A three-cell family proving inverse-square defect-scale dependence is
   necessary up to constants, with iterated scaled limit (4).

Equivalently, for (Q_i=UP_iU^*),
[
  C_{max}=D_{m op}(P,Q),qquad
  |[P_i,U]|_{m op}=|P_i-Q_i|_{m op},
]
so for matched-rank finite PVMs:
[
  D_{m op}(P,Q)^2
  le rac12sum_i|P_i-Q_i|_{m op}^2.
]

## Search fronts and findings

### 1. Geometry of projections and invariant subspaces

Relevant classical background:
- Halmos, *Two Subspaces* (1969).
- Davis--Kahan, *The Rotation of Eigenvectors by a Perturbation. III* (1970).

These give canonical geometry / perturbation theory for subspaces and
projection pairs, but the targeted search did not identify the finite cut
functional above together with its equality and near-equality structure.

### 2. Norm inequalities for commutators and projection pairs

Relevant works include:
- Bhatia--Davis--Kittaneh (1991), commutator inequalities and spectral
  variation.
- Kittaneh (2007), commutator inequalities for positive operators.
- Li (2004), *Commutators of Orthogonal Projections*.
- Conde (2022), *A Note about the Norm of the Sum and the Anticommutator of
  Two Orthogonal Projections*, JMAA 505(2), 125650.

Conde explicitly studies norm inequalities and extremal behavior for a pair
of orthogonal projections, including commutator bounds. This is a direct
neighbor and should remain cited. The object there is a projection pair,
whereas the manuscript studies a complete finite orthogonal decomposition,
all aggregate cuts, and a global (ell^2) cellwise budget.

No matching theorem was identified in this search front for
[
  max_S|[sum_{iin S}P_i,U]|^2
  le rac12sum_i|[P_i,U]|^2
]
together with the two-active-cell equality classification and quantitative
near-equality theorem.

### 3. Almost commuting operators / nearby commuting approximants

Relevant works:
- Voiculescu (1983), obstruction for almost commuting unitary matrices.
- Exel--Loring (1989, 1991), topological invariants / obstructions.
- Lin (1997), positive approximation theorem for self-adjoint matrices.
- Friis--Rørdam (1996), short proof of Lin's theorem.
- Hastings (2009), quantitative almost-commuting matrices.
- Dor-On--Hall--Kachkovskiy (2025), almost commuting unitaries.
- Herrera (2024, 2026), projection characterizations and symmetry bootstrap
  for nearby commuting operators.
- Marcoux--Popov--Radjavi (2013), almost-invariant subspaces and approximate
  commutation.

These are conceptually adjacent but solve a different inverse problem:
operators are perturbed to a commuting configuration. In the present
manuscript the projections and unitary remain fixed; near equality constrains
the internal distribution of their existing commutator defects.

### 4. Operational distance between quantum measurements

For finite POVMs (M=(M_i)), (N=(N_i)), the operational distance used in
measurement theory can be written
[
  D_{m op}(M,N)
  =max_{S}left|sum_{iin S}(M_i-N_i)ight|_infty.
]

Relevant works:
- Navascués--Popescu (2014), *How Energy Conservation Limits Our
  Measurements*.
- Puchała--Pawela--Krawiec--Kukulski (2018), single-shot discrimination of
  quantum measurements.
- Maciejewski--Zimborás--Oszmaniec (2020), detector tomography / readout
  mitigation, which explicitly records the subset-max operator-norm formula.

For (Q_i=UP_iU^*), the manuscript's cut envelope is exactly
(D_{m op}(P,Q)). This supplies a standard external interpretation of the
left-hand side and a useful equivalent PVM formulation.

A generic triangle argument gives
[
  D_{m op}(M,N)
  le rac12sum_i|M_i-N_i|_{m op}
]
because (sum_i(M_i-N_i)=0). The manuscript's matched-rank PVM result is
qualitatively different: it is a sharp (ell^2)-type estimate with a
dimension-free constant, followed by equality and stability theory.

The targeted search did not identify the specific PVM inequality
[
  D_{m op}(P,Q)^2
  lerac12sum_i|P_i-Q_i|_{m op}^2
]
together with the exact equality classification and the quantitative
near-equality result.

## Search terms used

Representative targeted queries included:
- operational distance projective measurements / PVM max subset operator norm;
- commutator orthogonal projections operator norm equality stability;
- sum commutators projections unitary operator norm l2 inequality;
- near equality projections commutator operator norm stability;
- operational distance POVM max subset operator norm;
- measurement discrimination operational distance POVM operator norm;
- exact (ell^2) / square-sum variants of the finite cut inequality.

## Claim calibration for the manuscript

Safe wording:
- “We prove ...” followed by the precise theorem.
- “A targeted literature search did not identify a prior result combining
  this finite-family envelope, its equality classification, the
  dimension-free near-equality theorem, and the scale-sharp three-cell
  family.”
- “The result is distinct from commuting-approximant stability.”

Avoid without a stronger bibliographic audit:
- “first ever,” “new inequality” without qualification, or “previously
  unknown” as an absolute historical statement.
- implying novelty of operational distance itself.
- implying novelty of projection-pair commutator geometry.

## Current assessment

No overlap found in the targeted search invalidates the manuscript's central
claim set. The operational-distance connection strengthens the paper's
positioning and provides a standard interpretation, but it also makes
measurement-distance literature part of the mandatory related-work audit.

Before submission, one final citation-chain pass should inspect papers citing
the operational-distance formula and recent projection-pair norm-inequality
papers for an unnoticed (ell^2) refinement or near-equality result.

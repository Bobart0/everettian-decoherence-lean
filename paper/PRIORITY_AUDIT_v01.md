# Priority audit v1 — finite cut commutator stability

**Audit date:** 2026-09-20  
**Reference manuscript:** \`paper/stability_rigidity_sharpness_v05_audited.tex\`

## Claims audited

The search targeted four claims, not the broad topic of commutator inequalities:

1. \(C_{\max}^2\le \frac12\sum_i\|[P_i,U]\|_{\rm op}^2\) for a finite orthogonal resolution;
2. equality at positive defect iff exactly two cells are active;
3. near equality implies cardinality-free quantitative two-cell concentration;
4. a three-cell family gives
   \(\lim_m\lim_n(\tau_{n,m}/\eta_{n,m})\delta_{n,m}^2=4\).

Searches covered journal pages, arXiv, DOI-indexed pages, and citation trails using
“orthogonal projections”, “finite orthogonal decomposition”, “resolution of the identity”,
“unitary commutator”, “operator norm”, “sum of squared commutator norms”,
“maximum over subsets”, “aggregate projection”, “equality case”, “near equality”,
“near saturation”, “almost invariant subspace”, “almost commuting”, “block operator”,
“pinching”, and “projection symmetry”.

## Closest literature found

### Two-projection geometry

Halmos' two-subspaces theorem and the Böttcher--Spitkovsky survey provide the
canonical two-projection block geometry:

- P. R. Halmos, *Two Subspaces*, Trans. AMS 144 (1969), 381--389.
- A. Böttcher and I. M. Spitkovsky, *A gentle guide to the basics of two
  projections theory*, Linear Algebra Appl. 432 (2010), 1412--1459,
  DOI 10.1016/j.laa.2009.11.002.

They do not study a finite family \((P_i)\), a unitary \(U\), a cellwise
projection--unitary commutator profile, or a maximum over aggregate cuts.

**Status:** background, no direct overlap.

### Commutators of two projections

Relevant structural work includes:

- Q. Li, *Commutators of Orthogonal Projections*, Nihonkai Math. J. 15 (2004), 93--99.
- W. Shi and G. Ji, *Anti-selfadjoint operators as commutators of projections*,
  JMAA 478 (2019), 539--559, DOI 10.1016/j.jmaa.2019.05.042.
- L. W. Marcoux, H. Radjavi and Y. Zhang, *Around the closures of the set of
  commutators and the set of differences of idempotent elements of B(H)*,
  J. Operator Theory 91 (2024), 97--124, DOI 10.7900/jot.2022feb07.2396.

This line contains the classical bound \(\|[P,Q]\|\le1/2\) for **two
projections** and characterizes operators representable as such commutators.

The manuscript's factor \(1/2\) is a different statement: the second operator
is unitary and the right-hand side is the adaptive finite-family budget
\(\sum_i\|[P_i,U]\|_{\rm op}^2\). The paper should explicitly distinguish the
two uses of \(1/2\).

**Status:** important neighboring result, no direct finite-family overlap found.

### Two-projection norm formulas

Relevant references include Walters' anticommutator formula, Conde's 2022
paper, and the 2024 refinements of Li--Liu--Deng. These concern sums,
differences, products, commutators and anticommutators of **two** projections.

- S. Walters, *Anticommutator Norm Formula for Projection Operators*,
  arXiv:1604.00699.
- C. Conde, JMAA 505 (2022), 125650, DOI 10.1016/j.jmaa.2021.125650.
- X. Li, M. Liu and C. Deng, Acta Math. Sci. 44 (2024), 1229--1243,
  DOI 10.1007/s10473-024-0403-9.

**Status:** useful context; no equality/near-equality theorem for the present
finite-family functional was found.

### Projection stability under symmetries

The conceptually closest stability literature found is:

- S. Walters, *Projection operators nearly orthogonal to their symmetries*,
  JMAA 446 (2017), 1356--1361, DOI 10.1016/j.jmaa.2016.09.013.
- I. M. Spitkovsky, *A distance formula related to a family of projections
  orthogonal to their symmetries*, OTAA 267 (2018), 371--376,
  DOI 10.1007/978-3-319-72449-2_17.

These perturb a projection toward another projection satisfying an exact
orthogonality relation. The present theorem does **not** perturb \(P_i\) or
\(U\): it infers concentration of the existing defect profile from near
equality in a sharp family-level inequality.

**Status:** closest conceptual neighbor, different input/output invariant.

### Almost commuting operators

Lin, Hastings, Dor-On--Hall--Kachkovskiy, and Herrera study closeness to
exactly commuting operators, including current 2025--2026 effective and
projection-characterization results.

- M. B. Hastings, CMP 291 (2009), 321--345.
- A. Dor-On, L. Hall, I. Kachkovskiy, arXiv:2510.03674 (2025).
- D. Herrera, arXiv:2412.20795 (2024).
- D. Herrera, arXiv:2609.15057 (submitted 2026-09-14).

The target is a nearby commuting pair, unlike the manuscript's inverse
near-equality statement for a fixed decomposition and fixed unitary.

**Status:** active neighboring field, no direct overlap.

### Generic commutator equality cases

Böttcher--Wenzel-type work is precedent for classifying equality cases of
sharp commutator inequalities, but uses Frobenius/unitarily invariant norms
of commutators of arbitrary matrices, not a finite orthogonal resolution and
subset maximum.

- A. Böttcher and D. Wenzel, LAA 429 (2008), 1864--1885,
  DOI 10.1016/j.laa.2008.05.020.
- C.-M. Cheng, K.-S. Fong, W.-F. Lei, LAA (2013), equality cases for related
  Frobenius-norm commutator inequalities.

**Status:** methodological precedent, not duplication.

### Multi-projection false positive

V. Mazorchuk and S. Rabanovich, *Multicommutators and multianticommutators of
orthogonal projections*, Linear Multilinear Algebra 56 (2008), 639--646,
DOI 10.1080/03081080701339911, studies nested expressions
\([[\cdots[P_1,P_2],P_3],\ldots]\). It does not study
\([\sum_{i\in S}P_i,U]\).

**Status:** terminological false positive.

## Claim-by-claim conclusion

### Cut envelope

No direct predecessor was located. However, the proof is elementary once the
cross-block budget inequalities are isolated, so an equivalent statement could
exist as folklore or as an unnamed block-matrix lemma.

**Submission wording:** claim the finite-family cut-envelope result as part of
the theorem package; do not claim that the scalar constant \(1/2\) itself is
historically new.

### Exact two-cell rigidity

No prior support classification for equality in this finite-family envelope
was located.

**Submission wording:** “we characterize the equality cases of the
cut-envelope inequality” is appropriate.

### Quantitative near-equality theorem

No direct predecessor was located. The searched stability literature changes
the operators to recover an exact relation; it does not derive concentration
of a fixed commutator-defect profile from near saturation.

**This is the strongest apparent novelty point.**

### Three-cell scale obstruction

No analogue of the explicit three-cell construction or the iterated constant-4
limit was located.

The paper should state the exact asymptotic theorem and infer from it that a
scale-independent \(O(\eta)\) tail bound is impossible and that an
inverse-square scale is necessary up to constants. It should **not** call 4
the best universal stability constant.

## Overall assessment

As of 2026-09-20, no direct literature overlap was identified for the combined
package:

- finite orthogonal resolution;
- subset cut envelope against the global squared projection--unitary
  commutator budget;
- exact two-active-cell equality rigidity;
- cardinality-free quantitative near-equality concentration;
- explicit three-cell inverse-square scale obstruction.

This is not a proof of absolute historical priority. The residual search risk
is mainly in older or poorly indexed block-operator, pinching, row/column
operator, and conditional-expectation literature.

Recommended manuscript language:

> We prove a finite-family cut-envelope inequality and characterize its
> equality and near-equality regimes. We have not located these finite-family
> equality and stability statements in the projection-commutator or
> almost-commuting-operator literature; the closest results concern
> two-projection norm identities or perturbation to nearby exact relations,
> rather than concentration of a fixed commutator-defect profile.

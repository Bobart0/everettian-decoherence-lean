# Stability / rigidity / sharpness paper

Primary target: **Linear Algebra and its Applications (LAA)**.

## Current reference manuscript

- `stability_rigidity_sharpness_v06_priority_audited.tex`: current reference manuscript after Lean audit and focused priority audit.
- `references_v03.bib`: current bibliography after priority audit.
- `MANUSCRIPT_LEAN_AUDIT_v01.md`: traceability ledger for paper claims versus Lean.
- `PRIORITY_AUDIT_v01.md`: focused literature/priority audit.
- `highlights_v02.txt`: current five submission highlights.

Earlier manuscript states v01--v05 are retained for provenance.

## Formal reference state

The paper branch was forked from Lean head
`81eb3ff53f6219749b84491513ff437fe7c545c1`, for which the complete CI passed, including the library build, audit aggregate, guards, and diff-hygiene checks.

## Manuscript ↔ Lean audit

No mismatch has been identified in the principal quantitative results.

Important qualifications retained in the paper:

1. Lean checks canonical finite-dimensional coordinate Hilbert spaces; the coordinate-free paper formulation is obtained by unitary identification.
2. The general optimal top-two tail used in the paper is explicitly connected to the three-cell sharpness quantity by `stabilitySharpnessTopTwoTail_eq_Tau`.
3. The quantified inverse-square obstruction in v0.6 is a mathematical consequence of several machine-checked limits and exact formulas; it is marked DERIVED rather than presented as a separate Lean declaration.

Static checks on v0.6:
- 54 labels and 45 internal references;
- no unresolved or duplicated labels;
- 19 cited keys, all resolved in `references_v03.bib`;
- no duplicated BibTeX keys;
- balanced LaTeX environments and braces.

## Priority audit

The focused search found substantial neighboring literature on two projections,
projection commutators, almost commuting operators, and perturbative projection
stability, but no direct predecessor for the combined finite-family package:
cut envelope + exact two-cell rigidity + quantitative near-equality
concentration + three-cell inverse-square scale obstruction.

The novelty language is intentionally non-absolute because an equivalent base
envelope lemma could exist under older block-operator or pinching terminology.

## Remaining pre-submission work

1. Recast the title/abstract/introduction in standard matrix/operator language, reducing projective-record terminology for LAA.
2. Perform a final editorial proof pass and, if possible, compile the submission PDF.
3. Replace the raw GitHub commit by a tagged archival release and persistent DOI.
4. Apply the final Elsevier/LAA template or class if required by the portal.
5. Prepare cover letter, highlights, declarations, and submission metadata.

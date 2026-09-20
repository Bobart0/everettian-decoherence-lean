# Stability / rigidity / sharpness paper

Primary target: **Linear Algebra and its Applications (LAA)**.

## Current reference manuscript

- `stability_rigidity_sharpness_v07_laa_indexed.tex`: current reference manuscript, with LAA-facing title/abstract and explicit searchable formalization lineage.
- `references_v03.bib`: current bibliography after priority audit.
- `MANUSCRIPT_LEAN_AUDIT_v01.md`: traceability ledger for paper claims versus Lean, including the upstream formalization lineage.
- `PRIORITY_AUDIT_v01.md`: focused literature/priority audit.
- `highlights_v02.txt`: current five submission highlights.

Earlier manuscript states v01--v06 are retained for provenance.

## Formalization stack exposed in v0.7

The abstract and introduction now expose the pinned four-repository stack:

`gleason-theorem-lean`
→ `quantum-foundations-lean`
→ `everettian-probability-lean`
→ `everettian-decoherence-lean`.

For search visibility and provenance, the abstract explicitly names major
machine-checked results available in the upstream library: Busch's theorem,
Gleason's theorem, Naimark dilation, Wigner's theorem, Uhlhorn-type uniqueness,
Riedel's branch-decomposition theorem, and Kent's contrary-inference
construction.

The manuscript states explicitly that these named results describe the broader
library coverage; they are not all premises of the present cut-envelope theorem.
Kent is a conceptual contrast upstream, not a logical dependency of the
stability result.

## Current title and indexing

Current title:

**Sharp Stability and Two-Cell Rigidity for Finite Projector--Unitary Commutator Profiles**

Current keywords include:
projector--unitary commutators; orthogonal resolutions of the identity;
near-equality stability; rigidity; Lean 4 formal verification;
Gleason theorem; Busch theorem; Kent contrary inference.

## Formal reference state

The paper branch was forked from Lean head
`81eb3ff53f6219749b84491513ff437fe7c545c1`, for which the complete CI passed,
including the library build, audit aggregate, guards, and diff-hygiene checks.

## Manuscript ↔ Lean audit

No mismatch has been identified in the principal quantitative results.

Important qualifications retained in the paper:

1. Lean checks canonical finite-dimensional coordinate Hilbert spaces; the coordinate-free paper formulation is obtained by unitary identification.
2. The general optimal top-two tail used in the paper is explicitly connected to the three-cell sharpness quantity by `stabilitySharpnessTopTwoTail_eq_Tau`.
3. The quantified inverse-square obstruction is a mathematical consequence of several machine-checked limits and exact formulas; it is marked DERIVED rather than presented as a separate Lean declaration.
4. The upstream theorem names in the abstract are claims about the audited formal library, not about the logical premises of the current theorem.

Static checks on v0.7:
- no unresolved or duplicated labels;
- no unresolved citation keys;
- no duplicated BibTeX keys;
- balanced LaTeX environments and braces.

## Priority audit

The focused search found substantial neighboring literature on two projections,
projection commutators, almost commuting operators, and perturbative projection
stability, but no direct predecessor for the combined finite-family package:
cut envelope + exact two-cell rigidity + quantitative near-equality
concentration + three-cell inverse-square scale obstruction.

The novelty language remains intentionally non-absolute because an equivalent
base envelope lemma could exist under older block-operator or pinching
terminology.

## Remaining pre-submission work

1. Final editorial pass on the first two pages and section ordering.
2. Compile and inspect the submission PDF.
3. Replace the raw GitHub commit by a tagged archival release and persistent DOI.
4. Apply the final Elsevier/LAA template or class if required by the submission portal.
5. Prepare cover letter, highlights, declarations, and submission metadata.

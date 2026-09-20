# Stability / rigidity / sharpness paper

Primary target: **Linear Algebra and its Applications (LAA)**.

## Current reference manuscript

- `stability_rigidity_sharpness_v09_visually_audited.tex`: current submission candidate after Lean audit, focused priority audit, LAA-facing rewrite, compilation, and visual PDF audit.
- `references_v03.bib`: current bibliography after priority and metadata audit.
- `MANUSCRIPT_LEAN_AUDIT_v01.md`: traceability ledger for paper claims versus Lean, including the upstream formalization lineage.
- `PRIORITY_AUDIT_v01.md`: focused literature/priority audit.
- `highlights_v02.txt`: current submission highlights; to be synchronized with the v0.9 title before portal submission.

Earlier manuscript states v01--v08 are retained for provenance.

## Current title

**Sharp Stability and Two-Cell Rigidity for Finite Projector--Unitary Commutator Profiles**

## Formalization visibility

The abstract retains explicit search-visible provenance for the broader audited
formalization library. It states that the principal theorems and sharpness
construction are machine-checked in Lean 4 and that the upstream library also
formalizes the Busch and Gleason representation theorems, Naimark dilation,
Wigner's theorem, Uhlhorn-type uniqueness, Riedel's branch decomposition, and
Kent's contrary-inference construction.

The manuscript explicitly distinguishes library coverage from logical
dependency: Kent is an upstream conceptual contrast, not a premise of the
present cut-envelope theorem.

Current search-oriented keywords include:
projector--unitary commutators; near-equality stability; rigidity;
Lean 4 formal verification; Gleason theorem; Busch theorem;
Kent contrary inference.

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

## Priority audit

The focused search found substantial neighboring literature on two projections,
projection commutators, almost commuting operators, and perturbative projection
stability, but no direct predecessor for the combined finite-family package:
cut envelope + exact two-cell rigidity + quantitative near-equality
concentration + three-cell inverse-square scale obstruction.

The novelty language remains intentionally non-absolute because an equivalent
base envelope lemma could exist under older block-operator or pinching
terminology.

## v0.9 submission-candidate audit

The v0.9 source is compiled reproducibly by GitHub Actions.

Final generic-article PDF audit:
- 14 pages;
- all labels and bibliography references resolve;
- no LaTeX `Overfull`, `Underfull`, `Undefined`, `Warning`, `Error`, or `Fatal` entries in the final log;
- no hyperlink boxes in the rendered manuscript;
- first-page title/abstract/keywords visually inspected;
- formal-verification page visually inspected after line-overflow corrections;
- bibliography visually inspected after capitalization/arXiv metadata corrections.

The LAA-facing v0.9 deliberately removes the standalone record-transfer
digression from the body. The broader quantum-foundations provenance remains
visible in the abstract and formal-verification section, while the mathematical
narrative stays centered on projector--unitary commutator profiles.

## Remaining pre-submission work

1. Check the current LAA/Elsevier author guidelines and required submission files.
2. Apply the final LAA/Elsevier class/template if required by the portal.
3. Create a tagged archival formalization release and persistent DOI, then replace/supplement the raw commit reference.
4. Synchronize highlights with the v0.9 title and abstract.
5. Prepare cover letter, data/code availability statement if required, declarations, and portal metadata.

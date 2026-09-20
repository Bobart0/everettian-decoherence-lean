# Stability / rigidity / sharpness paper

Primary target: **Linear Algebra and its Applications (LAA)**.

## Current manuscript states

- `stability_rigidity_sharpness_v01.tex`: first full generic manuscript.
- `stability_rigidity_sharpness_v02.tex`: literature-positioned draft.
- `stability_rigidity_sharpness_v03.tex`: expanded self-contained proof chain.
- `stability_rigidity_sharpness_v04_submission.tex`: first submission-facing draft.
- `stability_rigidity_sharpness_v05_audited.tex`: current reference manuscript after manuscript↔Lean audit corrections.
- `MANUSCRIPT_LEAN_AUDIT_v01.md`: traceability ledger for every principal paper claim.
- `references_v02.bib`: current bibliography.
- `highlights_v02.txt`: five submission highlights.

## Formal reference state

The paper branch was forked from Lean head
`81eb3ff53f6219749b84491513ff437fe7c545c1`, for which the complete CI passed, including the library build, audit aggregate, guards, and diff-hygiene checks.

## Manuscript↔Lean audit status

The v0.5 audit found no mismatch in the main quantitative statements.

Three presentation points were corrected:

1. the general paper definition of the optimal two-cell tail now makes explicit that positive global defect guarantees at least two cells;
2. the three-cell sharpness section now proves that cell 1 is the smallest budget and therefore that `stabilitySharpnessTau` is the *optimal* top-two tail, via `stabilitySharpnessTopTwoTail_eq_Tau`;
3. the formal-verification section now distinguishes the canonical coordinate Hilbert spaces checked in Lean from the coordinate-free finite-dimensional formulation used in the paper.

Static manuscript checks on v0.5:
- no unresolved or duplicated labels;
- no unresolved BibTeX citation keys;
- balanced LaTeX environments and braces.

## Remaining pre-submission work

1. Perform the second-pass priority audit focused specifically on equality and near-equality results for projection/block-commutator inequalities.
2. Refine the sharpness corollary wording so that the “inverse-square necessity” claim is stated in the most precise asymptotic form.
3. Replace the raw GitHub commit reference by a tagged archival release and persistent DOI.
4. Apply the final Elsevier/LAA class or submission template if required by the submission portal.
5. Prepare the cover letter and submission metadata.

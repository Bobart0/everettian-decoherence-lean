# Stability / rigidity / sharpness paper

Primary target: **Linear Algebra and its Applications (LAA)**.

## Current manuscript states

- `stability_rigidity_sharpness_v01.tex`: first full generic manuscript.
- `stability_rigidity_sharpness_v02.tex`: literature-positioned draft.
- `stability_rigidity_sharpness_v03.tex`: expanded self-contained proof chain.
- `stability_rigidity_sharpness_v04_submission.tex`: submission-facing draft with internal editorial notes removed, MSC classification added, AI-assisted formalization described in the formal-verification section, and the Elsevier AI declaration placed immediately before the references.
- `references_v02.bib`: current bibliography.
- `highlights_v02.txt`: five submission highlights.

## Formal reference state

The paper branch was forked from Lean head
`81eb3ff53f6219749b84491513ff437fe7c545c1`, for which the complete CI passed, including the library build, audit aggregate, guards, and diff-hygiene checks.

## Remaining pre-submission work

1. Perform a second-pass priority audit focused specifically on equality and near-equality results for projection/block-commutator inequalities.
2. Audit every mathematical display in v0.4 against the corresponding Lean declarations.
3. Replace the raw GitHub commit reference by a tagged archival release and persistent DOI.
4. Apply the final Elsevier/LAA class or submission template if the portal requires it.
5. Prepare the cover letter and submission metadata.

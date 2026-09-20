# Stability / rigidity / sharpness paper

Primary target: **Linear Algebra and its Applications (LAA)**.

## Current files

- `stability_rigidity_sharpness_v01.tex`: first full generic manuscript.
- `stability_rigidity_sharpness_v02.tex`: literature-positioned draft.
- `stability_rigidity_sharpness_v03.tex`: self-contained quantitative proof chain.
- `stability_rigidity_sharpness_v04_submission.tex`: submission-facing draft; internal editorial notes removed and Elsevier AI disclosure added.
- `references_v02.bib`: current bibliography.
- `highlights_v02.txt`: five LAA-style highlights.

## Formal reference state

The paper branch was forked from Lean head
`81eb3ff53f6219749b84491513ff437fe7c545c1`, for which GitHub Actions run
#218 passed the complete Lean build, audit aggregate, guards, and diff-hygiene
checks.

## Remaining pre-submission work

1. Complete a second-pass priority search focused on near-equality and equality
   cases for projection and block-operator norm inequalities.
2. Audit every mathematical display in v0.4 against the Lean declarations.
3. Replace the raw GitHub commit by a tagged archival release / persistent DOI.
4. Convert the final manuscript to the journal-specific Elsevier/LAA class if
   required by the submission portal.
5. Prepare cover letter and submission metadata.

# Release notes — v0.1.0

## Archival purpose

This is the first archival release of `everettian-decoherence-lean` intended
to support citation and long-term preservation of the Lean 4 artifact used by
the manuscript *Rigidity and Scale-Sharp Stability for Gaps of Finite
Orthogonal Decompositions*.

The mathematical source checkpoint frozen for this release is:

```
e2c0756964c93a894a37c54023a63da731daeb6e
```

GitHub Actions run 293 completed successfully at this checkpoint, including
Lean compilation, library build, upstream-contract checks, audit-contract
build, audit aggregation, guards, and diff-hygiene checks.

The `release/v0.1.0` branch is based exactly on that mathematical checkpoint.
Subsequent commits on this release branch modify only release metadata and
documentation; no Lean theorem source is changed.

## Scientific scope of this release

The release includes the finite post-T5 stability/rigidity/sharpness chain:

- cut-envelope bound and exact two-cell rigidity at positive-defect saturation;
- v12 finite near-saturation estimate with coefficient `18`;
- general small-defect asymptotic coefficient `8`;
- ultra-near asymptotic coefficient `4`;
- explicit sharpness families attaining the constants `8` and `4`;
- continuous two-parameter `ℂ^3` realization
  `U_{d,x} = Q_x R_d Q_x^*`;
- exact cell gaps `f_d(1-x)`, `f_d(x)`, `f_d(1)`;
- exact global budget, maximal cut, envelope defect, and top-two tail;
- fixed-`x` interpolation
  `A tau / eta -> 4 / max{x,1-x}`;
- symmetric path `x = 1/2` giving coefficient `8`;
- ultra-near path `x = d` with `eta/A -> 0` and coefficient `4`.

The repository also contains the earlier ED1-ED4B and T1-T5 formalization
chain.

## Verification surface

The production facade is:

```
EverettianDecoherence.Approximation.StabilitySharpness
```

The publication-facing audit module is:

```
EverettianDecoherence.Audit.StabilityRigiditySharpness
```

and is aggregated by:

```
EverettianDecoherence.Audit.MainResults
```

The paper-to-Lean map is in
`docs/STABILITY_RIGIDITY_SHARPNESS_MAPPING.md`.

## Reproducibility

From the release source archive:

```sh
lake build
bash scripts/validate.sh
bash scripts/guard.sh
```

## Scope limitation

The stability/rigidity results are finite operator-theoretic statements.
This release does not formalize time dynamics, an open-system model,
off-diagonal suppression, environment-induced decoherence, basis selection,
or any new derivation of the Born rule.

## GitHub / Zenodo archiving

Create the GitHub release with tag:

```
v0.1.0
```

targeting the final head of branch `release/v0.1.0`.

The repository intentionally uses `CITATION.cff` and does not include a
`.zenodo.json`. If the repository is enabled in the Zenodo GitHub
integration, publishing this GitHub release will trigger Zenodo ingestion and
mint a version-specific DOI.

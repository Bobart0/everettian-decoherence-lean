# Reproducibility

## Français

La révision amont résolue est
`3129833f3207272eddf9437bd7a3806437b7f87d`.

```sh
lean --version
lake --version
lake build
bash scripts/guard.sh
bash scripts/validate.sh
lake env lean EverettianDecoherence/Audit/UpstreamAPIContract.lean
```

## English

The resolved upstream revision is
`3129833f3207272eddf9437bd7a3806437b7f87d`.

```sh
lean --version
lake --version
lake build
bash scripts/guard.sh
bash scripts/validate.sh
lake env lean EverettianDecoherence/Audit/UpstreamAPIContract.lean
```

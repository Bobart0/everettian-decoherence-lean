# Everettian Decoherence in Lean

## Français

Statut : **ED0 — bootstrap initial sécurisé**. Ce dépôt prépare, avec prudence,
une formalisation Lean 4 de la décorrélation everettienne, de la robustesse
approchée, de la préservation approchée des records, des dynamiques de systèmes
ouverts et de bornes d'erreur quantitatives. Il ne contient aujourd'hui aucun
résultat scientifique local.

La dépendance stable est `everettian-probability-lean v2.0.0`. L'architecture
minimale contient une frontière amont, un arbre source local, un arbre d'audit,
des gardes et une CI.

```sh
lake build
bash scripts/guard.sh
bash scripts/validate.sh
```

La portée et les limitations sont explicites dans `docs/`. Les contributions
se font par incréments atomiques, vérifiés et sans revendication physique non
formalisée. Licence : Apache-2.0.

## English

Status: **ED1 — finite kinematic record-profile geometry**. This repository cautiously
prepares a Lean 4 formalization of Everettian decoherence, approximate
robustness, approximate record preservation, open-system dynamics, and
quantitative error bounds. It currently contains no local scientific result.

The stable dependency is `everettian-probability-lean v2.0.0`. The minimal
architecture has an upstream boundary, local source tree, audit tree, guards,
and CI.

The first local result is `EverettianDecoherence.Metrics.RecordProfileL1`.
It imports `bornRecord`, is therefore BORN-SENSITIVE, and is not a
decoherence theorem. The conditional ED1–ED12 program is documented in
`docs/SCIENTIFIC_ROADMAP.md`.

```sh
lake build
bash scripts/guard.sh
bash scripts/validate.sh
```

Scope and limitations are explicit in `docs/`. Contributions are atomic and
verified, with no unformalized physical claim. License: Apache-2.0.

## ED2A and ED2B

ED2A supplies the elementary bound with a record-cell-count factor. ED2B
supplies the global bound without that factor; import it with:

```lean
import EverettianDecoherence.Metrics.StateRecordDimensionFree
```

ED2B is BORN-SENSITIVE and kinematic, not a decoherence theorem.

## ED3A

```lean
import EverettianDecoherence.Approximation.ApproximateRecordPreservation
```

ED3A separates an algebraic statewise projector-commutator defect from its
BORN-SENSITIVE record-profile transfer. It introduces neither dynamics nor
decoherence.

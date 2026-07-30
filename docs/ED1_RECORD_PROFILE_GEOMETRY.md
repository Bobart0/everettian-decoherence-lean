# ED1 record-profile geometry

## Français

### Objet

La distance L1 compare deux fonctions réelles sur les cellules d'une
perspective finie. La spécialisation `recordProfileL1` compare les profils
`bornRecord`.

### Résultats

Non-négativité, réflexivité, symétrie, triangle, borne cellule par cellule,
séparation exacte, équivalence distance nulle/`SameRecord`, annulation sur
l'orbite unitaire exacte, et composition de `recordProfileWithin` sont
formalisés et audités.

### Dépendance bornienne explicite et limites

Cette métrique de transfert est BORN-SENSITIVE, pas une définition indépendante
de décohérence. ED1 ne prouve aucune borne entre états et profils, Lipschitz,
quasi-commutation, dynamique, système ouvert, factorisation, suppression hors
diagonale, stabilité temporelle, redondance, émergence de records, dérivation
de Born ou norme rationnelle. ED2 étudiera les perturbations de `bornRecord`
avec constantes et normalisation explicites.

## English

### Purpose

L1 compares real-valued functions on cells of a finite perspective. Its
`recordProfileL1` specialization compares `bornRecord` profiles.

### Results

Nonnegativity, reflexivity, symmetry, triangle, coordinate control, exact
separation, zero-distance/`SameRecord` equivalence, vanishing on the exact
unitary orbit, and `recordProfileWithin` composition are formalized and
audited.

### Explicit Born dependence and limits

This transfer metric is BORN-SENSITIVE, not an independent decoherence
definition. ED1 proves no state/profile bound, Lipschitz bound, approximate
commutation, dynamics, open system, factorization, off-diagonal suppression,
temporal stability, redundancy, record emergence, Born derivation, or
rationality norm. ED2 will study perturbations of `bornRecord` with explicit
constants and normalization.

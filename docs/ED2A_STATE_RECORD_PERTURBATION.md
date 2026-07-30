# ED2A state-to-record perturbation

## Français

### Objet et chaîne de preuve

ED2A contrôle la variation d'un profil bornien fini par la distance normique
entre deux états : différence de normes carrées, contraction des projections
de cellule, borne cellule par cellule, sommation L1, borne par cardinalité,
cas normalisé, puis relation recordProfileWithin.

### Résultat

recordProfileL1 D x y ≤ (recordCellCount D : ℝ) *
((‖x‖ + ‖y‖) * ‖x - y‖). Pour des états normalisés :
recordProfileL1 D x y ≤ (2 * (recordCellCount D : ℝ)) * ‖x - y‖.
La borne est correcte, finie, explicite, BORN-SENSITIVE et cinématique ; elle
dépend du nombre de cellules et n'est pas revendiquée optimale.

### Limites

Aucune convergence temporelle, quasi-commutation, suppression hors diagonale,
décohérence, stabilité dynamique, redondance, réciproque profil/état ni
dérivation de Born n'est établie. ED2B reste planifié pour une amélioration
éventuelle par sommation quadratique et Cauchy–Schwarz.

## English

### Purpose and proof chain

ED2A controls variation of a finite Born profile by norm distance between
states: squared-norm difference, cell-projection contraction, pointwise bound,
L1 summation, cardinality bound, normalized case, and recordProfileWithin.

### Result

recordProfileL1 D x y ≤ (recordCellCount D : ℝ) *
((‖x‖ + ‖y‖) * ‖x - y‖). For normalized states:
recordProfileL1 D x y ≤ (2 * (recordCellCount D : ℝ)) * ‖x - y‖.
The bound is correct, finite, explicit, BORN-SENSITIVE, and kinematic; it
depends on cell count and is not claimed optimal.

### Limitations

No time convergence, approximate commutation, off-diagonal suppression,
decoherence, dynamical stability, redundancy, profile/state converse, or Born
derivation is established. ED2B remains planned for a possible quadratic-sum
and Cauchy–Schwarz sharpening.

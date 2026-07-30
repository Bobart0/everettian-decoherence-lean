# ED3A — Statewise projector quasi-commutation

## Français

ED3A mesure, pour une perspective `D`, une isométrie linéaire `U` et un état `x` fournis, le défaut algébrique `P_c (U x) - U (P_c x)`. Sa norme L2 est `sqrt (∑ c, ‖P_c (U x) - U (P_c x)‖ ^ 2)`. Cette définition ne contient pas `bornRecord`, dépend explicitement de `D` et `x`, et n'est pas une norme d'opérateur uniforme.

Le transfert BORN-SENSITIVE établit `recordProfileL1 D (U x) x ≤ 2 * ‖x‖ * statewiseProjectorCommutatorL2 D U x`, et la constante `2` si `‖x‖ = 1`. Un défaut nul implique `SameRecord D (U x) x` pour cet état seulement ; il n'implique aucune commutation globale. Le pare-feu est : perspective donnée + transformation donnée + défaut algébrique → préservation approchée du profil bornien, pas décohérence ni émergence.

Limites : aucune norme d'opérateur, uniformité sur les états, composition, temps, Hamiltonien, système ouvert, suppression hors diagonale, redondance, base émergente, dérivation de Born ou justification normative. ED3B est prévu pour une uniformisation par norme d'opérateur explicitement choisie.

## English

ED3A measures, for supplied perspective `D`, linear isometry `U`, and state `x`, the algebraic defect `P_c (U x) - U (P_c x)`. Its L2 norm is `sqrt (∑ c, ‖P_c (U x) - U (P_c x)‖ ^ 2)`. This definition contains no `bornRecord`, explicitly depends on `D` and `x`, and is not a uniform operator norm.

The BORN-SENSITIVE transfer proves `recordProfileL1 D (U x) x ≤ 2 * ‖x‖ * statewiseProjectorCommutatorL2 D U x`, and constant `2` when `‖x‖ = 1`. Zero defect implies `SameRecord D (U x) x` only at that state; it does not imply global commutation. The firewall is: supplied perspective + supplied transformation + algebraic defect → approximate Born profile preservation, not decoherence or emergence.

Limitations: no operator norm, uniformity over states, composition, time, Hamiltonian, open system, off-diagonal suppression, redundancy, emerging basis, derivation of Born, or normative justification. ED3B is planned for an explicit operator-norm uniformization.

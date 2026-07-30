# Approximation instructions

## Français

Cette couche contient des notions quantitatives algébriques, non des modèles de décohérence. Chaque défaut nomme objet, norme, domaine, état éventuel et constantes ; une quantité dépendant d'un état porte `statewise`. Une petite commutation sur un état n'est ni une commutation globale, ni une norme uniforme, ni une décohérence. Les quantités sans `bornRecord` restent distinctes des transferts BORN-SENSITIVE. Une perspective fournie n'est pas émergée. Aucun temps, Hamiltonien, canal, environnement, matrice densité, trace partielle ou import interne amont n'est permis sans incrément séparé. Les gardes racine restent applicables.

Distinguer strictement `LinearMap` et `ContinuousLinearMap` : une norme
d'opérateur (`‖·‖op`) n'existe que pour le second. `statewise` est obligatoire
si la quantité dépend d'un état ; `uniform` est réservé à une quantité
indépendante de l'état. Ici, l'uniformité porte uniquement sur les états pour
`D` et `U` fixés ; aucune indépendance du nombre de cellules n'est implicite.
Un défaut uniforme nul doit récupérer la commutation globale si cette
propriété est revendiquée. Aucune interprétation temporelle et aucun usage du
mot décohérence ne sont permis dans cette couche.

## English

This layer contains quantitative algebraic notions, not decoherence models. Every defect names its object, norm, domain, possible state, and constants; a state-dependent quantity uses `statewise`. Small commutation at one state is neither global commutation, a uniform norm, nor decoherence. Quantities without `bornRecord` remain distinct from BORN-SENSITIVE transfers. A supplied perspective is not emergent. No time, Hamiltonian, channel, environment, density matrix, partial trace, or upstream internal import is allowed without a separate increment. Root safeguards remain applicable.

Strictly distinguish `LinearMap` from `ContinuousLinearMap`: an operator norm
(`‖·‖op`) exists only for the latter. `statewise` is mandatory whenever a
quantity depends on a state; `uniform` is reserved for a state-independent
quantity. Here, uniformity concerns only states for fixed `D` and `U`; no
independence from cell count is implicit. A zero uniform defect must recover
global commutation whenever that property is claimed. No temporal
interpretation and no use of the word decoherence are allowed in this layer.

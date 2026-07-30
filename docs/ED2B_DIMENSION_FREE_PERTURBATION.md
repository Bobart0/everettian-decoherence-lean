# ED2B — Borne de perturbation indépendante du nombre de cellules

## Français

### Objet

ED2B supprime le facteur de cardinalité d'ED2A en utilisant l'orthogonalité globale des cellules d'une perspective projective finie.

### Résultat principal

```text
recordProfileL1 D x y ≤ (‖x‖ + ‖y‖) * ‖x - y‖.
recordProfileL1 D x y ≤ 2 * ‖x - y‖  si ‖x‖ = ‖y‖ = 1.
```

### Mécanisme

1. Profils des normes de composantes.
2. Factorisation des différences de carrés.
3. Contrôle des différences de normes.
4. Cauchy--Schwarz fini sur les deux sommes.
5. Pythagore sur la décomposition orthogonale.
6. Suppression du facteur `recordCellCount`.

### Comparaison avec ED2A

ED2A établit `recordProfileL1 D x y ≤ card(cells D) * ((‖x‖ + ‖y‖) * ‖x - y‖)` par une preuve coordonnée élémentaire. ED2B est une borne globale plus informative lorsque le nombre de cellules dépasse un. ED2A reste correct et utile. Aucune optimalité ni saturation de constante n'est revendiquée.

### Portée et limitations

La portée est celle des espaces de Hilbert complexes finis du dépôt amont, des perspectives projectives finies, des états purs, de la distance normique et du profil de record bornien. Le résultat est cinématique et BORN-SENSITIVE. Il ne prouve ni réciproque, ni distance de trace, ni états mixtes, ni POVM générale, ni dynamique, ni quasi-commutation, ni décohérence, ni stabilité temporelle, ni redondance environnementale, ni dérivation de Born.

« Dimension-free » signifie seulement indépendant du nombre de cellules de la perspective, et non une extension démontrée aux espaces de Hilbert infinis.

### Étape suivante

ED3 devra choisir une norme de commutateur et étudier « quasi-commutation → préservation approchée des composantes de record », sans être présenté comme un théorème complet de décohérence.

## English

### Purpose

ED2B removes ED2A's cardinality factor by using the global orthogonality of the cells of a finite projective perspective.

### Main result

```text
recordProfileL1 D x y ≤ (‖x‖ + ‖y‖) * ‖x - y‖.
recordProfileL1 D x y ≤ 2 * ‖x - y‖  when ‖x‖ = ‖y‖ = 1.
```

### Mechanism

1. Norm profiles of the components.
2. Factor differences of squares.
3. Control norm differences.
4. Finite Cauchy--Schwarz on the two sums.
5. Pythagoras for the orthogonal decomposition.
6. Remove the `recordCellCount` factor.

### Comparison with ED2A

ED2A proves `recordProfileL1 D x y ≤ card(cells D) * ((‖x‖ + ‖y‖) * ‖x - y‖)` by an elementary coordinatewise proof. ED2B is a more informative global bound when there is more than one cell. ED2A remains correct and useful. No optimality or saturation claim is made.

### Scope and limitations

The scope is the upstream repository's finite complex Hilbert spaces, finite projective perspectives, pure states, norm distance, and Born record profile. The result is kinematic and BORN-SENSITIVE. It proves no converse, trace-distance comparison, mixed-state extension, general POVM, dynamics, approximate commutation, decoherence, temporal stability, environmental redundancy, or derivation of Born.

“Dimension-free” means only independent of the perspective's cell count, not a proved extension to infinite-dimensional Hilbert spaces.

### Next step

ED3 will choose a commutator norm and study “approximate commutation → approximate preservation of record components”, without being described as a complete decoherence theorem.

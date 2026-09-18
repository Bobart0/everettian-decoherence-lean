# ED3B — Operator-Norm Uniformization
# ED3B — Uniformisation par normes d'opérateur

## Français

### 1. Objet

ED3B transforme le contrôle relatif à un état d'ED3A en un contrôle uniforme
sur les états, pour une perspective `D` et une transformation `U` fixées. Le
défaut statewise `statewiseProjectorCommutatorL2 D U x` d'ED3A dépend de
l'état `x` fourni ; ED3B introduit une quantité `operatorNormProjectorCommutatorL2 D U`
qui ne dépend que de `D` et `U`, et qui borne le défaut statewise pour tout
état simultanément.

### 2. Commutateur continu

`perspectiveProjectorCommutatorCLM D U c` est la version `ContinuousLinearMap`
du commutateur algébrique ED3A `perspectiveProjectorCommutator D U c`. Le
théorème `perspectiveProjectorCommutatorCLM_apply` montre que son application
à un état coïncide exactement avec l'application du commutateur algébrique :
`perspectiveProjectorCommutatorCLM D U c x = perspectiveProjectorCommutator D U c x`.
Ce passage à `ContinuousLinearMap` est nécessaire pour disposer d'une norme
d'opérateur (`ContinuousLinearMap.opNorm`) ; il n'introduit aucune nouvelle
hypothèse physique et ne modifie l'application sous-jacente en aucun point.

### 3. Profil de normes d'opérateur

`perspectiveProjectorCommutatorOpNormProfile D U c = ‖perspectiveProjectorCommutatorCLM D U c‖op`,
c'est-à-dire `‖P_c U - U P_c‖op` : la norme d'opérateur du commutateur de
projecteur pour la cellule `c`, sans référence à un état particulier.

### 4. Agrégation L2 uniforme

```text
operatorNormProjectorCommutatorL2 D U
= sqrt (∑ c, ‖P_c U - U P_c‖op ^ 2).
```

Cette quantité ne dépend d'aucun état `x` ; elle dépend de `D` et de `U`, et
peut dépendre du nombre de cellules de `D`. Sa définition ne contient aucune
occurrence de `bornRecord` ni de `recordProfileL1`.

### 5. Contrôle du défaut statewise

```text
statewiseProjectorCommutatorL2 D U x
≤ operatorNormProjectorCommutatorL2 D U * ‖x‖.
```

Les deux ponts quantitatifs vers ED3A sont :

```text
operatorNormProjectorCommutatorWithin D U ε
→ statewiseProjectorCommutatorWithin D U x (ε * ‖x‖).
```

et, pour un état normalisé (`‖x‖ = 1`) :

```text
operatorNormProjectorCommutatorWithin D U ε
→ statewiseProjectorCommutatorWithin D U x ε.
```

### 6. Transfert vers le profil de record

**BORN-SENSITIVE TRANSFER.**

```text
recordProfileL1 D (U x) x
≤ 2 * ‖x‖ ^ 2 * operatorNormProjectorCommutatorL2 D U.
```

Pour un état normalisé :

```text
recordProfileL1 D (U x) x
≤ 2 * operatorNormProjectorCommutatorL2 D U.
```

La couche T5B affine ensuite cette borne à la constante optimale :

```text
recordProfileL1 D (U x) x
≤ sqrt 2 * ‖x‖ ^ 2 * operatorNormProjectorCommutatorL2 D U.
```

Pour un état normalisé :

```text
recordProfileL1 D (U x) x
≤ sqrt 2 * operatorNormProjectorCommutatorL2 D U.
```

Combinée au témoin T5A de ratio exactement `sqrt 2`, cette borne caractérise
les coefficients universels normalisés : `K` convient si et seulement si
`sqrt 2 ≤ K`. L'ancienne borne de constante `2` reste un théorème valide,
mais n'est plus la meilleure constante connue.

### 7. Limite exacte

```text
operatorNormProjectorCommutatorL2 D U = 0
↔ ∀ c, perspectiveProjectorCommutator D U c = 0.
```

Cette équivalence caractérise le défaut uniforme nul par une **commutation
globale** : l'égalité d'opérateurs `P_c U = U P_c` pour chaque cellule `c`,
pour tous les états simultanément — et non plus seulement en un état donné
comme en ED3A. Elle implique :

```text
operatorNormProjectorCommutatorL2 D U = 0
→ ∀ x, SameRecord D (U x) x.
```

La commutation est globale sur les états pour chaque projecteur, mais reste
relative à la perspective `D` fournie. Aucune perspective émergée n'est
obtenue : `D` demeure une donnée, pas un résultat.

### 8. Cas identité

`operatorNormProjectorCommutatorL2_refl` établit :

```text
operatorNormProjectorCommutatorL2 D (LinearIsometryEquiv.refl ℂ (Gleason.H n)) = 0.
```

### 9. Sens exact d'« uniforme »

Le mot « uniforme » signifie uniquement : **uniforme sur les états, pour `D`
et `U` fixés**. Il ne signifie pas :

- uniforme sur les perspectives ;
- uniforme sur le nombre de cellules ;
- uniforme sur les dimensions ;
- uniforme dans le temps ;
- indépendant de la décomposition.

La quantité `operatorNormProjectorCommutatorL2 D U` peut dépendre du nombre
de cellules de `D`.

### 10. Relation ED3A / ED3B

| Couche | Dépend de x | Objet |
|---|---:|---|
| ED3A | oui | L2 des commutateurs appliqués à x |
| ED3B | non | L2 des normes d'opérateur |
| transfert ED3A/ED3B | oui dans la conclusion | distance de profil bornienne |

### 11. Ce qui n'est pas démontré

- aucune composition de transformations ;
- aucune itération ;
- aucune accumulation d'erreurs ;
- aucun temps ;
- aucun Hamiltonien ;
- aucun canal ;
- aucun système ouvert ;
- aucun état mixte ;
- aucune factorisation système/environnement ;
- aucune suppression hors diagonale ;
- aucune décohérence ;
- aucune sélection de base ;
- aucune émergence de records ;
- aucune redondance environnementale ;
- aucune dérivation de Born ;
- aucune optimalité de l'agrégation L2.

### 12. État aval

ED4A et ED4B sont désormais **FORMALIZED / AUDITED** dans leurs portées finies
respectives de composition à perspective fixée et d'itération/accumulation.
Le cycle transversal T0–T5 a ensuite étudié les contrôles de structure et de
sharpness associés. En particulier, T5A et T5B établissent ensemble que le
coefficient universel optimal du transfert ED3B sur les états normalisés est
`sqrt 2`.

Ces développements ne changent pas la nature d'ED3B : le défaut de
commutateur reste une quantité algébrique NON BORN-SENSITIVE, tandis que le
transfert vers `recordProfileL1` est BORN-SENSITIVE. Aucun T6 ni nouveau
jalon physique n'est ouvert par cette mise à jour documentaire.

## English

### 1. Purpose

ED3B turns ED3A's state-relative control into a control uniform over states,
for a fixed perspective `D` and transformation `U`. ED3A's statewise defect
`statewiseProjectorCommutatorL2 D U x` depends on the supplied state `x`; ED3B
introduces a quantity `operatorNormProjectorCommutatorL2 D U` that depends
only on `D` and `U`, and that bounds the statewise defect for every state at
once.

### 2. Continuous commutator

`perspectiveProjectorCommutatorCLM D U c` is the `ContinuousLinearMap` version
of the ED3A algebraic commutator `perspectiveProjectorCommutator D U c`. The
theorem `perspectiveProjectorCommutatorCLM_apply` shows its application to a
state coincides exactly with the algebraic commutator's application:
`perspectiveProjectorCommutatorCLM D U c x = perspectiveProjectorCommutator D U c x`.
This passage to `ContinuousLinearMap` is required to access an operator norm
(`ContinuousLinearMap.opNorm`); it introduces no new physical hypothesis and
does not change the underlying application anywhere.

### 3. Operator-norm profile

`perspectiveProjectorCommutatorOpNormProfile D U c = ‖perspectiveProjectorCommutatorCLM D U c‖op`,
i.e. `‖P_c U - U P_c‖op`: the operator norm of the projector commutator for
cell `c`, with no reference to any particular state.

### 4. Uniform L2 aggregation

```text
operatorNormProjectorCommutatorL2 D U
= sqrt (∑ c, ‖P_c U - U P_c‖op ^ 2).
```

This quantity has no dependence on any state `x`; it depends on `D` and `U`,
and may depend on the cell count of `D`. Its definition contains no
occurrence of `bornRecord` or `recordProfileL1`.

### 5. Control of the statewise defect

```text
statewiseProjectorCommutatorL2 D U x
≤ operatorNormProjectorCommutatorL2 D U * ‖x‖.
```

The two quantitative bridges to ED3A are:

```text
operatorNormProjectorCommutatorWithin D U ε
→ statewiseProjectorCommutatorWithin D U x (ε * ‖x‖).
```

and, for a normalized state (`‖x‖ = 1`):

```text
operatorNormProjectorCommutatorWithin D U ε
→ statewiseProjectorCommutatorWithin D U x ε.
```

### 6. Transfer to the record profile

**BORN-SENSITIVE TRANSFER.**

```text
recordProfileL1 D (U x) x
≤ 2 * ‖x‖ ^ 2 * operatorNormProjectorCommutatorL2 D U.
```

For a normalized state:

```text
recordProfileL1 D (U x) x
≤ 2 * operatorNormProjectorCommutatorL2 D U.
```

T5B then sharpens this to the optimal coefficient:

```text
recordProfileL1 D (U x) x
≤ sqrt 2 * ‖x‖ ^ 2 * operatorNormProjectorCommutatorL2 D U.
```

For a normalized state:

```text
recordProfileL1 D (U x) x
≤ sqrt 2 * operatorNormProjectorCommutatorL2 D U.
```

Combined with the T5A witness whose ratio is exactly `sqrt 2`, this
characterizes normalized universal coefficients: `K` works if and only if
`sqrt 2 ≤ K`. The former coefficient-`2` bound remains a valid theorem, but
is no longer the best known constant.

### 7. Exact limit

```text
operatorNormProjectorCommutatorL2 D U = 0
↔ ∀ c, perspectiveProjectorCommutator D U c = 0.
```

This equivalence characterizes a zero uniform defect by **global
commutation**: operator equality `P_c U = U P_c` for every cell `c`, for all
states simultaneously — not merely at one supplied state as in ED3A. It
implies:

```text
operatorNormProjectorCommutatorL2 D U = 0
→ ∀ x, SameRecord D (U x) x.
```

Commutation is global over states for each projector, yet remains relative to
the supplied perspective `D`. No emergent perspective is obtained: `D` remains
a given, not a result.

### 8. Identity case

`operatorNormProjectorCommutatorL2_refl` establishes:

```text
operatorNormProjectorCommutatorL2 D (LinearIsometryEquiv.refl ℂ (Gleason.H n)) = 0.
```

### 9. Exact meaning of "uniform"

The word "uniform" means only: **uniform over states, for fixed `D` and
`U`**. It does not mean:

- uniform over perspectives;
- uniform over the number of cells;
- uniform over dimensions;
- uniform in time;
- independent of the decomposition.

The quantity `operatorNormProjectorCommutatorL2 D U` may depend on the cell
count of `D`.

### 10. ED3A / ED3B relation

| Layer | Depends on x | Object |
|---|---:|---|
| ED3A | yes | L2 of commutators applied to x |
| ED3B | no | L2 of operator norms |
| ED3A/ED3B transfer | yes in the conclusion | Born profile distance |

### 11. What is not proven

- no composition of transformations;
- no iteration;
- no error accumulation;
- no time;
- no Hamiltonian;
- no channel;
- no open system;
- no mixed state;
- no system/environment factorization;
- no off-diagonal suppression;
- no decoherence;
- no basis selection;
- no record emergence;
- no environmental redundancy;
- no derivation of Born;
- no optimality of the L2 aggregation.

### 12. Downstream status

ED4A and ED4B are now **FORMALIZED / AUDITED** in their respective finite
scopes of fixed-perspective composition and finite iteration/error
accumulation. The transversal T0–T5 cycle then studied the associated
structure and sharpness controls. In particular, T5A and T5B together establish
that the optimal universal ED3B transfer coefficient on normalized states is
`sqrt 2`.

These developments do not change the nature of ED3B: the commutator defect
remains a NON BORN-SENSITIVE algebraic quantity, while transfer to
`recordProfileL1` is BORN-SENSITIVE. This documentation update opens neither
T6 nor any new physical milestone.

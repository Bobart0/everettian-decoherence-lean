# Program status

## Français

Date : **2026-09-22**. Version : **0.2.0-dev**. Statut :
**ED4B — CLOSED IN ITS FINITE ITERATION-ACCUMULATION SCOPE** ;
**cycle transversal T0–T5 — CLOSED ; T1–T5 FORMALIZED / AUDITED**.

Aucun statut **PUBLISHED** n'est revendiqué pour T0–T5.

### Résumé des couches ED

- **ED1** — *CLOSED IN ITS FINITE KINEMATIC SCOPE* : géométrie L1 finie et
  profils de records BORN-SENSITIVE.
- **ED2A** — *CLOSED IN ITS EXPLICIT FINITE SCOPE* : borne état→record avec
  facteur de cardinalité.
- **ED2B** — *CLOSED IN ITS FINITE DECOMPOSITION-AWARE SCOPE* : borne globale
  sans facteur de cardinalité, de constante normalisée `2`.
- **ED3A** — *CLOSED IN ITS FINITE STATEWISE UNITARY SCOPE* : défaut de
  commutation statewise et transfert BORN-SENSITIVE.
- **ED3B** — *CLOSED IN ITS FINITE OPERATOR-NORM UNIFORM SCOPE* :
  uniformisation par normes d'opérateur, limite exacte vers la commutation
  globale et transfert uniforme.
- **ED4A** — *CLOSED IN ITS FINITE FIXED-PERSPECTIVE COMPOSITION SCOPE* :
  composition de deux transformations et sous-additivité du défaut.
- **ED4B** — *CLOSED IN ITS FINITE ITERATION-ACCUMULATION SCOPE* :
  composition d'une liste finie et accumulation additive des défauts.

### Cycle transversal T0–T5

- **T0** — réconciliation documentaire des statuts et de la portée ; aucune
  nouvelle preuve scientifique.
- **T1 `ProjectorStructureStability`** — **FORMALIZED / AUDITED**, NON
  BORN-SENSITIVE : contrôle de l'écart entre projecteurs transportés et
  projecteurs fournis.
- **T2 `DimensionFreeSharpness`** — **FORMALIZED / AUDITED**,
  BORN-SENSITIVE : sharpness de la constante `2` de la borne ED2B.
- **T3 `IterationSharpness`** — **FORMALIZED / AUDITED**, NON
  BORN-SENSITIVE : sharpness asymptotique du coefficient additif `1` de
  l'accumulation ED4B.
- **T4 `WorkedInstance`** — **FORMALIZED / AUDITED** : instance exacte en
  dimension `2`, séparant défaut NON BORN-SENSITIVE et transfert de profil
  BORN-SENSITIVE.
- **T5A `UniformTransferSharpness`** — **FORMALIZED / AUDITED / MERGED**,
  BORN-SENSITIVE : famille normalisée de ratio exactement `sqrt 2`, donc
  barrière inférieure pour tout coefficient ED3B universel.
- **T5B `UniformTransferOptimality`** — **FORMALIZED / AUDITED / MERGED** :
  borne universelle correspondante et caractérisation exacte des coefficients.

**Tx** est la clôture documentaire de ce cycle. Il n'ouvre **aucun T6** et
n'ajoute aucun énoncé mathématique.

### Résultats quantitatifs les plus forts

Pour toute perspective finie fournie `D`, toute unitaire fournie `U` et tout
état `x` :

```text
recordProfileL1 D (U x) x
≤ sqrt 2 * ‖x‖ ^ 2 * operatorNormProjectorCommutatorL2 D U.
```

Pour `‖x‖ = 1` :

```text
recordProfileL1 D (U x) x
≤ sqrt 2 * operatorNormProjectorCommutatorL2 D U.
```

Et la constante est optimale dans cette portée :

```text
IsUniversalUniformTransferCoefficient K ↔ Real.sqrt 2 ≤ K.
```

L'ancienne borne ED3B de constante `2` reste correcte, mais n'est plus la
meilleure constante universelle connue dans cette portée.

Le défaut `operatorNormProjectorCommutatorL2` et les bornes purement
commutatoriales de T5B sont **NON BORN-SENSITIVE**. Le transfert vers
`recordProfileL1`, ainsi que l'argument de saturation T5A, sont
**BORN-SENSITIVE**.

### Front post-T5 de stabilité quantitative

Ce front transversal est **FORMALIZED / AUDITED** et **NON BORN-SENSITIVE**.
Il formalise l'enveloppe des cuts, la rigidité exacte à saturation, la queue
top-two optimale, la borne finie à constante `18`, les coefficients
asymptotiques sharp `8` et `4`, la famille continue `C^3`, les mécanismes
de la proposition à budget fixé, et la famille diffuse géométrique à `2m`
cellules avec seuil sharp `1/8` lorsque la queue tend vers `1`.

La définition order-théorique unique de
`C_fix(A0) = lim_{eps↓0} sup(...)` reste un emballage de manuscrit ; les
estimations finies, le témoin inférieur à trois cellules et l'argument diagonal
de constante `4` sont machine-checkés séparément. Ce front n'ouvre aucun
jalon physique T6/ED5 et n'introduit aucune dynamique ni décohérence.

### Frontière de portée

Le cycle T0–T5 n'introduit aucun temps, Hamiltonien, canal, système ouvert,
état mixte, suppression hors diagonale, mécanisme de décohérence, sélection de
base ou émergence de perspective. Les modules de factorisation coordonnée déjà
présents dans le dépôt sont des briques typées séparées ; leur existence
n'ouvre pas à elle seule un nouveau jalon physique ED5–ED12.

Aucun T6 et aucun nouveau jalon physique ne sont ouverts par Tx.

## English

Date: **2026-09-22**. Version: **0.2.0-dev**. Status:
**ED4B — CLOSED IN ITS FINITE ITERATION-ACCUMULATION SCOPE**;
**transversal T0–T5 cycle — CLOSED; T1–T5 FORMALIZED / AUDITED**.

No **PUBLISHED** status is claimed for T0–T5.

### ED-layer summary

- **ED1** — *CLOSED IN ITS FINITE KINEMATIC SCOPE*: finite L1 geometry and
  BORN-SENSITIVE record profiles.
- **ED2A** — *CLOSED IN ITS EXPLICIT FINITE SCOPE*: state-to-record bound with
  a cardinality factor.
- **ED2B** — *CLOSED IN ITS FINITE DECOMPOSITION-AWARE SCOPE*: global bound
  without a cardinality factor, normalized coefficient `2`.
- **ED3A** — *CLOSED IN ITS FINITE STATEWISE UNITARY SCOPE*: statewise
  commutator defect and BORN-SENSITIVE transfer.
- **ED3B** — *CLOSED IN ITS FINITE OPERATOR-NORM UNIFORM SCOPE*: operator-norm
  uniformization, exact global-commutation limit, and uniform transfer.
- **ED4A** — *CLOSED IN ITS FINITE FIXED-PERSPECTIVE COMPOSITION SCOPE*:
  two-transformation composition and defect subadditivity.
- **ED4B** — *CLOSED IN ITS FINITE ITERATION-ACCUMULATION SCOPE*: finite-list
  composition and additive defect accumulation.

### Transversal T0–T5 cycle

- **T0** — documentation-only reconciliation of status and scope; no new
  scientific theorem.
- **T1 `ProjectorStructureStability`** — **FORMALIZED / AUDITED**, NON
  BORN-SENSITIVE: control of supplied versus transported projectors.
- **T2 `DimensionFreeSharpness`** — **FORMALIZED / AUDITED**,
  BORN-SENSITIVE: sharpness of the ED2B coefficient `2`.
- **T3 `IterationSharpness`** — **FORMALIZED / AUDITED**, NON
  BORN-SENSITIVE: asymptotic sharpness of the ED4B additive coefficient `1`.
- **T4 `WorkedInstance`** — **FORMALIZED / AUDITED**: exact dimension-`2`
  instance separating the NON BORN-SENSITIVE defect from the BORN-SENSITIVE
  profile transfer.
- **T5A `UniformTransferSharpness`** — **FORMALIZED / AUDITED / MERGED**,
  BORN-SENSITIVE: a normalized family with exact ratio `sqrt 2`, giving the
  lower barrier for every universal ED3B coefficient.
- **T5B `UniformTransferOptimality`** — **FORMALIZED / AUDITED / MERGED**:
  the matching universal upper bound and exact coefficient characterization.

**Tx** is the documentation-only closure of this cycle. It opens **no T6** and
adds no mathematical statement.

### Strongest current quantitative results

For every supplied finite perspective `D`, supplied unitary `U`, and state
`x`:

```text
recordProfileL1 D (U x) x
≤ sqrt 2 * ‖x‖ ^ 2 * operatorNormProjectorCommutatorL2 D U.
```

For `‖x‖ = 1`:

```text
recordProfileL1 D (U x) x
≤ sqrt 2 * operatorNormProjectorCommutatorL2 D U.
```

The coefficient is optimal in this scope:

```text
IsUniversalUniformTransferCoefficient K ↔ Real.sqrt 2 ≤ K.
```

The previous coefficient-`2` ED3B bound remains correct, but it is no longer
the best universal coefficient known in this scope.

The `operatorNormProjectorCommutatorL2` defect and the purely commutator
bounds in T5B are **NON BORN-SENSITIVE**. Transfer to `recordProfileL1` and
the T5A saturation argument are **BORN-SENSITIVE**.

### Post-T5 quantitative-stability front

This transversal front is **FORMALIZED / AUDITED** and **NON BORN-SENSITIVE**.
It formalizes the cut envelope, exact saturation rigidity, the exact optimal
top-two tail, the finite coefficient `18`, sharp asymptotic coefficients
`8` and `4`, the continuous `C^3` family, the proof mechanisms of the
fixed-budget proposition, and the geometric diffuse `2m`-cell family with
sharp threshold `1/8` as the tail tends to `1`.

The single order-theoretic object
`C_fix(A0) = lim_{eps↓0} sup(...)` remains manuscript-level packaging; the
finite estimates, three-cell lower witness, and coefficient-`4` diagonal
argument are machine-checked separately. This front opens no physical T6/ED5
milestone and introduces no dynamics or decoherence.

### Scope boundary

The T0–T5 cycle introduces no time, Hamiltonian, channel, open system, mixed
state, off-diagonal suppression, decoherence mechanism, basis selection, or
perspective emergence. Coordinate-factorization modules already present in the
repository remain separate typed building blocks; their existence alone does
not open a new ED5–ED12 physical milestone.

Tx opens neither T6 nor any new physical milestone.

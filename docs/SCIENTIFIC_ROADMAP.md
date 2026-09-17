# Scientific roadmap

## Français

### Chronologie courante

ED0 est **CLOSED IN BOOTSTRAP SCOPE**. ED1 est **CLOSED IN ITS FINITE
KINEMATIC SCOPE** : métrique L1 générique, profil bornien, équivalence
distance nulle/`SameRecord`, annulation sur orbite unitaire et relation
`recordProfileWithin`. ED2A est **CLOSED IN ITS EXPLICIT FINITE SCOPE** : borne
état-vers-record élémentaire avec facteur de cardinalité. ED2B est **CLOSED IN
ITS FINITE DECOMPOSITION-AWARE SCOPE** : Cauchy--Schwarz fini et identité de
Pythagore globale suppriment ce facteur ; la version normalisée a constante 2,
sans revendication d'optimalité dans le jalon ED2B lui-même. ED3A est **CLOSED
IN ITS FINITE STATEWISE UNITARY SCOPE** : commutateurs de projecteurs
algébriques, défaut statewise L2, transfert BORN-SENSITIVE vers le profil de
record, cas normalisé, et limite exacte vers `SameRecord` en un état donné.
ED3B est **CLOSED IN ITS FINITE OPERATOR-NORM UNIFORM SCOPE** : version
`ContinuousLinearMap` du commutateur, profil de normes d'opérateur, agrégation
L2 uniforme sur les états pour une perspective et une transformation fixées,
contrôle du défaut statewise, transfert BORN-SENSITIVE uniforme, et limite
exacte équivalente à la commutation globale.

ED4A est **CLOSED IN ITS FINITE FIXED-PERSPECTIVE COMPOSITION SCOPE** :
`ComposedProjectorCommutator.lean` formalise la composition de deux
transformations, la décomposition du commutateur composé et la sous-additivité
du défaut uniforme ; `ComposedRecordPreservation.lean` fournit le transfert
BORN-SENSITIVE correspondant. ED4B est **CLOSED IN ITS FINITE
ITERATION-ACCUMULATION SCOPE** : `IteratedProjectorCommutator.lean` formalise
la composition d'une liste finie et notamment
`operatorNormProjectorCommutatorL2_iterated_le_sum` ;
`IteratedRecordPreservation.lean` formalise notamment
`recordProfileL1_iterated_le_two_mul_operatorNormProjectorCommutatorSum`,
BORN-SENSITIVE. Les audits ED4A et ED4B sont intégrés à `Audit/MainResults.lean`.
Ces jalons sont donc formalisés et audités ; aucun statut de publication
supplémentaire n'est affirmé ici.

Le contrôle T1 `ProjectorStructureStability` est **FORMALIZED / AUDITED** et
explicitement **NON BORN-SENSITIVE**. Pour chaque cellule `c`, il compare
`U P_c U⁻¹` à `P_c` en norme d'opérateur et montre que cet écart est majoré
par la norme du commutateur correspondant ; l'agrégat L2 des écarts est donc
majoré par `operatorNormProjectorCommutatorL2`. Ce résultat ne définit ni une
décohérence ni une perspective émergente. Aucun statut **PUBLISHED** n'est
revendiqué.

T2 `DimensionFreeSharpness` est **FORMALIZED / NOT YET COMPILE-VERIFIED** et
explicitement **BORN-SENSITIVE**. Le module construit en dimension `2` une
famille rationnelle normalisée issue de la récurrence
`(p,q) ↦ (3p+4q, 2p+3q)` avec invariant `p^2 + 1 = 2 q^2`, calcule le quotient
`recordProfileL1 / ‖x-y‖`, vise la preuve qu'il tend vers `2` et le corollaire
que toute constante universelle `K < 2` échoue sur un membre de la famille.
Le fichier d'audit T2 est présent, mais T2 ne sera classé **AUDITED** qu'après
compilation et exécution de cet audit. Aucun statut **PUBLISHED** n'est
revendiqué.

ED5–ED12 sont **NOT OPENED** dans cette feuille de route. Aucun de ces statuts
ne promet de résultat.

ED1 utilise `bornRecord` et n'est donc pas un critère indépendant de
décohérence ; il en va de même pour tout transfert ED2A–ED4B utilisant
`recordProfileL1` ou `SameRecord`, ainsi que pour T2. Les défauts de
commutateur ED3A–ED4B et le contrôle T1, qui n'utilisent pas `bornRecord`,
restent des quantités algébriques distinctes des transferts BORN-SENSITIVE.

### Chaîne conditionnelle visée

1. métriques quantitatives (ED1) ;
2. perturbations état→record (ED2A, ED2B) ;
3. quasi-commutation statewise (ED3A) et son uniformisation par norme
   d'opérateur (ED3B) ;
4. composition à perspective fixée (ED4A) ;
5. itération finie et calcul compositionnel d'erreurs (ED4B) ;
6. factorisation système/environnement typée ;
7. dynamiques ou canaux explicites ;
8. suppression hors-diagonale ;
9. stabilité et redondance de records ;
10. transfert vers profils borniens ;
11. transfert vers poids, espérances et ratios amont avec dénominateurs
    minorés ;
12. contre-modèles, agrégation, audit d'API et release éventuelle.

T1 est un résultat de contrôle algébrique transversal ajouté sans ouvrir une
nouvelle étape physique de cette chaîne. T2 est un résultat de sharpness
métrique BORN-SENSITIVE, également transversal. Les étapes au-delà d'ED4B
restent **NOT OPENED** dans cette feuille de route et ne sont pas numérotées de
façon définitive tant qu'un incrément d'architecture séparé ne les ouvre pas.

### Pare-feu logique

Mathématiques génériques → approximation algébrique (ED3A–ED4B et T1) →
dynamiques explicites futures → décohérence algébrique future → émergence ou
stabilité future des records → transfert sensible à Born → conséquences
décisionnelles conditionnelles. Les futures couches physiques n'utilisent pas
de crédence, vraisemblance ou axiome de rationalité. Toute quantité utilisant
`bornRecord` est **BORN-SENSITIVE** ; T1 est **NON BORN-SENSITIVE** et T2 est
**BORN-SENSITIVE**. Une faible distance de profils, une faible variation de
projecteurs ou une commutation globale de projecteurs n'est pas une
décohérence physique. Trace partielle, canal ou matrice densité devront
distinguer identité mathématique, hypothèse dynamique, interprétation physique
et transfert bornien.

## English

### Current chronology

ED0 is **CLOSED IN BOOTSTRAP SCOPE**. ED1 is **CLOSED IN ITS FINITE KINEMATIC
SCOPE**: generic L1 metric, Born-sensitive profile, zero-distance/`SameRecord`
equivalence, vanishing on the unitary orbit, and `recordProfileWithin`. ED2A
is **CLOSED IN ITS EXPLICIT FINITE SCOPE**: an elementary state-to-record
bound with a cardinality factor. ED2B is **CLOSED IN ITS FINITE
DECOMPOSITION-AWARE SCOPE**: finite Cauchy--Schwarz and the global Pythagorean
identity remove that factor; the normalized version has constant 2, with no
optimality claim inside the ED2B milestone itself. ED3A is **CLOSED IN ITS
FINITE STATEWISE UNITARY SCOPE**: algebraic projector commutators, a statewise
L2 defect, BORN-SENSITIVE transfer to the record profile, a normalized case,
and an exact `SameRecord` limit at a given state. ED3B is **CLOSED IN ITS
FINITE OPERATOR-NORM UNIFORM SCOPE**: the `ContinuousLinearMap` version of the
commutator, an operator-norm profile, an L2 aggregation uniform over states for
a fixed perspective and transformation, control of the statewise defect, a
uniform BORN-SENSITIVE transfer, and an exact limit equivalent to global
commutation.

ED4A is **CLOSED IN ITS FINITE FIXED-PERSPECTIVE COMPOSITION SCOPE**:
`ComposedProjectorCommutator.lean` formalizes composition of two
transformations, decomposition of the composed commutator, and subadditivity
of the uniform defect; `ComposedRecordPreservation.lean` supplies the
corresponding BORN-SENSITIVE transfer. ED4B is **CLOSED IN ITS FINITE
ITERATION-ACCUMULATION SCOPE**: `IteratedProjectorCommutator.lean` formalizes
composition of a finite list and, in particular,
`operatorNormProjectorCommutatorL2_iterated_le_sum`;
`IteratedRecordPreservation.lean` formalizes, in particular,
`recordProfileL1_iterated_le_two_mul_operatorNormProjectorCommutatorSum`, which
is BORN-SENSITIVE. The ED4A and ED4B audits are integrated into
`Audit/MainResults.lean`. These milestones are therefore formalized and
audited; no additional publication status is asserted here.

The T1 `ProjectorStructureStability` control is **FORMALIZED / AUDITED** and
explicitly **NON BORN-SENSITIVE**. For each cell `c`, it compares `U P_c U⁻¹`
with `P_c` in operator norm and proves that this displacement is bounded by
the corresponding commutator norm; the L2 aggregate of displacements is
therefore bounded by `operatorNormProjectorCommutatorL2`. This result defines
neither decoherence nor an emergent perspective. No **PUBLISHED** status is
claimed.

T2 `DimensionFreeSharpness` is **FORMALIZED / NOT YET COMPILE-VERIFIED** and
explicitly **BORN-SENSITIVE**. The module builds, in dimension `2`, a
normalized rational family generated by `(p,q) ↦ (3p+4q, 2p+3q)` with invariant
`p^2 + 1 = 2 q^2`, computes the `recordProfileL1 / ‖x-y‖` ratio, targets a proof
that it tends to `2`, and the corollary that every universal constant `K < 2`
fails on some family member. The T2 audit file is present, but T2 will be
classified as **AUDITED** only after compilation and execution of that audit.
No **PUBLISHED** status is claimed.

ED5–ED12 are **NOT OPENED** in this roadmap. None of these statuses promises a
result.

ED1 uses `bornRecord` and is therefore not an independent decoherence
criterion; the same holds for every ED2A–ED4B transfer using
`recordProfileL1` or `SameRecord`, and for T2. The ED3A–ED4B commutator defects
and T1 control, which do not use `bornRecord`, remain algebraic quantities
distinct from BORN-SENSITIVE transfers.

### Conditional target chain

1. quantitative metrics (ED1);
2. state-to-record perturbations (ED2A, ED2B);
3. statewise approximate commutation (ED3A) and its operator-norm
   uniformization (ED3B);
4. composition at a fixed perspective (ED4A);
5. finite iteration and compositional error calculus (ED4B);
6. typed system/environment factorization;
7. explicit dynamics or channels;
8. off-diagonal suppression;
9. record stability and redundancy;
10. transfer to Born profiles;
11. transfer to upstream weights, expectations, and ratios with
    lower-bounded denominators;
12. countermodels, aggregation, API audit, and possible release.

T1 is a transversal algebraic control result added without opening a new
physical stage of this chain. T2 is a transversal BORN-SENSITIVE metric
sharpness result. Stages beyond ED4B remain **NOT OPENED** in this roadmap and
are not definitively numbered until a separate architecture increment opens
them.

### Logical firewall

Generic mathematics → algebraic approximation (ED3A–ED4B and T1) → future
explicit dynamics → future algebraic decoherence → future record emergence or
stability → Born-sensitive transfer → conditional decision-theoretic
consequences. Future physical layers use no credence, likelihood, or
rationality axiom. Every `bornRecord` quantity is **BORN-SENSITIVE**; T1 is
**NON BORN-SENSITIVE** and T2 is **BORN-SENSITIVE**. A small profile distance,
small projector displacement, or global projector commutation is not physical
decoherence. Partial traces, channels, and density matrices must distinguish
mathematical identity, dynamical assumption, physical interpretation, and Born
transfer.

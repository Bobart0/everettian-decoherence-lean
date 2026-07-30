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
sans revendication d'optimalité. ED3A est **CLOSED IN ITS FINITE STATEWISE
UNITARY SCOPE** : commutateurs de projecteurs algébriques, défaut statewise
L2, transfert BORN-SENSITIVE vers le profil de record, cas normalisé, et
limite exacte vers `SameRecord` en un état donné. ED3B est **CLOSED IN ITS
FINITE OPERATOR-NORM UNIFORM SCOPE** : version `ContinuousLinearMap` du
commutateur, profil de normes d'opérateur, agrégation L2 uniforme sur les
états pour une perspective et une transformation fixées, contrôle du défaut
statewise, transfert BORN-SENSITIVE uniforme, et limite exacte équivalente à
la commutation globale.

ED4A et ED4B sont **PLANNED / NOT OPENED**. ED4A concernera la composition de
transformations à perspective fixée ; ED4B concernera l'itération finie et
l'accumulation d'erreurs. ED5–ED12 sont **NOT OPENED**. Aucun de ces statuts
ne promet de résultat.

ED1 utilise `bornRecord` et n'est donc pas un critère indépendant de
décohérence ; il en va de même pour tout transfert ED2A–ED3B utilisant
`recordProfileL1` ou `SameRecord`.

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

Les étapes au-delà d'ED4B restent **NOT OPENED** et ne sont pas numérotées de
façon définitive tant qu'un incrément d'architecture séparé ne les ouvre pas.

### Pare-feu logique

Mathématiques génériques → approximation algébrique (ED3A–ED3B) → dynamiques
explicites futures → décohérence algébrique future → émergence ou stabilité
future des records → transfert sensible à Born → conséquences décisionnelles
conditionnelles. Les futures couches physiques n'utilisent pas de crédence,
vraisemblance ou axiome de rationalité. Toute quantité utilisant `bornRecord`
est **BORN-SENSITIVE** ; une faible distance de profils ou une commutation
globale de projecteurs n'est pas une décohérence physique. Trace partielle,
canal ou matrice densité devront distinguer identité mathématique, hypothèse
dynamique, interprétation physique et transfert bornien.

## English

### Current chronology

ED0 is **CLOSED IN BOOTSTRAP SCOPE**. ED1 is **CLOSED IN ITS FINITE KINEMATIC
SCOPE**: generic L1 metric, Born-sensitive profile, zero-distance/`SameRecord`
equivalence, vanishing on the unitary orbit, and `recordProfileWithin`. ED2A
is **CLOSED IN ITS EXPLICIT FINITE SCOPE**: an elementary state-to-record
bound with a cardinality factor. ED2B is **CLOSED IN ITS FINITE
DECOMPOSITION-AWARE SCOPE**: finite Cauchy--Schwarz and the global Pythagorean
identity remove that factor; the normalized version has constant 2, with no
optimality claim. ED3A is **CLOSED IN ITS FINITE STATEWISE UNITARY SCOPE**:
algebraic projector commutators, a statewise L2 defect, BORN-SENSITIVE
transfer to the record profile, a normalized case, and an exact `SameRecord`
limit at a given state. ED3B is **CLOSED IN ITS FINITE OPERATOR-NORM UNIFORM
SCOPE**: the `ContinuousLinearMap` version of the commutator, an operator-norm
profile, an L2 aggregation uniform over states for a fixed perspective and
transformation, control of the statewise defect, a uniform BORN-SENSITIVE
transfer, and an exact limit equivalent to global commutation.

ED4A and ED4B are **PLANNED / NOT OPENED**. ED4A will concern composition of
transformations at a fixed perspective; ED4B will concern finite iteration and
error accumulation. ED5–ED12 are **NOT OPENED**. None of these statuses
promises a result.

ED1 uses `bornRecord` and is therefore not an independent decoherence
criterion; the same holds for every ED2A–ED3B transfer using
`recordProfileL1` or `SameRecord`.

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

Stages beyond ED4B remain **NOT OPENED** and are not definitively numbered
until a separate architecture increment opens them.

### Logical firewall

Generic mathematics → algebraic approximation (ED3A–ED3B) → future explicit
dynamics → future algebraic decoherence → future record emergence or
stability → Born-sensitive transfer → conditional decision-theoretic
consequences. Future physical layers use no credence, likelihood, or
rationality axiom. Every `bornRecord` quantity is **BORN-SENSITIVE**; a small
profile distance or a global projector commutation is not physical
decoherence. Partial traces, channels, and density matrices must distinguish
mathematical identity, dynamical assumption, physical interpretation, and
Born transfer.

# Scientific roadmap

## Français

ED0 est **CLOSED / CLOSED IN BOOTSTRAP SCOPE**. ED1 est **CLOSED IN ITS
FINITE KINEMATIC SCOPE** : métrique L1 générique, profil bornien, équivalence
distance nulle/`SameRecord`, annulation sur orbite unitaire et relation
`recordProfileWithin`. ED1 utilise `bornRecord` et n'est donc pas un
critère indépendant de décohérence.

La chaîne conditionnelle visée est : 1. métriques quantitatives ; 2.
perturbations état→record ; 3. quasi-commutation ; 4. calcul compositionnel
d'erreurs ; 5. factorisation système/environnement typée ; 6. dynamiques ou
canaux explicites ; 7. suppression hors-diagonale ; 8. stabilité et
redondance de records ; 9. transfert vers profils borniens ; 10. transfert
vers poids, espérances et ratios amont avec dénominateurs minorés ; 11.
contre-modèles ; 12. agrégation, audit d'API et release éventuelle.

ED2–ED4 sont **PLANNED / NOT OPENED**. ED5–ED6 sont des cibles
architecturales, ED7–ED10 des cibles scientifiques, ED11 une cible d'audit :
toutes sont **NOT OPENED**. ED12 est **NOT OPENED**. Ces statuts ne promettent
aucun résultat.

### Pare-feu logique

Mathématiques génériques → dynamiques explicites → décohérence algébrique →
émergence ou stabilité des records → transfert sensible à Born → conséquences
décisionnelles conditionnelles. Les futures couches physiques n'utilisent pas
de crédence, vraisemblance ou axiome de rationalité. Toute quantité utilisant
`bornRecord` est **BORN-SENSITIVE** ; une faible distance de profils n'est
pas une décohérence physique. Trace partielle, canal ou matrice densité devront
distinguer identité mathématique, hypothèse dynamique, interprétation physique
et transfert bornien.

## English

ED0 is **CLOSED / CLOSED IN BOOTSTRAP SCOPE**. ED1 is **CLOSED IN ITS FINITE
KINEMATIC SCOPE**: generic L1 metric, Born-sensitive profile, zero
distance/`SameRecord` equivalence, vanishing on the unitary orbit, and
`recordProfileWithin`. Because ED1 uses `bornRecord`, it is not an
independent decoherence criterion.

The conditional target chain is: 1. quantitative metrics; 2. state-to-record
perturbations; 3. approximate commutation; 4. compositional errors; 5. typed
system/environment factorization; 6. explicit dynamics or channels; 7.
off-diagonal suppression; 8. record stability and redundancy; 9. transfer to
Born profiles; 10. transfer to upstream weights, expectations, and ratios with
lower-bounded denominators; 11. countermodels; 12. aggregation, API audit, and
possible release.

ED2–ED4 are **PLANNED / NOT OPENED**; ED5–ED6 architectural targets,
ED7–ED10 scientific targets, and ED11 an audit target are all **NOT OPENED**;
ED12 is **NOT OPENED**. None promises a result.

### ED2A, ED2B, and ED3

ED2A is **CLOSED IN ITS EXPLICIT FINITE SCOPE**. ED2B is **CLOSED IN ITS
FINITE DECOMPOSITION-AWARE SCOPE**: finite Cauchy--Schwarz, the Pythagorean
identity for components, a cell-count-independent bound, and normalized
constant 2 are formalized; no optimality is claimed. ED3 is **PLANNED / NOT
OPENED** and will concern bounded linear or unitary transformations,
commutators with record projectors, an explicitly chosen operator norm, and a
component-variation bound. It will strictly distinguish approximate
commutation from decoherence. ED4–ED12 remain unchanged and not opened.

### Logical firewall

Generic mathematics → explicit dynamics → algebraic decoherence → record
emergence or stability → Born-sensitive transfer → conditional
decision-theoretic consequences. Future physical layers use no credence,
likelihood, or rationality axiom. Every `bornRecord` quantity is
**BORN-SENSITIVE**; small profile distance is not physical decoherence.
Partial traces, channels, and density matrices must distinguish mathematical
identity, dynamical assumption, physical interpretation, and Born transfer.

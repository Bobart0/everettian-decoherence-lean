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

T2 `DimensionFreeSharpness` est **FORMALIZED / AUDITED** et explicitement
**BORN-SENSITIVE**. Le module construit en dimension `2` une famille
rationnelle normalisée issue de la récurrence `(p,q) ↦ (3p+4q, 2p+3q)` avec
invariant `p^2 + 1 = 2 q^2`, calcule exactement le quotient
`recordProfileL1 / ‖x-y‖`, prouve qu'il tend vers `2`, et en déduit que toute
constante universelle `K < 2` échoue sur un membre de la famille. Le module et
son audit ont passé le build Lean, `guard.sh` et `validate.sh`. Aucun statut
**PUBLISHED** n'est revendiqué.

T3 `IterationSharpness` est **FORMALIZED / AUDITED** et explicitement
**NON BORN-SENSITIVE**. Le module construit une famille explicite de listes de
longueur deux `[Uₙ,Uₙ]` sur la perspective binaire fixe. Le défaut élémentaire
L2 vaut exactement `sqrt 2 * sₙ`, le défaut du composé vaut exactement
`sqrt 2 * (2 cₙ sₙ)`, et la somme ED4B vaut `2 * sqrt 2 * sₙ`. Le ratio exact
« défaut composé / somme additive » est donc `cₙ`; la forme rationnelle
`cₙ = 1 - 2/(pₙ^2+1)` donne `cₙ → 1`. Il en résulte que tout coefficient
uniforme `K < 1` devant la somme ED4B est violé par un membre de cette famille,
déjà pour deux transformations. Ce résultat établit la sharpness asymptotique
du coefficient additif `1` dans cette portée finie ; il ne définit ni temps,
ni dynamique physique, ni décohérence. Aucun statut **PUBLISHED** n'est
revendiqué.

T4 `WorkedInstance` est **FORMALIZED / AUDITED**. En dimension `2`, sur la
même perspective binaire fournie, il instancie la rotation rationnelle au rang
`n = 1`, de matrice réelle `[[24/25,-7/25],[7/25,24/25]]`, et l'état normalisé
`e₀`. Le défaut uniforme L2 vaut exactement `7 * sqrt 2 / 25` et admet le
certificat rationnel `≤ 2/5` ; cette partie est **NON BORN-SENSITIVE**. Les
poids borniens calculés passent de `(1,0)` à `(576/625,49/625)`, le profil L1
réel vaut exactement `98/625`, la borne ED3B rationnelle choisie vaut `4/5`,
et le gap correspondant vaut exactement `402/625` ; ces quantités sont
**BORN-SENSITIVE**. L'exemple est numérique et illustratif : il ne constitue
ni une dynamique, ni une décohérence, ni une émergence de perspective. Aucun
statut **PUBLISHED** n'est revendiqué.

T5A `UniformTransferSharpness` est **FORMALIZED / AUDITED / MERGED** et
explicitement **BORN-SENSITIVE**. Sur la famille rationnelle déjà utilisée par
T3, le ratio entre la variation réelle du profil et le défaut uniforme vaut
exactement `sqrt 2`. Toute constante universelle ED3B strictement inférieure
à `sqrt 2` est donc exclue.

T5B `UniformTransferOptimality` est **FORMALIZED / AUDITED / MERGED**. La
géométrie d'un sous-ensemble de cellules et de son complément donne, pour le
projecteur agrégé `P_S`,
`‖[P_S,U]x‖^2 ≤ operatorNormProjectorCommutatorL2 D U ^ 2 * ‖x‖^2 / 2`.
Le transfert BORN-SENSITIVE qui en résulte améliore la constante ED3B de `2`
à `sqrt 2`. Combiné à T5A, il établit exactement
`IsUniversalUniformTransferCoefficient K ↔ Real.sqrt 2 ≤ K`.
La partie commutatoriale de T5B est NON BORN-SENSITIVE ; le transfert de profil
et l'optimalité utilisant T5A sont BORN-SENSITIVE. Aucun statut **PUBLISHED**
n'est revendiqué.

Tx clôt le cycle transversal T0–T5 sur le plan documentaire. Il n'ouvre aucun
T6 et n'ajoute aucun résultat scientifique.

Le front post-T5 de stabilité quantitative est **FORMALIZED / AUDITED** et
**NON BORN-SENSITIVE** sans être renommé T6. Il couvre l'enveloppe des cuts,
la rigidité exacte, la stabilité à deux cellules (constante finie `18`), les
coefficients asymptotiques sharp `8` et `4`, la famille continue `C^3`,
les ingrédients de l'analyse à budget fixé, ainsi que la famille diffuse
géométrique à `2m` cellules et le seuil sharp `1/8`. L'objet order-théorique
unique `C_fix` reste un emballage de manuscrit ; ses mécanismes de preuve
sont formalisés. Ce front n'introduit ni temps, ni dynamique, ni décohérence.

Les jalons **physiques** ED5–ED12 sont **NOT OPENED** dans cette feuille de
route. Les modules de factorisation coordonnée déjà nommés ED5A/ED5B/ED5C
restent des briques typées préparatoires ; leur existence ne constitue pas à
elle seule l'ouverture d'un jalon physique ED5. Aucun de ces statuts ne promet
de résultat physique.

ED1 utilise `bornRecord` et n'est donc pas un critère indépendant de
décohérence ; il en va de même pour tout transfert ED2A–ED4B utilisant
`recordProfileL1` ou `SameRecord`, ainsi que pour T2, la partie profil/gap de
T4 et le transfert T5. Les défauts de commutateur ED3A–ED4B, le contrôle T1,
T3, la partie défaut de T4 et la couche commutatoriale de T5B, qui n'utilisent
pas `bornRecord`, restent des quantités algébriques distinctes des transferts
BORN-SENSITIVE.

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
métrique BORN-SENSITIVE, également transversal. T3 est un résultat de sharpness
algébrique NON BORN-SENSITIVE de la borne d'accumulation ED4B, lui aussi
transversal. T4 est une instance numérique transversale. T5 ferme le problème
de constante uniforme ED3B : T5A fournit la barrière inférieure et T5B la
borne supérieure correspondante. Tx clôt ce cycle transversal sans ouvrir T6.
Les étapes physiques au-delà d'ED4B restent **NOT OPENED** dans cette feuille
de route et ne sont pas numérotées de façon définitive tant qu'un incrément
d'architecture séparé ne les ouvre pas.

### Pare-feu logique

Mathématiques génériques → approximation algébrique (ED3A–ED4B, T1, T3, la
partie défaut de T4 et la couche commutatoriale T5B) → dynamiques explicites
futures → décohérence algébrique future → émergence ou stabilité future des
records → transfert sensible à Born → conséquences décisionnelles
conditionnelles. Les futures couches physiques n'utilisent pas de crédence,
vraisemblance ou axiome de rationalité. Toute quantité utilisant `bornRecord`
est **BORN-SENSITIVE** ; T1 et T3 sont **NON BORN-SENSITIVE**, T2 est
**BORN-SENSITIVE**, T4 sépare défaut et profil, et T5 sépare explicitement la
borne commutatoriale NON BORN-SENSITIVE du transfert/optimalité
BORN-SENSITIVE. Une faible distance de profils, une faible variation de
projecteurs, une quasi-commutation composée presque saturante ou une
commutation globale de projecteurs n'est pas une décohérence physique. Trace
partielle, canal ou matrice densité devront distinguer identité mathématique,
hypothèse dynamique, interprétation physique et transfert bornien.

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

T2 `DimensionFreeSharpness` is **FORMALIZED / AUDITED** and explicitly
**BORN-SENSITIVE**. The module builds, in dimension `2`, a normalized rational
family generated by `(p,q) ↦ (3p+4q, 2p+3q)` with invariant
`p^2 + 1 = 2 q^2`, computes the `recordProfileL1 / ‖x-y‖` ratio exactly, proves
that it tends to `2`, and derives that every universal constant `K < 2` fails
on some family member. The module and its audit have passed the Lean build,
`guard.sh`, and `validate.sh`. No **PUBLISHED** status is claimed.

T3 `IterationSharpness` is **FORMALIZED / AUDITED** and explicitly **NON
BORN-SENSITIVE**. The module constructs an explicit family of length-two lists
`[Uₙ,Uₙ]` on the fixed binary perspective. The elementary L2 defect is exactly
`sqrt 2 * sₙ`, the composite defect is exactly `sqrt 2 * (2 cₙ sₙ)`, and the
ED4B sum is `2 * sqrt 2 * sₙ`. Thus the exact composite/additive-sum ratio is
`cₙ`; the rational form `cₙ = 1 - 2/(pₙ^2+1)` gives `cₙ → 1`. Consequently
every uniform coefficient `K < 1` in front of the ED4B sum is violated by a
member of this family, already for two transformations. This establishes
asymptotic sharpness of the additive coefficient `1` in this finite scope; it
defines neither time, physical dynamics, nor decoherence. No **PUBLISHED**
status is claimed.

T4 `WorkedInstance` is **FORMALIZED / AUDITED**. In dimension `2`, on the same
supplied binary perspective, it instantiates the rational rotation at `n = 1`,
with real matrix `[[24/25,-7/25],[7/25,24/25]]`, and the normalized state `e₀`.
The uniform L2 defect is exactly `7 * sqrt 2 / 25` and has the rational
certificate `≤ 2/5`; this part is **NON BORN-SENSITIVE**. The calculated Born
weights move from `(1,0)` to `(576/625,49/625)`, the actual L1 profile is
exactly `98/625`, the chosen rational ED3B bound is `4/5`, and the resulting
gap is exactly `402/625`; these quantities are **BORN-SENSITIVE**. The example
is numerical and illustrative: it is neither dynamics, decoherence, nor an
emergent perspective. No **PUBLISHED** status is claimed.

T5A `UniformTransferSharpness` is **FORMALIZED / AUDITED / MERGED** and
explicitly **BORN-SENSITIVE**. On the rational family already used by T3, the
ratio of actual profile variation to the uniform defect is exactly `sqrt 2`.
Hence every universal ED3B coefficient strictly below `sqrt 2` is excluded.

T5B `UniformTransferOptimality` is **FORMALIZED / AUDITED / MERGED**.
Subset/complement geometry for the aggregate projector `P_S` yields
`‖[P_S,U]x‖^2 ≤ operatorNormProjectorCommutatorL2 D U ^ 2 * ‖x‖^2 / 2`.
The resulting BORN-SENSITIVE transfer improves the ED3B coefficient from `2`
to `sqrt 2`. Together with T5A it proves exactly
`IsUniversalUniformTransferCoefficient K ↔ Real.sqrt 2 ≤ K`.
The commutator part of T5B is NON BORN-SENSITIVE; the profile transfer and the
optimality argument using T5A are BORN-SENSITIVE. No **PUBLISHED** status is
claimed.

Tx closes the transversal T0–T5 cycle at the documentation level. It opens no
T6 and adds no scientific result.

The post-T5 quantitative-stability front is **FORMALIZED / AUDITED** and
**NON BORN-SENSITIVE** without being renamed T6. It covers the cut envelope,
exact rigidity, two-cell stability (finite coefficient `18`), sharp
asymptotic coefficients `8` and `4`, the continuous `C^3` family, the
fixed-budget proof ingredients, and the geometric diffuse `2m`-cell family
with sharp threshold `1/8`. The single order-theoretic `C_fix` object
remains manuscript packaging while its proof mechanisms are formalized. This
front introduces neither time, dynamics, nor decoherence.

The **physical** ED5–ED12 milestones are **NOT OPENED** in this roadmap.
Coordinate-factorization modules already named ED5A/ED5B/ED5C remain typed
preparatory building blocks; their existence alone does not open an ED5
physical milestone. None of these statuses promises a physical result.

ED1 uses `bornRecord` and is therefore not an independent decoherence
criterion; the same holds for every ED2A–ED4B transfer using
`recordProfileL1` or `SameRecord`, for T2, the profile/gap part of T4, and
the T5 transfer. The ED3A–ED4B commutator defects, T1 control, T3, the defect
part of T4, and the commutator layer of T5B, which do not use `bornRecord`,
remain algebraic quantities distinct from BORN-SENSITIVE transfers.

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
sharpness result. T3 is a transversal NON BORN-SENSITIVE algebraic sharpness
result for the ED4B accumulation bound. T4 is a transversal numerical
instance. T5 closes the ED3B uniform-coefficient problem: T5A supplies the
lower barrier and T5B the matching upper bound. Tx closes this transversal
cycle without opening T6. Physical stages beyond ED4B remain **NOT OPENED**
in this roadmap and are not definitively numbered until a separate
architecture increment opens them.

### Logical firewall

Generic mathematics → algebraic approximation (ED3A–ED4B, T1, T3, the T4
defect part, and the T5B commutator layer) → future explicit dynamics → future
algebraic decoherence → future record emergence or stability → Born-sensitive
transfer → conditional decision-theoretic consequences. Future physical
layers use no credence, likelihood, or rationality axiom. Every `bornRecord`
quantity is **BORN-SENSITIVE**; T1 and T3 are **NON BORN-SENSITIVE**, T2 is
**BORN-SENSITIVE**, T4 separates defect from profile, and T5 explicitly
separates the NON BORN-SENSITIVE commutator bound from the BORN-SENSITIVE
transfer/optimality argument. A small profile
distance, small projector displacement, near-saturation of a composed
commutator bound, or global projector commutation is not physical decoherence.
Partial traces, channels, and density matrices must distinguish mathematical
identity, dynamical assumption, physical interpretation, and Born transfer.

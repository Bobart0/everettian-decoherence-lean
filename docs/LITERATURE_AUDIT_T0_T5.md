# Literature audit — T0–T5 optimal transfer theorem

## Français

Date : **2026-09-18**. Statut : **AUDIT BIBLIOGRAPHIQUE PRÉLIMINAIRE**.

Ce document compare le noyau T5 déjà **FORMALIZED / AUDITED** à des familles
de résultats antérieures proches. Il ne constitue pas une preuve de nouveauté
et n'ajoute aucun résultat Lean.

### 1. Résultat audité

Pour une décomposition projective orthogonale finie $(P_c)_{c\in C}$, une
unitaire $U$ et un état $x$, poser

$$
p_c(x)=\lVert P_cx\rVert^2,
\qquad
\delta(D,U)=
\left(\sum_{c\in C}\lVert P_cU-UP_c\rVert_{\mathrm{op}}^2\right)^{1/2}.
$$

T5B établit

$$
\sum_{c\in C}|p_c(Ux)-p_c(x)|
\le
\sqrt{2}\,\lVert x\rVert^2\,\delta(D,U),
$$

et T5A montre que, sur les états normalisés, la constante universelle
$\sqrt{2}$ est optimale.

La comparaison bibliographique doit donc porter sur le **paquet complet** :

1. PVM finie arbitraire ;
2. variation $L^1$ complète du profil de poids projectifs sous une unitaire ;
3. agrégat $L^2$ des normes d'opérateur des commutateurs cellule par cellule ;
4. coefficient universel exact $\sqrt{2}$ ;
5. famille explicite saturante.

### 2. Antécédents les plus proches identifiés

#### A. Czajkowski–Grilo — presque-commutation sur état

Jan Czajkowski, Alex B. Grilo,
*On-State Commutativity of Measurements and Joint Distributions of Their
Outcomes*, arXiv:2101.08313 (2021).

Leur théorème 7 considère deux projecteurs $P_1,P_2$ et un état
$|\psi\rangle$. Si

$$
\lVert(P_1P_2-P_2P_1)|\psi\rangle\rVert=\varepsilon,
$$

ils construisent un projecteur $P_2'$ tel que $[P_1,P_2']=0$ et

$$
\lVert(P_2'-P_2)|\psi\rangle\rVert\le\sqrt{2}\,\varepsilon.
$$

**Proximité avec T5 : élevée sur la géométrie des projecteurs et la constante
$\sqrt2$, faible sur l'énoncé final.**

Différences : deux projecteurs contre une PVM arbitraire ; norme d'état contre
variation $L^1$ des probabilités ; construction d'un projecteur commutant
contre stabilité d'un profil sous une unitaire ; pas d'agrégat
$\left(\sum_c\lVert[P_c,U]\rVert_{\rm op}^2\right)^{1/2}$.

Conséquence pour le positionnement : **la présence du facteur $\sqrt2$ dans un
problème de presque-commutation de projecteurs n'est pas nouvelle en soi**.

#### B. de la Salle — PVMs presque commutantes

Mikael de la Salle,
*Orthogonalization of Positive Operator Valued Measures*,
Comptes Rendus Mathématique **360** (2022), 549–560,
DOI 10.5802/crmath.326; arXiv:2103.14126.

Un résultat de l'article montre que deux PVMs presque commutantes en norme
dépendant d'un état peuvent être rapprochées d'une paire de PVMs commutantes.
La quantité de départ agrège quadratiquement les commutateurs
$\lVert p_iq_j-q_jp_i\rVert_\varphi$.

**Proximité avec T5 : élevée sur l'agrégation quadratique de commutateurs de
projecteurs, mais objet de sortie différent.**

Différences : deux PVMs et norme $\varphi$ dépendant de l'état ; conclusion
d'orthogonalisation/arrondi vers une PVM commutante ; pas de distance
$L^1$ entre distributions avant/après $U$, pas de coefficient universel
$\sqrt2$ pour cette distance.

#### C. Ozawa — disturbance comme somme quadratique de commutateurs

Masanao Ozawa,
*Universal Uncertainty Principle in the Measurement Operator Formalism*,
Journal of Optics B **7** (2005), S672–S681,
DOI 10.1088/1464-4266/7/12/033; arXiv:quant-ph/0510083.

Dans le formalisme des opérateurs de mesure, la disturbance rms d'un observable
$B$ peut s'écrire sous la forme

$$
\eta(B)^2=\sum_m\lVert[M_m,B]|\psi\rangle\rVert^2.
$$

Pour certains observables de Pauli et une mesure projective, un facteur
$\sqrt2$ apparaît également.

**Proximité avec T5 : élevée sur la structure “somme de carrés de
commutateurs”, moyenne sur l'interprétation.**

Différences : disturbance d'un observable causée par une mesure, commutateurs
appliqués à l'état, et non normes d'opérateur par cellule ; pas de variation
$L^1$ du profil de la même PVM sous une unitaire ; pas du même théorème de
meilleure constante.

#### D. Sendall — dérive probabiliste contrôlée par un commutateur

Jonathon Sendall,
*The Beta-Bound: Drift constraints for Gated Quantum Probabilities*,
arXiv:2601.22188 (2026).

Pour un état $\rho$, un projecteur de gate $F$, un effet $E$, une probabilité
de passage $s=\operatorname{Tr}(\rho F)$ et
$\varepsilon=\lVert[F,E]\rVert$, la dérive conditionnelle considérée satisfait

$$
|\Delta p_F(E)|
\le 2\sqrt{\frac{1-s}{s}}\,\varepsilon,
$$

avec constante $2$ sharp dans ce cadre.

**Proximité avec T5 : élevée sur l'idée “dérive de probabilité contrôlée par
non-commutation”, faible sur la géométrie exacte.**

Différences : gate unique + effet ; conditionnement et facteur dépendant de
$s$ ; pas de PVM complète, pas d'agrégat $L^2$ des commutateurs, constante et
quantité probabiliste différentes.

#### E. Zhou–Wu–Chau — disturbance statistique entre distributions

S. S. Zhou, S. Wu, H. F. Chau,
*State-independent error-disturbance trade-off for measurement operators*,
Physics Letters A **380** (2016), 1918–1924,
DOI 10.1016/j.physleta.2016.03.046; arXiv:1509.03812.

Les auteurs définissent une disturbance via la distinguabilité de
distributions classiques obtenues par une mesure seule ou par une succession
de mesures incompatibles.

**Proximité avec T5 : élevée sur le choix d'une distance entre statistiques,
faible sur la borne commutatoriale.**

Aucun équivalent direct de l'agrégat T5 ni de la constante optimale $\sqrt2$
n'a été identifié dans ce travail lors de cet audit préliminaire.

#### F. Conde et littérature sur deux projections

Cristian Conde,
*A note about the norm of the sum and the anticommutator of two orthogonal
projections*, Journal of Mathematical Analysis and Applications **505**
(2022), 125650, DOI 10.1016/j.jmaa.2021.125650.

Cette littérature établit des identités et bornes précises pour
$\lVert[P,Q]\rVert$ entre deux projections orthogonales, notamment la borne
universelle classique $\lVert[P,Q]\rVert\le 1/2$.

**Proximité avec T5 : composante opératorielle locale pertinente, mais pas de
profil probabiliste multi-cellule.**

#### G. Hastings — matrices presque commutantes

M. B. Hastings,
*Making Almost Commuting Matrices Commute*,
Communications in Mathematical Physics **291** (2009), 321–345,
DOI 10.1007/s00220-009-0877-2; arXiv:0808.2474.

Le problème traité est l'approximation de matrices presque commutantes par des
matrices exactement commutantes, avec contrôle quantitatif indépendant de la
dimension.

**Proximité avec T5 : arrière-plan conceptuel**, mais ni la quantité de sortie
ni la meilleure constante T5 ne coïncident.

#### H. Kittaneh — commutateur et conjugaison unitaire

Fuad Kittaneh,
*Commutator inequalities associated with the polar decomposition*,
Proceedings of the American Mathematical Society **130**(5) (2002),
1279–1283, DOI 10.1090/S0002-9939-01-06197-4.

Pour un opérateur positif (P) et une unitaire (U), ce travail étudie
quantitativement le commutateur (UP-PU) et les objets de conjugaison unitaire
associés, dans des normes unitairement invariantes.

Dans le cas particulier où (P) est un projecteur, l'identité algébrique
élémentaire

[
[P,U]U^ast=P-UPU^ast
]

donne immédiatement

[
lVert[P,U]Vert_{mathrm{op}}
=
lVert P-UPU^astVert_{mathrm{op}}.
]

**Proximité avec T5 : très élevée pour la géométrie opératorielle locale du
projecteur agrégé (P_S), mais pas pour la statistique multi-cellule.**

Cela renforce le risque que la brique locale « commutateur d'un projecteur
agrégé versus déplacement de ce projecteur par conjugaison » soit standard.
L'élément potentiellement distinct de T5 doit donc être recherché dans le
passage depuis les commutateurs cellule par cellule vers (P_S), puis vers la
variation (L^1) complète du profil, avec constante universelle optimale et
famille saturante.

### 3. Résultat standard à ne pas confondre avec T5

Pour une mesure fixée, la distance de variation totale entre les distributions
obtenues sur deux états est dominée par leur distance de trace. C'est un fait
standard de distinguishabilité quantique.

Ce résultat ne subsume pas immédiatement T5 : une unitaire peut modifier
fortement l'état à l'intérieur de chaque cellule tout en commutant avec tous les
$P_c$, auquel cas $\delta(D,U)=0$ et le profil projectif reste exactement
inchangé. T5 exploite donc la **structure relative à la décomposition** plutôt
qu'une simple distance globale entre $x$ et $Ux$.

### 4. Risques d'antériorité

#### Risque R1 — le lemme agrégé peut être connu sous une autre forme

Le cœur T5B passe du sous-ensemble de variation positive $S$ au projecteur
agrégé $P_S$, puis utilise la géométrie des blocs croisés de $[P_S,U]$.
Des résultats très proches peuvent être cachés dans la littérature sur :

- paires de projections et angles principaux ;
- pinching/dephasing et conditional expectations ;
- almost commuting PVMs ;
- gentle measurement / disturbance ;
- operator-space norm inequalities.

**R1 reste ouvert.**

#### Risque R2 — combinaison de lemmes standards

Même si l'énoncé complet n'est pas publié explicitement, un referee peut
considérer que la preuve combine des outils standards : identité de variation
totale, agrégation de projecteurs, décomposition orthogonale des blocs et
Cauchy–Schwarz/Pythagore.

Le caractère publiable dépend donc non seulement de “personne n'a écrit la
même formule”, mais de la valeur ajoutée du **best-constant theorem**, de la
famille saturante, de l'extension composition/itération et de la formalisation
Lean.

#### Risque R3 — la constante $\sqrt2$ n'est pas un marqueur de nouveauté

Czajkowski–Grilo et Ozawa donnent déjà des $\sqrt2$ dans des problèmes
commutatoriaux de mesure différents. La revendication éventuelle devra porter
sur l'**inégalité précise et sa constante optimale dans la métrique T5**, pas
sur le nombre $\sqrt2$ lui-même.

### 5. Matrice de comparaison

| Travail | Entrée de non-commutation | Sortie contrôlée | Agrégation | Constante sharp | Équivalent T5 ? |
|---|---|---|---|---|---|
| T5A/T5B | $\lVert[P_c,U]\rVert_{\rm op}$ | $L^1$ du profil projectif | $L^2$ sur $c$ | $\sqrt2$ | référence |
| Czajkowski–Grilo 2021 | $\lVert[P_1,P_2]\psi\rVert$ | distance sur état à un projecteur commutant | aucune PVM complète | $\sqrt2$ comme borne | non identifié |
| de la Salle 2022 | commutateurs de deux PVMs en norme $\varphi$ | distance à une PVM commutante | quadratique | ordre linéaire optimal | non |
| Ozawa 2005 | $[M_m,B]\psi$ | disturbance rms de $B$ | quadratique sur $m$ | cas $\sqrt2$ particuliers | non |
| Sendall 2026 | $\lVert[F,E]\rVert$ | dérive probabiliste conditionnelle | un gate/un effet | $2$ sharp | non |
| Zhou–Wu–Chau 2016 | incompatibilité de mesures | distance entre distributions successives | selon mesure | autre trade-off | non identifié |
| Conde 2022 | $[P,Q]$ | normes opératorielles de deux projections | aucune | bornes exactes/locales | non |
| Hastings 2009 | $[A,B]$ | distance à des matrices commutantes | deux opérateurs | quantitative | non |
| Kittaneh 2002 | $UP-PU$ / conjugaison unitaire | inégalités de normes opératorielles | un opérateur positif + unitaire | sharpness locale selon inégalité | non, mais brique locale proche |

### 6. Conclusion provisoire

**NOVELTY STATUS: UNRESOLVED, WITH NO EXACT ANTECEDENT IDENTIFIED IN THIS
PRELIMINARY AUDIT.**

Ce statut signifie exactement :

- plusieurs antécédents structurels importants existent ;
- aucun des travaux examinés ci-dessus n'énonce manifestement le paquet T5
  complet ;
- l'absence actuelle de match exact ne suffit pas à établir la nouveauté.

Le prochain audit doit cibler prioritairement la littérature d'analyse
fonctionnelle et d'algèbres d'opérateurs sur les PVMs, pinching maps,
conditional expectations et matrices bloc, où un théorème équivalent pourrait
être formulé sans vocabulaire de probabilités quantiques.

### 7. Critère avant soumission

Avant toute revendication de nouveau théorème, il faut au minimum :

1. rechercher un équivalent du lemme de projecteur agrégé pour $[P_S,U]$ ;
2. rechercher explicitement des bornes de variation totale des statistiques
   d'une PVM en fonction de commutateurs ;
3. remonter les références citées par Kittaneh, Conde, Hastings, de la Salle
   et Czajkowski–Grilo ;
4. vérifier si la constante $\sqrt2$ peut être obtenue comme corollaire direct
   d'un théorème général déjà publié ;
5. documenter la différence exacte si un résultat plus général est trouvé.

Aucun passage de **UNRESOLVED** à **NOVEL** ne doit être fait sans cet audit.

## English

Date: **2026-09-18**. Status: **PRELIMINARY LITERATURE AUDIT**.

This document compares the already **FORMALIZED / AUDITED** T5 nucleus with
nearby prior result families. It is not evidence of novelty and adds no Lean
result.

### 1. Audited theorem

For a finite orthogonal projective decomposition $(P_c)_{c\in C}$, unitary
$U$, and state $x$, define

$$
p_c(x)=\lVert P_cx\rVert^2,
\qquad
\delta(D,U)=
\left(\sum_{c\in C}\lVert P_cU-UP_c\rVert_{\mathrm{op}}^2\right)^{1/2}.
$$

T5B proves

$$
\sum_{c\in C}|p_c(Ux)-p_c(x)|
\le
\sqrt{2}\,\lVert x\rVert^2\,\delta(D,U),
$$

and T5A proves that on normalized states the universal coefficient
$\sqrt{2}$ is optimal.

The literature comparison must therefore target the **whole package**:
arbitrary finite PVM, full $L^1$ profile change, $L^2$ aggregate of per-cell
operator commutator norms, exact universal coefficient $\sqrt2$, and an
explicit saturating family.

### 2. Closest identified antecedents

#### A. Czajkowski–Grilo — on-state almost commutation

Jan Czajkowski, Alex B. Grilo,
*On-State Commutativity of Measurements and Joint Distributions of Their
Outcomes*, arXiv:2101.08313 (2021).

Their theorem 7 starts from
$\lVert(P_1P_2-P_2P_1)|\psi\rangle\rVert=\varepsilon$ and constructs a
projector $P_2'$ commuting with $P_1$ such that

$$
\lVert(P_2'-P_2)|\psi\rangle\rVert\le\sqrt2\,\varepsilon.
$$

This is close in projector geometry and in the appearance of $\sqrt2$, but it
does not control the $L^1$ probability profile of an arbitrary PVM under a
unitary and uses no T5 operator-norm aggregate.

Accordingly, the occurrence of $\sqrt2$ in an almost-commuting-projector
problem is **not itself novel**.

#### B. de la Salle — almost commuting PVMs

Mikael de la Salle,
*Orthogonalization of Positive Operator Valued Measures*,
Comptes Rendus Mathématique **360** (2022), 549–560,
DOI 10.5802/crmath.326; arXiv:2103.14126.

The paper includes a quantitative result taking two PVMs that almost commute in
a state-dependent norm and producing a nearby commuting PVM. Its hypothesis
quadratically aggregates commutators. The target and norms nevertheless differ
from T5, and no full pre/post-unitary $L^1$ profile bound with the T5 aggregate
was identified.

#### C. Ozawa — rms disturbance as a quadratic commutator sum

Masanao Ozawa,
*Universal Uncertainty Principle in the Measurement Operator Formalism*,
Journal of Optics B **7** (2005), S672–S681,
DOI 10.1088/1464-4266/7/12/033; arXiv:quant-ph/0510083.

Measurement disturbance can be written in the form

$$
\eta(B)^2=\sum_m\lVert[M_m,B]|\psi\rangle\rVert^2.
$$

This is structurally close to a quadratic aggregation of commutators, and
$\sqrt2$ also occurs in particular Pauli-projective cases. The controlled
quantity, norm placement, and measurement scenario are different from T5.

#### D. Sendall — commutator-controlled probability drift

Jonathon Sendall,
*The Beta-Bound: Drift constraints for Gated Quantum Probabilities*,
arXiv:2601.22188 (2026).

For a density operator $\rho$, gate projector $F$, effect $E$,
$s=\operatorname{Tr}(\rho F)$, and
$\varepsilon=\lVert[F,E]\rVert$, the paper proves a sharp conditional drift
bound

$$
|\Delta p_F(E)|
\le 2\sqrt{\frac{1-s}{s}}\,\varepsilon.
$$

This is close in theme but differs in conditioning, state dependence, number of
effects, aggregation, and constant.

#### E. Zhou–Wu–Chau — distributional measurement disturbance

S. S. Zhou, S. Wu, H. F. Chau,
*State-independent error-disturbance trade-off for measurement operators*,
Physics Letters A **380** (2016), 1918–1924,
DOI 10.1016/j.physleta.2016.03.046; arXiv:1509.03812.

They quantify disturbance through distinguishability of classical outcome
distributions produced by a single measurement versus a sequence of
incompatible measurements. No direct equivalent of the T5 commutator
aggregate or optimal $\sqrt2$ coefficient was identified in this preliminary
audit.

#### F. Conde and two-projection norm inequalities

Cristian Conde,
*A note about the norm of the sum and the anticommutator of two orthogonal
projections*, Journal of Mathematical Analysis and Applications **505**
(2022), 125650, DOI 10.1016/j.jmaa.2021.125650.

This line gives exact identities and sharp bounds for operator norms associated
with two projections, including the classical universal
$\lVert[P,Q]\rVert\le1/2$. It is directly relevant to the local operator
geometry but does not state a multi-cell probability-profile theorem.

#### G. Hastings — almost commuting matrices

M. B. Hastings,
*Making Almost Commuting Matrices Commute*,
Communications in Mathematical Physics **291** (2009), 321–345,
DOI 10.1007/s00220-009-0877-2; arXiv:0808.2474.

This is important conceptual background for quantitative almost-commutation,
but its target is approximation by commuting operators rather than T5 profile
stability.

#### H. Kittaneh — commutator and unitary conjugation

Fuad Kittaneh,
*Commutator inequalities associated with the polar decomposition*,
Proceedings of the American Mathematical Society **130**(5) (2002),
1279–1283, DOI 10.1090/S0002-9939-01-06197-4.

For a positive operator (P) and a unitary (U), this paper quantitatively
studies the commutator (UP-PU) and associated unitary-conjugation objects
under unitarily invariant norms.

When (P) is a projection, the elementary algebraic identity

[
[P,U]U^ast=P-UPU^ast
]

immediately gives

[
lVert[P,U]Vert_{mathrm{op}}
=
lVert P-UPU^astVert_{mathrm{op}}.
]

**Proximity to T5: very high for the local operator geometry of the aggregate
projector (P_S), but not for the multicell statistical statement.**

This increases the risk that the local step relating an aggregate-projector
commutator to unitary displacement is standard. The potentially distinctive
part of T5 must therefore be sought in the passage from per-cell commutators to
(P_S), then to the full (L^1) profile variation, with an optimal universal
constant and an explicit saturating family.

### 3. Standard measurement-contraction bound is not T5

For a fixed measurement, total variation distance between outcome
distributions is bounded by trace distance of the underlying states. This
standard distinguishability fact does not directly subsume T5: a unitary can
move a state substantially within each projective cell while commuting with
every $P_c$, in which case $\delta(D,U)=0$ and the projective profile remains
exactly unchanged.

T5 therefore exploits geometry **relative to the projective decomposition**,
rather than merely global state distance.

### 4. Prior-art risks

**R1 — aggregate-projector lemma may already exist under operator-algebra
language.** The identity
(lVert[P,U]Vert_{m op}=lVert P-UPU^astVert_{m op}) places the
local (P_S) step directly inside classical projection/unitary-conjugation
geometry; Kittaneh's commutator inequalities reinforce this point. The
positive-variation subset, aggregation from the cellwise (L^2) budget,
cross-block decomposition, and sharp factor (1/2) must therefore be checked
against work on pairs of projections, pinching, conditional expectations, and
block operator matrices.

**R2 — combination-of-standard-lemmas risk.** Even absent an identical printed
statement, a referee may regard the proof as a short combination of standard
total-variation and projection-geometry facts. Publication value must therefore
rest on the best-constant theorem, explicit saturation, composition/iteration
package, and verified formalization rather than formula novelty alone.

**R3 — $\sqrt2$ is not a novelty marker.** The same numerical factor appears
in distinct projector-commutation and measurement-disturbance problems.
Any future claim must concern the precise T5 inequality and its optimality.

### 5. Comparison matrix

| Work | Noncommutation input | Controlled output | Aggregation | Sharp constant | Identified as T5-equivalent? |
|---|---|---|---|---|---|
| T5A/T5B | $\lVert[P_c,U]\rVert_{\rm op}$ | full projective-profile $L^1$ | $L^2$ over cells | $\sqrt2$ | reference |
| Czajkowski–Grilo 2021 | $\lVert[P_1,P_2]\psi\rVert$ | state-distance to commuting projector | two projections | $\sqrt2$ bound | no |
| de la Salle 2022 | state-norm commutators of two PVMs | nearby commuting PVM | quadratic | optimal linear order | no |
| Ozawa 2005 | $[M_m,B]\psi$ | rms observable disturbance | quadratic over outcomes | $\sqrt2$ in special cases | no |
| Sendall 2026 | $\lVert[F,E]\rVert$ | conditional probability drift | one gate/effect | $2$ sharp | no |
| Zhou–Wu–Chau 2016 | incompatible measurements | statistical distribution disturbance | measurement dependent | different trade-off | no identified match |
| Conde 2022 | $[P,Q]$ | two-projection operator norms | none | sharp local bounds | no |
| Hastings 2009 | $[A,B]$ | distance to commuting matrices | two operators | quantitative | no |
| Kittaneh 2002 | $UP-PU$ / unitary conjugation | operator-norm inequalities | positive operator + unitary | inequality-dependent local sharpness | no, but close local ingredient |

### 6. Provisional conclusion

**NOVELTY STATUS: UNRESOLVED, WITH NO EXACT ANTECEDENT IDENTIFIED IN THIS
PRELIMINARY AUDIT.**

This means only that important structural antecedents exist and that none of
the works inspected above manifestly states the entire T5 package. It is not a
novelty certificate.

The highest-priority remaining search is operator-analysis literature on PVMs,
pinching/dephasing maps, conditional expectations, block matrices, and
projection angles, where the result could be formulated without quantum
probability language.

### 7. Gate before submission

Before any new-theorem claim:

1. search for an equivalent aggregate-projector commutator lemma;
2. search explicitly for total-variation bounds on PVM statistics in terms of
   commutators;
3. follow backward citations from Kittaneh, Conde, Hastings, de la Salle, and
   Czajkowski–Grilo;
4. test whether $\sqrt2$ follows immediately from a more general published
   operator inequality;
5. if a more general theorem is found, state precisely what remains new:
   formulation, sharpness family, Lean formalization, composition results, or
   another corollary.

No transition from **UNRESOLVED** to **NOVEL** is justified before that work.

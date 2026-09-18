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

Pour un opérateur positif $P$ et une unitaire $U$, ce travail étudie
quantitativement le commutateur $UP-PU$ et les objets de conjugaison unitaire
associés, dans des normes unitairement invariantes.

Dans le cas particulier où $P$ est un projecteur, l'identité algébrique
élémentaire

$
[P,U]U^\ast=P-UPU^\ast
$

donne immédiatement

$
\lVert[P,U]\rVert_{\mathrm{op}}
=
\lVert P-UPU^\ast\rVert_{\mathrm{op}}.
$

**Proximité avec T5 : très élevée pour la géométrie opératorielle locale du
projecteur agrégé $P_S$, mais pas pour la statistique multi-cellule.**

Cela renforce le risque que la brique locale « commutateur d'un projecteur
agrégé versus déplacement de ce projecteur par conjugaison » soit standard.
L'élément potentiellement distinct de T5 doit donc être recherché dans le
passage depuis les commutateurs cellule par cellule vers $P_S$, puis vers la
variation $L^1$ complète du profil, avec constante universelle optimale et
famille saturante.

#### I. Halmos — forme canonique de deux projections

Paul R. Halmos,
*Two Subspaces*, Transactions of the American Mathematical Society **144**
(1969), 381–389.

La théorie classique de deux sous-espaces réduit, sur la partie en position
générique, une paire de projecteurs orthogonaux à la forme bloc

$
P \simeq
\begin{pmatrix} I&0\\0&0\end{pmatrix},
\qquad
Q \simeq
\begin{pmatrix} C^2&CS\\CS&S^2\end{pmatrix},
\qquad C^2+S^2=I,
$

avec $C$ et $S$ contractions positives commutantes.

Conde 2022 réutilise cette géométrie de deux projections et décompose notamment
$P-Q$ à l'aide des deux blocs croisés
$P(I-Q)$ et $(I-P)Q$, dont les images sont orthogonales.

**Conséquence pour T5 : la réduction locale à deux blocs et le fait que les
extrémaux puissent déjà apparaître en dimension $2$ ne doivent pas être
présentés comme nouveaux.** Le contenu éventuellement distinct doit être
cherché dans la manière dont une PVM entière fournit simultanément le budget
cellulaire, dans la sélection du sous-ensemble de variation positive, et dans
le théorème global de meilleure constante.

#### J. Rieffel / Arveson — distance à une sous-algèbre et projections du commutant

Marc A. Rieffel,
*Quantum Hamming Metrics*, arXiv:2507.23046 (2025), théorème 12.1,
s'appuie sur la norme quotient
\[
L_q(a)=\operatorname{dist}(a,\mathcal B)
\]
pour une sous-algèbre unitaire \(\mathcal B\subseteq B(H)\) en dimension
finie. Le théorème représente cette distance par le supremum des
\(\lVert[P,a]\rVert\) lorsque \(P\) parcourt certaines projections du commutant
\(\mathcal B'\). Rieffel relie explicitement ce résultat à Christensen (1977)
et à la formule de distance d'Arveson (1975).

Appliquons extérieurement ce cadre à la sous-algèbre bloc-diagonale associée à
la PVM \(D\),
\[
\mathcal B_D
=
\{T:[T,P_c]=0\ \text{pour tout }c\}
\simeq \bigoplus_c B(P_cH).
\]
Son commutant est l'algèbre des scalaires par bloc,
\[
\mathcal B_D'=\left\{\sum_c\lambda_cP_c\right\},
\]
et ses projections sont exactement les projecteurs agrégés
\(P_S=\sum_{c\in S}P_c\). Dans le cadre fini à blocs non nuls, la restriction
de rang du théorème 12.1 est automatique puisque, si \(r_c=\operatorname{rank}
P_c\),
\[
\dim\mathcal B_D=\sum_c r_c^2\ge\sum_c r_c=\dim H.
\]
On obtient donc la reformulation externe
\[
\operatorname{dist}(U,\mathcal B_D)
=
\sup_S\lVert[P_S,U]\rVert_{\mathrm{op}}.
\]

**Statut dans ce dépôt : OBSERVATION EXTERNE / NON FORMALISÉE EN LEAN sous
cette forme.** Elle ne change aucun statut de T5.

En prenant le supremum sur les vecteurs unitaires dans la borne T5B déjà
formalisée pour chaque \(S\), on obtient mathématiquement
\[
\operatorname{dist}(U,\mathcal B_D)
\le
\frac1{\sqrt2}
\left(\sum_c\lVert[P_c,U]\rVert_{\mathrm{op}}^2\right)^{1/2}.
\]
Dans une décomposition binaire \(P_1=I-P_0\),
\([P_1,U]=-[P_0,U]\), donc le rapport entre le membre de gauche exprimé par le
supremum des projecteurs agrégés et l'agrégat \(L^2\) vaut exactement
\(1/\sqrt2\) dès que le commutateur est non nul. La constante opératorielle
\(1/\sqrt2\) est ainsi naturellement sharp dans ce cadre.

**Conséquence pour la nouveauté : très importante.** La formule de distance
montre que le supremum sur les projecteurs agrégés n'est pas en lui-même un
nouvel objet. Le front bibliographique pertinent se réduit désormais à
l'inégalité sharp qui compare cette distance quotient à l'agrégat \(L^2\) des
commutateurs atomiques \( [P_c,U] \), puis au corollaire de variation totale
des poids projectifs.

#### K. Row/column operators — la borne multi-cellule comme inégalité bloc standard

La borne multi-cellule de T5B admet une lecture élémentaire en opérateurs-lignes
et opérateurs-colonnes. Pour un sous-ensemble \(S\subseteq C\), l'opérateur

\[
P_SU P_{S^c}
\]

est l'opérateur-ligne formé des blocs \(P_cUP_{S^c}\), \(c\in S\). Comme les
espaces de sortie \(P_cH\) sont orthogonaux,

\[
\lVert P_SU P_{S^c}\rVert_{\mathrm{op}}^2
=
\left\|
\sum_{c\in S}
(P_cUP_{S^c})^\ast(P_cUP_{S^c})
\right\|_{\mathrm{op}}
\le
\sum_{c\in S}\lVert P_cUP_{S^c}\rVert_{\mathrm{op}}^2.
\]

Or chaque bloc vérifie

\[
\lVert P_cUP_{S^c}\rVert_{\mathrm{op}}
\le
\lVert[P_c,U]\rVert_{\mathrm{op}}.
\]

Le même argument côté complément donne

\[
\lVert[P_S,U]\rVert_{\mathrm{op}}^2
\le
\min\!\left(
\sum_{c\in S}\lVert[P_c,U]\rVert_{\mathrm{op}}^2,\,
\sum_{c\notin S}\lVert[P_c,U]\rVert_{\mathrm{op}}^2
\right).
\]

Comme les deux sommes partitionnent le budget global,

\[
\lVert[P_S,U]\rVert_{\mathrm{op}}^2
\le
\frac12
\sum_c\lVert[P_c,U]\rVert_{\mathrm{op}}^2.
\]

Cette dérivation est essentiellement une application de la formule standard de
norme pour un row/column operator, suivie de
\(\min(A,B)\le(A+B)/2\).

**Conséquence pour la nouveauté : majeure.** Le facteur \(1/2\) de la borne
quadratique T5B ne repose pas sur une nouvelle théorie opératorielle profonde ;
il résulte d'une combinaison courte de faits standards une fois le bon
projecteur agrégé \(P_S\) choisi. La valeur scientifique éventuelle de T5 doit
donc être cherchée dans le paquet complet : identification du \(S\) de variation
positive, passage exact à la variation \(L^1\), constante universelle optimale,
famille saturante, composition/itération et formalisation Lean.

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

L'identité
$\lVert[P,U]\rVert_{\mathrm{op}}=\lVert P-UPU^\ast\rVert_{\mathrm{op}}$
place la brique locale de $P_S$ directement dans la géométrie classique des
projecteurs et de la conjugaison unitaire ; les inégalités de Kittaneh
renforcent ce point. Le risque d'antériorité porte donc surtout sur les étapes
suivantes : construction du sous-ensemble de variation positive, agrégation du
budget $L^2$ cellule par cellule, décomposition en blocs croisés et facteur
quadratique sharp $1/2$.

Des résultats très proches peuvent être cachés dans la littérature sur :

- paires de projections et angles principaux ;
- pinching/dephasing et conditional expectations ;
- almost commuting PVMs ;
- gentle measurement / disturbance ;
- block operator matrices et operator-space norm inequalities.

**R1 reste ouvert.**

#### Risque R2 — combinaison de lemmes standards

Ce risque est désormais **élevé**. La partie opératorielle multi-cellule se
réduit à une estimation standard de row/column operator, à la partition
(S/S^c) et à (min(A,B)le(A+B)/2). Même si l'énoncé complet n'est pas
publié explicitement, un referee peut considérer la preuve principale comme
une combinaison courte de faits standards.

Le caractère publiable dépend donc moins de la nouveauté technique de la preuve
que de la valeur ajoutée du **best-constant theorem** dans cette métrique
précise, de la famille saturante, du paquet composition/itération et de la
formalisation Lean.

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
| Halmos 1969 | paire de projections | forme canonique en blocs | réduction à deux blocs | structure exacte | non, mais géométrie locale fondamentale |
| Rieffel 2025 / Arveson | distance à (mathcal B_D) | supremum de commutateurs avec projections du commutant | tous les (P_S) | formule de distance exacte | non, mais reformule le côté gauche opératoriel |

### 6. Conclusion provisoire

**NOVELTY STATUS: UNRESOLVED; EXACT ANTECEDENT NOT IDENTIFIED, BUT
STANDARD-LEMMA RISK IS HIGH.**

Ce statut signifie exactement :

- plusieurs antécédents structurels importants existent ;
- aucun des travaux examinés ci-dessus n'énonce manifestement le paquet T5
  complet ;
- l'absence actuelle de match exact ne suffit pas à établir la nouveauté.

L'audit réduit maintenant fortement la zone d'incertitude : la géométrie
locale de deux projections est classique (Halmos, Kittaneh, Conde), et le
supremum sur les projecteurs agrégés a une interprétation standard de distance
à la sous-algèbre bloc-diagonale (Rieffel/Arveson). Le prochain audit doit donc
cibler presque exclusivement la comparaison **multi-cellules**
[
operatorname{dist}(U,mathcal B_D)
stackrel{?}{le}
rac1{sqrt2}
left(sum_clVert[P_c,U]Vert_{mathrm{op}}^2ight)^{1/2},
]
sa meilleure constante, et le passage de cette inégalité à la variation totale
du profil projectif.

### 7. Critère avant soumission

Avant toute revendication de nouveau théorème, il faut au minimum :

1. rechercher explicitement la comparaison entre distance à l'algèbre
   bloc-diagonale et norme (L^2) de la famille des commutateurs atomiques ;
2. rechercher des bornes de variation totale des statistiques d'une PVM en
   fonction de cette distance quotient ou des commutateurs ;
3. remonter les références citées par Halmos, Kittaneh, Conde, Hastings,
   de la Salle et Czajkowski–Grilo ;
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

For a positive operator $P$ and a unitary $U$, this paper quantitatively
studies the commutator $UP-PU$ and associated unitary-conjugation objects
under unitarily invariant norms.

When $P$ is a projection, the elementary algebraic identity

$
[P,U]U^\ast=P-UPU^\ast
$

immediately gives

$
\lVert[P,U]\rVert_{\mathrm{op}}
=
\lVert P-UPU^\ast\rVert_{\mathrm{op}}.
$

**Proximity to T5: very high for the local operator geometry of the aggregate
projector $P_S$, but not for the multicell statistical statement.**

This increases the risk that the local step relating an aggregate-projector
commutator to unitary displacement is standard. The potentially distinctive
part of T5 must therefore be sought in the passage from per-cell commutators to
$P_S$, then to the full $L^1$ profile variation, with an optimal universal
constant and an explicit saturating family.

#### I. Halmos — canonical form for two projections

Paul R. Halmos,
*Two Subspaces*, Transactions of the American Mathematical Society **144**
(1969), 381–389.

The classical two-subspace theory reduces a pair of orthogonal projections, on
their generic-position component, to the block form

$
P \simeq
\begin{pmatrix} I&0\\0&0\end{pmatrix},
\qquad
Q \simeq
\begin{pmatrix} C^2&CS\\CS&S^2\end{pmatrix},
\qquad C^2+S^2=I,
$

with commuting positive contractions $C$ and $S$.

Conde 2022 uses this two-projection geometry and in particular decomposes
$P-Q$ through the two cross blocks $P(I-Q)$ and $(I-P)Q$, whose ranges are
orthogonal.

**Consequence for T5: the local two-block reduction and the fact that
extremizers may already occur in dimension $2$ should not be presented as
new.** Any potentially distinctive content must instead lie in how the whole
PVM supplies the simultaneous cellwise budget, in the positive-variation
subset selection, and in the global best-constant theorem.

#### J. Rieffel / Arveson — distance to a subalgebra and commutant projections

Marc A. Rieffel,
*Quantum Hamming Metrics*, arXiv:2507.23046 (2025), Theorem 12.1,
uses the quotient norm
\[
L_q(a)=\operatorname{dist}(a,\mathcal B)
\]
for a unital subalgebra \(\mathcal B\subseteq B(H)\) in finite dimension. The
theorem represents this distance through the supremum of
\(\lVert[P,a]\rVert\) over suitable projections \(P\) in the commutant
\(\mathcal B'\). Rieffel explicitly relates the theorem to Christensen (1977)
and the Arveson distance formula (1975).

Apply this framework externally to the block-diagonal algebra associated with
the PVM \(D\),
\[
\mathcal B_D
=
\{T:[T,P_c]=0\ \text{for every }c\}
\simeq \bigoplus_c B(P_cH).
\]
Its commutant is the block-scalar algebra
\[
\mathcal B_D'=\left\{\sum_c\lambda_cP_c\right\},
\]
whose projections are exactly the aggregate projectors
\(P_S=\sum_{c\in S}P_c\). In the finite nonzero-block setting, the rank
restriction in Theorem 12.1 is automatic: with
\(r_c=\operatorname{rank}P_c\),
\[
\dim\mathcal B_D=\sum_c r_c^2\ge\sum_c r_c=\dim H.
\]
Thus the external reformulation is
\[
\operatorname{dist}(U,\mathcal B_D)
=
\sup_S\lVert[P_S,U]\rVert_{\mathrm{op}}.
\]

**Repository status: EXTERNAL OBSERVATION / NOT FORMALIZED IN LEAN in this
form.** It changes no T5 status.

Taking the supremum over unit vectors in the already formalized T5B estimate
for every \(S\) gives mathematically
\[
\operatorname{dist}(U,\mathcal B_D)
\le
\frac1{\sqrt2}
\left(\sum_c\lVert[P_c,U]\rVert_{\mathrm{op}}^2\right)^{1/2}.
\]
For a binary decomposition \(P_1=I-P_0\),
\([P_1,U]=-[P_0,U]\), so the ratio of the left side, expressed through the
aggregate-projector supremum, to the cellwise \(L^2\) aggregate is exactly
\(1/\sqrt2\) whenever the commutator is nonzero. The operator-theoretic
coefficient \(1/\sqrt2\) is therefore naturally sharp in this setting.

**Novelty consequence: very important.** The distance formula shows that the
aggregate-projector supremum is not by itself a new object. The relevant
literature question now narrows to the sharp comparison between this quotient
distance and the \(L^2\) aggregate of the atomic commutators \([P_c,U]\), and
then to the total-variation corollary for the projective weights.

#### K. Row/column operators — the multicell estimate as a standard block inequality

The T5B multicell estimate has an elementary row/column-operator formulation.
For a subset \(S\subseteq C\), the operator

\[
P_SU P_{S^c}
\]

is the row operator formed by the blocks \(P_cUP_{S^c}\), \(c\in S\). Since
the output spaces \(P_cH\) are orthogonal,

\[
\lVert P_SU P_{S^c}\rVert_{\mathrm{op}}^2
=
\left\|
\sum_{c\in S}
(P_cUP_{S^c})^\ast(P_cUP_{S^c})
\right\|_{\mathrm{op}}
\le
\sum_{c\in S}\lVert P_cUP_{S^c}\rVert_{\mathrm{op}}^2.
\]

Each block satisfies

\[
\lVert P_cUP_{S^c}\rVert_{\mathrm{op}}
\le
\lVert[P_c,U]\rVert_{\mathrm{op}}.
\]

Applying the same argument to the complement gives

\[
\lVert[P_S,U]\rVert_{\mathrm{op}}^2
\le
\min\!\left(
\sum_{c\in S}\lVert[P_c,U]\rVert_{\mathrm{op}}^2,\,
\sum_{c\notin S}\lVert[P_c,U]\rVert_{\mathrm{op}}^2
\right).
\]

Because the two sums partition the full budget,

\[
\lVert[P_S,U]\rVert_{\mathrm{op}}^2
\le
\frac12
\sum_c\lVert[P_c,U]\rVert_{\mathrm{op}}^2.
\]

This is essentially the standard row/column-operator norm formula followed by
\(\min(A,B)\le(A+B)/2\).

**Novelty consequence: major.** The quadratic factor \(1/2\) in T5B does not
appear to require a deep new operator-theoretic mechanism once the correct
aggregate projector \(P_S\) is chosen. Any remaining publication value must
therefore be assessed at the level of the whole package: positive-variation
subset selection, exact passage to full \(L^1\) profile variation, optimal
universal constant, explicit saturation, composition/iteration, and Lean
formalization.

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
$\lVert[P,U]\rVert_{\mathrm{op}}=\lVert P-UPU^\ast\rVert_{\mathrm{op}}$
places the local $P_S$ step directly inside classical projection and
unitary-conjugation geometry; Kittaneh's commutator inequalities reinforce this
point. The prior-art risk therefore concentrates on the subsequent steps:
constructing the positive-variation subset, aggregating the cellwise $L^2$
budget, using the cross-block decomposition, and obtaining the sharp quadratic
factor $1/2$. Closely related statements may occur in work on pairs of
projections, pinching, conditional expectations, almost commuting PVMs, and
block operator matrices.

**R2 — combination-of-standard-lemmas risk: HIGH.** The multicell operator
estimate reduces to a standard row/column-operator norm estimate, the
(S/S^c) partition, and (min(A,B)le(A+B)/2). Even absent an identical
printed statement, a referee may therefore regard the main proof as a short
combination of standard facts. Publication value must rest primarily on the
best-constant theorem in this precise metric, explicit saturation, the
composition/iteration package, and verified formalization rather than on a
claim of technically novel operator geometry.

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
| Halmos 1969 | pair of projections | canonical block form | two-block reduction | exact structure | no, but fundamental local geometry |
| Rieffel 2025 / Arveson | distance to (mathcal B_D) | supremum of commutators with commutant projections | all (P_S) | exact distance formula | no, but reformulates the operator-side quantity |

### 6. Provisional conclusion

**NOVELTY STATUS: UNRESOLVED; EXACT ANTECEDENT NOT IDENTIFIED, BUT
STANDARD-LEMMA RISK IS HIGH.**

This means only that important structural antecedents exist and that none of
the works inspected above manifestly states the entire T5 package. It is not a
novelty certificate.

The audit now narrows the uncertainty region substantially: local
two-projection geometry is classical (Halmos, Kittaneh, Conde), and the
aggregate-projector supremum has a standard interpretation as distance to the
block-diagonal subalgebra (Rieffel/Arveson). The highest-priority remaining
search is therefore almost entirely the **multicell** comparison
[
operatorname{dist}(U,mathcal B_D)
stackrel{?}{le}
rac1{sqrt2}
left(sum_clVert[P_c,U]Vert_{mathrm{op}}^2ight)^{1/2},
]
its best constant, and the passage from this inequality to total variation of
the projective profile.

### 7. Gate before submission

Before any new-theorem claim:

1. search explicitly for the comparison between distance to the block-diagonal
   algebra and the (L^2) norm of the atomic-commutator family;
2. search for total-variation bounds on PVM statistics in terms of this
   quotient distance or the commutators;
3. follow backward citations from Halmos, Kittaneh, Conde, Hastings,
   de la Salle, and Czajkowski–Grilo;
4. test whether $\sqrt2$ follows immediately from a more general published
   operator inequality;
5. if a more general theorem is found, state precisely what remains new:
   formulation, sharpness family, Lean formalization, composition results, or
   another corollary.

No transition from **UNRESOLVED** to **NOVEL** is justified before that work.

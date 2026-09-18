# Publication nucleus — T0–T5

## Français

Date : **2026-09-18**. Statut : **document de préparation**.

Ce document extrait le noyau mathématique candidat à une publication à partir
des résultats déjà **FORMALIZED / AUDITED** du cycle transversal T0–T5. Il
n'ajoute aucun théorème Lean, aucune hypothèse physique et aucun statut de
publication.

### 1. Formulation mathématique minimale

Soit une décomposition projective orthogonale finie
$(P_c)_{c\in C}$ de l'identité sur un espace de Hilbert complexe de dimension
finie. Pour un état $x$, poser

$$
p_c(x)=\lVert P_c x\rVert^2,
$$

et, pour une unitaire $U$,

$$
\delta(D,U)=
\left(\sum_{c\in C}\lVert P_cU-UP_c\rVert_{\mathrm{op}}^2\right)^{1/2}.
$$

Le résultat central déjà formalisé est

$$
\sum_{c\in C}|p_c(Ux)-p_c(x)|
\le \sqrt{2}\,\lVert x\rVert^2\,\delta(D,U).
$$

Pour $\lVert x\rVert=1$,

$$
\lVert p(Ux)-p(x)\rVert_1\le \sqrt{2}\,\delta(D,U).
$$

La constante $\sqrt{2}$ est universellement optimale dans cette portée :

$$
K\text{ est un coefficient universel}
\quad\Longleftrightarrow\quad
\sqrt{2}\le K.
$$

### 2. API Lean correspondante

Résultat supérieur :

- \`recordProfileL1_unitary_le_sqrt_two_mul_norm_sq_mul_operatorNormCommutatorL2\`;
- \`recordProfileL1_unitary_le_sqrt_two_mul_operatorNormCommutatorL2\`;
- \`IsUniversalUniformTransferCoefficient\`;
- \`isUniversalUniformTransferCoefficient_iff_sqrt_two_le\`.

Sharpness :

- \`uniformTransferSharpness_profile_exact\`;
- \`uniformTransferSharpnessRatio_eq_sqrt_two\`;
- \`exists_uniformTransfer_violation_of_lt_sqrt_two\`.

Résultats complémentaires pouvant entrer dans l'article :

- contrôle structurel des projecteurs transportés par
  \`projectorStructureDisplacementL2_le_operatorNormProjectorCommutatorL2\`;
- sharpness du coefficient additif ED4B via
  \`iterationSharpnessAdditiveRatio_tendsto_one\` et
  \`exists_twoStep_defect_gt_const_mul_sum_of_lt_one\`;
- exemple exact \`WorkedInstance\`;
- bornes de composition et d'itération ED4A/ED4B.

### 3. Mécanisme de la constante \`sqrt 2\`

La preuve T5B ne provient pas d'une simple amélioration numérique de la borne
ED3B précédente. Elle utilise :

1. l'identité de variation totale pour isoler le sous-ensemble $S$ des
   cellules où la probabilité augmente ;
2. le projecteur agrégé $P_S$ ;
3. la décomposition orthogonale $S/S^c$ du commutateur ;
4. le partage quadratique exact du budget global ;
5. la borne

   $$
   \lVert[P_S,U]x\rVert^2
   \le \frac12\,\delta(D,U)^2\lVert x\rVert^2.
   $$

Le facteur $1/2$ dans la borne quadratique produit le facteur $\sqrt{2}$
dans le transfert $L^1$.

T5A fournit ensuite une famille binaire explicite dont le quotient

$$
\frac{\lVert p(Ux)-p(x)\rVert_1}{\delta(D,U)}
$$

vaut exactement $\sqrt{2}$, de sorte que l'upper bound T5B et le lower bound
T5A coïncident.

### 4. Positionnement candidat de l'article

L'audit bibliographique du 18 septembre 2026 modifie le positionnement
recommandé.

**Piste A — recommandée à ce stade : formalisation vérifiée + paquet sharp.**

Titre de travail possible :

**Lean-verified sharp stability of finite projective measurement profiles**

ou, plus neutre :

**Machine-checked stability bounds for finite projective measurement profiles**

La contribution mise en avant serait alors :

- une formulation unifiée des bornes de stabilité ;
- la constante optimale \(\sqrt2\) et une famille saturante explicite ;
- les extensions composition/itération et leur sharpness ;
- la séparation systématique entre couches NON BORN-SENSITIVE et
  BORN-SENSITIVE ;
- la formalisation Lean et l'audit d'axiomes ;
- une carte précise des dépendances logiques et des limites d'interprétation.

**Piste B — non recommandée sans résultat supplémentaire : nouveau théorème
d'analyse opératorielle.**

L'audit montre que la preuve T5B se décompose en briques standards :
géométrie de deux projections, formule de distance à une sous-algèbre,
row/column operators, partition \(S/S^c\) et dualité de variation totale.
Aucun antécédent exact du paquet complet n'a été identifié, mais cela ne suffit
pas à soutenir une forte revendication de nouveauté technique.

Le vocabulaire principal devrait rester celui des décompositions projectives,
profils de probabilités, commutateurs, stabilité quantitative et vérification
formelle. Le terme « decoherence » ne devrait pas porter le titre tant
qu'aucune dynamique de système ouvert, suppression hors diagonale ou
redondance environnementale n'est formalisée.

### 5. Architecture possible du manuscrit

1. décomposition projective finie et profil \(p(x)\) ;
2. défaut uniforme \(\delta(D,U)\) ;
3. dérivation courte de la borne sharp à partir des briques standards ;
4. famille saturante et optimalité de \(\sqrt2\) ;
5. composition et itération, avec sharpness du coefficient additif ;
6. contrôle structurel des projecteurs ;
7. formalisation Lean, architecture des dépendances et audit d'axiomes ;
8. comparaison détaillée avec Halmos, Kittaneh, Conde, Rieffel/Arveson,
   almost-commutation et disturbance ;
9. limites : aucune dynamique physique ni décohérence n'est déduite.

Dans cette version, le résultat de meilleure constante reste le centre
mathématique, mais **la valeur de l'article ne doit pas être présentée comme
reposant sur une preuve opératorielle techniquement nouvelle**. Le point fort
est le paquet sharp complet, sa vérification mécanique et la clarification de
sa portée.

### 6. Pare-feu d'interprétation

Le défaut commutatorial et les résultats purement opératoriels sont
**NON BORN-SENSITIVE**. Le profil $p_c(x)=\lVert P_cx\rVert^2$, sa distance
$L^1$, le transfert T5B et la saturation T5A sont **BORN-SENSITIVE**.

Le manuscrit ne devra donc pas présenter le résultat comme une dérivation de la
règle de Born, une preuve de décohérence, une sélection de base ou une
émergence de branches.

### 7. État de nouveauté

**NOVELTY STATUS: UNRESOLVED; STANDARD-LEMMA RISK HIGH.**

L'audit bibliographique détaillé est consigné dans
\`docs/LITERATURE_AUDIT_T0_T5.md\`.

État actuel :

- aucun antécédent exact du paquet T5 complet n'a été identifié ;
- la géométrie locale de deux projections est classique ;
- le supremum sur les projecteurs agrégés a une interprétation standard de
  distance à la sous-algèbre bloc-diagonale ;
- la borne multi-cellule se réduit à une estimation standard de row/column
  operator et à la partition \(S/S^c\) ;
- le passage final au profil \(L^1\) se réduit à l'identité standard de
  variation totale.

Par conséquent, **l'absence de formule identique dans la littérature ne doit
pas être confondue avec une preuve de nouveauté mathématique substantielle**.
Le risque est très élevé qu'un referee juge T5B comme un corollaire naturel de
faits standards, même si la constante optimale, la saturation explicite et
l'intégration formalisée sont propres.

### 8. Critère de passage au manuscrit

Deux voies sont désormais distinguées.

**Voie A — manuscrit de formalisation / vérification : GO conditionnel.**

Un manuscrit peut être préparé sans revendiquer un nouveau mécanisme
opératoriel, à condition que la contribution soit clairement formulée comme
une intégration sharp machine-checkée : théorème de meilleure constante,
saturation, composition/itération, audits et dépendances logiques.

**Voie B — manuscrit de nouveau résultat mathématique : NO-GO en l'état.**

Pour revenir à cette voie, il faudrait obtenir au moins un incrément
mathématique non trivial qui ne se réduise pas immédiatement aux briques
standards identifiées. Exemples de directions possibles : généralisation aux
POVMs, aux états mixtes/channels, à une autre classe de normes avec meilleure
constante non triviale, ou un résultat structurel de composition/dynamique qui
dépasse les inégalités bloc élémentaires.

Aucun statut **PUBLISHED** n'est revendiqué et aucun choix de revue n'est fixé
par ce document.


## English

Date: **2026-09-18**. Status: **preparation document**.

This document extracts a candidate publication nucleus from results already
**FORMALIZED / AUDITED** in the transversal T0–T5 cycle. It adds no Lean
theorem, physical assumption, or publication status.

### 1. Minimal mathematical formulation

Let $(P_c)_{c\in C}$ be a finite orthogonal projective decomposition of the
identity on a finite-dimensional complex Hilbert space. For a state $x$, set

$$
p_c(x)=\lVert P_c x\rVert^2,
$$

and for a unitary $U$,

$$
\delta(D,U)=
\left(\sum_{c\in C}\lVert P_cU-UP_c\rVert_{\mathrm{op}}^2\right)^{1/2}.
$$

The formalized central result is

$$
\sum_{c\in C}|p_c(Ux)-p_c(x)|
\le \sqrt{2}\,\lVert x\rVert^2\,\delta(D,U).
$$

For $\lVert x\rVert=1$,

$$
\lVert p(Ux)-p(x)\rVert_1\le \sqrt{2}\,\delta(D,U).
$$

The constant $\sqrt{2}$ is universally optimal in this scope:

$$
K\text{ is a universal coefficient}
\quad\Longleftrightarrow\quad
\sqrt{2}\le K.
$$

### 2. Corresponding Lean API

Upper bound:

- \`recordProfileL1_unitary_le_sqrt_two_mul_norm_sq_mul_operatorNormCommutatorL2\`;
- \`recordProfileL1_unitary_le_sqrt_two_mul_operatorNormCommutatorL2\`;
- \`IsUniversalUniformTransferCoefficient\`;
- \`isUniversalUniformTransferCoefficient_iff_sqrt_two_le\`.

Sharpness:

- \`uniformTransferSharpness_profile_exact\`;
- \`uniformTransferSharpnessRatio_eq_sqrt_two\`;
- \`exists_uniformTransfer_violation_of_lt_sqrt_two\`.

Complementary results that may enter the paper:

- transported-projector structural control via
  \`projectorStructureDisplacementL2_le_operatorNormProjectorCommutatorL2\`;
- ED4B additive-coefficient sharpness via
  \`iterationSharpnessAdditiveRatio_tendsto_one\` and
  \`exists_twoStep_defect_gt_const_mul_sum_of_lt_one\`;
- the exact \`WorkedInstance\`;
- ED4A/ED4B composition and iteration bounds.

### 3. Why the constant is \`sqrt 2\`

The T5B proof is not merely a numerical tightening of the previous ED3B
estimate. It uses:

1. the total-variation identity to isolate the subset $S$ of cells whose
   probabilities increase;
2. the aggregate projector $P_S$;
3. the orthogonal $S/S^c$ decomposition of its commutator;
4. the exact quadratic split of the global defect budget;
5. the bound

   $$
   \lVert[P_S,U]x\rVert^2
   \le \frac12\,\delta(D,U)^2\lVert x\rVert^2.
   $$

The factor $1/2$ in the quadratic estimate produces the factor $\sqrt{2}$ in
the $L^1$ transfer bound.

T5A then gives an explicit binary family for which

$$
\frac{\lVert p(Ux)-p(x)\rVert_1}{\delta(D,U)}
$$

is exactly $\sqrt{2}$, so the T5B upper bound and the T5A lower bound coincide.

### 4. Candidate paper positioning

The September 18, 2026 literature audit changes the recommended positioning.

**Track A — currently recommended: verified formalization + sharp package.**

Possible working title:

**Lean-verified sharp stability of finite projective measurement profiles**

or, more neutral:

**Machine-checked stability bounds for finite projective measurement profiles**

The contribution would emphasize:

- a unified formulation of the stability bounds;
- the optimal coefficient \(\sqrt2\) and an explicit saturating family;
- composition/iteration extensions and their sharpness;
- systematic separation of NON BORN-SENSITIVE and BORN-SENSITIVE layers;
- Lean formalization and axioms auditing;
- a precise logical-dependency and interpretation-scope map.

**Track B — not recommended without an additional result: new
operator-analysis theorem.**

The audit shows that the T5B proof decomposes into standard ingredients:
two-projection geometry, distance to a subalgebra, row/column operators, the
\(S/S^c\) budget split, and total-variation duality. No exact antecedent for
the whole package has been identified, but this is insufficient for a strong
technical-novelty claim.

The primary language should remain finite projective decompositions,
probability profiles, commutators, quantitative stability, and formal
verification. “Decoherence” should not carry the title while no open-system
dynamics, off-diagonal suppression, or environmental redundancy is formalized.

### 5. Possible manuscript structure

1. finite projective decompositions and the profile \(p(x)\);
2. the uniform defect \(\delta(D,U)\);
3. a short derivation of the sharp bound from standard ingredients;
4. the saturating family and optimality of \(\sqrt2\);
5. composition and iteration, including additive sharpness;
6. transported-projector structural control;
7. Lean formalization, dependency architecture, and axioms audit;
8. detailed comparison with Halmos, Kittaneh, Conde, Rieffel/Arveson,
   almost-commutation, and disturbance literature;
9. limitations: no physical dynamics or decoherence is inferred.

In this version the best-constant result remains the mathematical centerpiece,
but **the paper should not claim value from a technically new operator proof**.
The strength is the complete sharp package, its machine verification, and its
carefully delimited scope.

### 6. Interpretation firewall

The commutator defect and purely operator-theoretic results are **NON
BORN-SENSITIVE**. The profile $p_c(x)=\lVert P_cx\rVert^2$, its $L^1$
distance, the T5B transfer, and T5A saturation are **BORN-SENSITIVE**.

The manuscript should therefore not present the result as a derivation of the
Born rule, a decoherence theorem, basis selection, or branch emergence.

### 7. Novelty status

**NOVELTY STATUS: UNRESOLVED; STANDARD-LEMMA RISK HIGH.**

The detailed literature audit is recorded in
\`docs/LITERATURE_AUDIT_T0_T5.md\`.

Current assessment:

- no exact antecedent for the complete T5 package has been identified;
- local two-projection geometry is classical;
- the aggregate-projector supremum has a standard distance-to-block-diagonal
  algebra interpretation;
- the multicell estimate reduces to a standard row/column-operator estimate
  plus the \(S/S^c\) budget split;
- the final \(L^1\)-profile passage reduces to standard total-variation
  duality.

Accordingly, **failure to find the identical formula should not be confused
with evidence of substantial mathematical novelty**. There is a very high risk
that a referee views T5B as a natural corollary of standard facts, even though
the optimal constant, explicit saturation, and verified integration are clean.

### 8. Gate to manuscript drafting

Two tracks are now distinguished.

**Track A — formalization / verification manuscript: CONDITIONAL GO.**

A manuscript can be prepared without claiming a new operator-theoretic
mechanism, provided the contribution is framed as a machine-checked sharp
integration: best-constant theorem, saturation, composition/iteration, audits,
and logical dependencies.

**Track B — new-mathematics manuscript: NO-GO in the present state.**

Reopening this track would require at least one nontrivial mathematical
increment that does not collapse immediately to the standard ingredients
identified by the audit. Possible directions include POVMs, mixed
states/channels, another norm class with a genuinely nontrivial optimal
constant, or a structural composition/dynamical result beyond elementary
block inequalities.

No **PUBLISHED** status is claimed and no target journal is fixed by this
document.

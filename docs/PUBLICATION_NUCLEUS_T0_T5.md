# Publication nucleus — T0–T5

## Français

Date : **2026-09-18**. Statut : **document de préparation**.

Ce document extrait le noyau mathématique candidat à une publication à partir
des résultats déjà **FORMALIZED / AUDITED** du cycle transversal T0–T5. Il
n'ajoute aucun théorème Lean, aucune hypothèse physique et aucun statut de
publication.

### 1. Formulation mathématique minimale

Soit une décomposition projective orthogonale finie ((P_c)_{cin C}) de
l'identité sur un espace de Hilbert complexe de dimension finie. Pour un état
(x), poser

[
p_c(x)=\|P_c x\|^2,
]

et, pour une unitaire (U),

[
delta(D,U)=
\left(\sum_{cin C}\|P_cU-UP_c\|_{op}^2\right)^{1/2}.
]

Le résultat central déjà formalisé est

[
\sum_{cin C}|p_c(Ux)-p_c(x)|
\le \sqrt 2,\|x\|^2,delta(D,U).
]

Pour (|x|=1),

[
\|p(Ux)-p(x)\|_1\le \sqrt 2,delta(D,U).
]

La constante (sqrt2) est universellement optimale dans cette portée :

[
K	ext{ est un coefficient universel}
\quad\Longleftrightarrow\quad
\sqrt2\le K.
]

### 2. API Lean correspondante

Résultat supérieur :

- `recordProfileL1_unitary_le_sqrt_two_mul_norm_sq_mul_operatorNormCommutatorL2`;
- `recordProfileL1_unitary_le_sqrt_two_mul_operatorNormCommutatorL2`;
- `IsUniversalUniformTransferCoefficient`;
- `isUniversalUniformTransferCoefficient_iff_sqrt_two_le`.

Sharpness :

- `uniformTransferSharpness_profile_exact`;
- `uniformTransferSharpnessRatio_eq_sqrt_two`;
- `exists_uniformTransfer_violation_of_lt_sqrt_two`.

Résultats complémentaires pouvant entrer dans l'article :

- contrôle structurel des projecteurs transportés par
  `projectorStructureDisplacementL2_le_operatorNormProjectorCommutatorL2`;
- sharpness du coefficient additif ED4B via
  `iterationSharpnessAdditiveRatio_tendsto_one` et
  `exists_twoStep_defect_gt_const_mul_sum_of_lt_one`;
- exemple exact `WorkedInstance`;
- bornes de composition et d'itération ED4A/ED4B.

### 3. Mécanisme de la constante `sqrt 2`

La preuve T5B ne provient pas d'une simple amélioration numérique de la borne
ED3B précédente. Elle utilise :

1. l'identité de variation totale pour isoler le sous-ensemble (S) des
   cellules où la probabilité augmente ;
2. le projecteur agrégé (P_S) ;
3. la décomposition orthogonale (S/S^c) du commutateur ;
4. le partage quadratique exact du budget global ;
5. la borne
   [
   \|[P_S,U]x\|^2\le
   \frac12,delta(D,U)^2\|x\|^2.
   ]

Le facteur (1/2) dans la borne quadratique produit le facteur (sqrt2)
dans le transfert (L^1).

T5A fournit ensuite une famille binaire explicite dont le quotient
[
\frac{\|p(Ux)-p(x)\|_1}{\delta(D,U)}
]
vaut exactement (sqrt2), de sorte que l'upper bound T5B et le lower bound
T5A coïncident.

### 4. Positionnement candidat de l'article

Titre de travail recommandé :

**Optimal commutator control of finite projective measurement profiles**

Variante plus descriptive :

**Sharp stability of finite projective measurement profiles under approximately commuting unitaries**

Le vocabulaire principal devrait rester celui des décompositions projectives,
profils de probabilités, commutateurs et stabilité quantitative. Le terme
« decoherence » ne devrait pas porter le titre tant qu'aucune dynamique de
système ouvert, suppression hors diagonale ou redondance environnementale
n'est formalisée.

### 5. Architecture possible du manuscrit

1. décomposition projective finie et profil (p(x)) ;
2. défaut uniforme (delta(D,U)) ;
3. borne élémentaire puis borne optimale ;
4. géométrie subset/complément et preuve de (sqrt2) ;
5. famille saturante et optimalité ;
6. composition et itération, avec sharpness du coefficient additif ;
7. contrôle structurel des projecteurs ;
8. formalisation Lean et audit d'axiomes ;
9. limites : aucune dynamique physique ni décohérence n'est déduite.

Le résultat principal à mettre en avant est le théorème de meilleure constante,
non l'historique ED1–ED4B.

### 6. Pare-feu d'interprétation

Le défaut commutatorial et les résultats purement opératoriels sont
**NON BORN-SENSITIVE**. Le profil (p_c(x)=\|P_cx\|^2), sa distance (L^1),
le transfert T5B et la saturation T5A sont **BORN-SENSITIVE**.

Le manuscrit ne devra donc pas présenter le résultat comme une dérivation de la
règle de Born, une preuve de décohérence, une sélection de base ou une
émergence de branches.

### 7. État de nouveauté

**NOVELTY STATUS: UNRESOLVED.**

Des recherches externes ciblées initiales n'ont pas identifié d'énoncé
manifestement identique combinant exactement :

- une décomposition projective finie arbitraire ;
- la distance (L^1) complète des distributions de poids projectifs avant et
  après une unitaire ;
- l'agrégat (L^2) des normes d'opérateur des commutateurs cellule par
  cellule ;
- une meilleure constante universelle égale à (sqrt2) ;
- une famille explicite saturant cette constante.

Cette absence de correspondance immédiate ne constitue **pas** une preuve de
nouveauté. Avant toute soumission, un audit bibliographique dédié doit couvrir
au minimum : perturbation de mesures projectives, stabilité des mesures
spectrales, inégalités commutatoriales, disturbance/incompatibility,
approximate commutation et distances statistiques des distributions de
mesure.

### 8. Critère de passage au manuscrit

Le passage à un manuscrit scientifique est justifié si l'audit bibliographique
confirme soit :

- l'absence d'un théorème équivalent avec la constante optimale (sqrt2), ou
- une formulation antérieure plus générale dont la présente contribution
  apporte une formalisation Lean substantielle, une preuve nouvelle, une
  sharpness explicite ou un corollaire non documenté.

En cas d'antériorité exacte, le cycle reste mathématiquement correct mais le
positionnement devra basculer vers la formalisation vérifiée et l'intégration
des résultats, plutôt que vers une revendication de nouveau théorème.

## English

Date: **2026-09-18**. Status: **preparation document**.

This document extracts a candidate publication nucleus from results already
**FORMALIZED / AUDITED** in the transversal T0–T5 cycle. It adds no Lean
theorem, physical assumption, or publication status.

### 1. Minimal mathematical formulation

Let ((P_c)_{cin C}) be a finite orthogonal projective decomposition of the
identity on a finite-dimensional complex Hilbert space. For a state (x), set

[
p_c(x)=\|P_c x\|^2,
]

and for a unitary (U),

[
delta(D,U)=
\left(\sum_{cin C}\|P_cU-UP_c\|_{op}^2\right)^{1/2}.
]

The formalized central result is

[
\sum_{cin C}|p_c(Ux)-p_c(x)|
\le \sqrt2,\|x\|^2,delta(D,U).
]

For (|x|=1),

[
\|p(Ux)-p(x)\|_1\le \sqrt2,delta(D,U).
]

The constant (sqrt2) is universally optimal in this scope:

[
K	ext{ is a universal coefficient}
\quad\Longleftrightarrow\quad
\sqrt2\le K.
]

### 2. Corresponding Lean API

Upper bound:

- `recordProfileL1_unitary_le_sqrt_two_mul_norm_sq_mul_operatorNormCommutatorL2`;
- `recordProfileL1_unitary_le_sqrt_two_mul_operatorNormCommutatorL2`;
- `IsUniversalUniformTransferCoefficient`;
- `isUniversalUniformTransferCoefficient_iff_sqrt_two_le`.

Sharpness:

- `uniformTransferSharpness_profile_exact`;
- `uniformTransferSharpnessRatio_eq_sqrt_two`;
- `exists_uniformTransfer_violation_of_lt_sqrt_two`.

Complementary results that may enter the paper:

- transported-projector structural control via
  `projectorStructureDisplacementL2_le_operatorNormProjectorCommutatorL2`;
- ED4B additive-coefficient sharpness via
  `iterationSharpnessAdditiveRatio_tendsto_one` and
  `exists_twoStep_defect_gt_const_mul_sum_of_lt_one`;
- the exact `WorkedInstance`;
- ED4A/ED4B composition and iteration bounds.

### 3. Why the constant is `sqrt 2`

The T5B proof is not merely a numerical tightening of the previous ED3B
estimate. It uses:

1. the total-variation identity to isolate the subset (S) of cells whose
   probabilities increase;
2. the aggregate projector (P_S);
3. the orthogonal (S/S^c) decomposition of its commutator;
4. the exact quadratic split of the global defect budget;
5. the bound
   [
   \|[P_S,U]x\|^2\le
   \frac12,delta(D,U)^2\|x\|^2.
   ]

The factor (1/2) in the quadratic estimate produces the factor (sqrt2) in
the (L^1) transfer bound.

T5A then gives an explicit binary family for which
[
\frac{\|p(Ux)-p(x)\|_1}{\delta(D,U)}
]
is exactly (sqrt2), so the T5B upper bound and the T5A lower bound coincide.

### 4. Candidate paper positioning

Recommended working title:

**Optimal commutator control of finite projective measurement profiles**

More descriptive alternative:

**Sharp stability of finite projective measurement profiles under approximately commuting unitaries**

The primary language should be finite projective decompositions, probability
profiles, commutators, and quantitative stability. “Decoherence” should not
carry the title while no open-system dynamics, off-diagonal suppression, or
environmental redundancy is formalized.

### 5. Possible manuscript structure

1. finite projective decompositions and the profile (p(x));
2. the uniform defect (delta(D,U));
3. elementary and then optimal transfer bounds;
4. subset/complement geometry and the (sqrt2) proof;
5. saturating family and optimality;
6. composition and iteration, including additive sharpness;
7. transported-projector structural control;
8. Lean formalization and axioms audit;
9. limitations: no physical dynamics or decoherence is inferred.

The headline result should be the best-constant theorem, not the ED1–ED4B
development history.

### 6. Interpretation firewall

The commutator defect and purely operator-theoretic results are **NON
BORN-SENSITIVE**. The profile (p_c(x)=\|P_cx\|^2), its (L^1) distance, the
T5B transfer, and T5A saturation are **BORN-SENSITIVE**.

The manuscript should therefore not present the result as a derivation of the
Born rule, a decoherence theorem, basis selection, or branch emergence.

### 7. Novelty status

**NOVELTY STATUS: UNRESOLVED.**

Initial targeted external searches did not identify an obviously identical
statement simultaneously combining:

- an arbitrary finite projective decomposition;
- the full (L^1) distance between projective-weight distributions before and
  after a unitary;
- the (L^2) aggregate of per-cell operator commutator norms;
- the optimal universal coefficient (sqrt2);
- an explicit family saturating that coefficient.

Failure to find an immediate match is **not** evidence of novelty. Before
submission, a dedicated literature audit must cover at least projective
measurement perturbation, spectral-measure stability, commutator inequalities,
measurement disturbance/incompatibility, approximate commutation, and
statistical distances between measurement distributions.

### 8. Gate to manuscript drafting

A scientific manuscript is justified if the literature audit confirms either:

- no equivalent theorem with optimal constant (sqrt2), or
- an earlier more general statement for which the present work contributes a
  substantial Lean formalization, a new proof, explicit sharpness, or a
  previously undocumented corollary.

If an exact antecedent is found, the mathematics remains correct but the
positioning should shift toward verified formalization and integration rather
than a new-theorem claim.

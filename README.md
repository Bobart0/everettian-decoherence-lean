# Everettian Decoherence in Lean

## Français

Statut : **ED4B — CLOSED IN ITS FINITE ITERATION-ACCUMULATION SCOPE** ;
**cycle transversal T0–T5 — CLOSED ; T1–T5 FORMALIZED / AUDITED**. Ce dépôt
formalise en Lean 4 une chaîne quantitative finie reliant la structure exacte
finie exposée par `everettian-probability-lean`, une géométrie de profils de
records, une perturbation état-vers-record, des défauts de commutation de
projecteurs, leur uniformisation par norme d'opérateur, leur composition à
perspective fixée et leur accumulation sur une liste finie de transformations.
Il ne contient aujourd'hui aucune dynamique temporelle ni aucune décohérence.

La dépendance stable est `everettian-probability-lean v2.0.0`. L'architecture
locale contient une frontière amont, un arbre `Metrics`, un arbre
`Approximation`, un arbre d'audit, des gardes et une CI.

Résultats locaux actuels :

- **ED1** — géométrie L1 générique et profil bornien `recordProfileL1`,
  BORN-SENSITIVE ;
- **ED2A** — borne état-vers-record explicite avec facteur de cardinalité ;
- **ED2B** — borne globale sans facteur de cardinalité, constante 2 pour un
  état normalisé ;
- **ED3A** — défaut statewise de commutation de projecteurs et son transfert
  BORN-SENSITIVE vers `recordProfileL1` ;
- **ED3B** — uniformisation du défaut ED3A par norme d'opérateur, uniforme sur
  les états pour une perspective et une transformation fixées, avec limite
  exacte vers la commutation globale ;
- **ED4A — CLOSED IN ITS FINITE FIXED-PERSPECTIVE COMPOSITION SCOPE** —
  composition de deux transformations, borne sous-additive du défaut uniforme
  et transfert BORN-SENSITIVE correspondant ;
- **ED4B — CLOSED IN ITS FINITE ITERATION-ACCUMULATION SCOPE** — composition
  d'une liste finie, majoration du défaut par la somme des défauts élémentaires
  et transfert BORN-SENSITIVE itéré ;
- **T5A/T5B** — coefficient optimal exact `sqrt 2` pour le transfert uniforme
  ED3B sur les états normalisés : T5A fournit la saturation et T5B la borne
  universelle ;
- **front post-T5 de stabilité quantitative** — classification exacte du cas
  de saturation sur deux cellules, modulus explicite à échelle fixée, et
  famille tridimensionnelle établissant la nécessité de la dépendance
  `η / ρ^2` à constante près.

ED1–ED4B ainsi que T1–T5 sont formalisés et audités dans leur portée
documentée. Les déclarations principales ED4A et ED4B sont aussi
auditées dans `EverettianDecoherence/Audit/ComposedRecordPreservation.lean` et
`EverettianDecoherence/Audit/IteratedRecordPreservation.lean`, importés par
`Audit/MainResults.lean`. Aucun statut de publication supplémentaire n'est
affirmé ici.

```sh
lake build
bash scripts/guard.sh
bash scripts/validate.sh
```

```lean
import EverettianDecoherence.Metrics.RecordProfileL1
import EverettianDecoherence.Metrics.StateRecordPerturbation
import EverettianDecoherence.Metrics.StateRecordDimensionFree
import EverettianDecoherence.Approximation.ApproximateRecordPreservation
import EverettianDecoherence.Approximation.UniformRecordPreservation
import EverettianDecoherence.Approximation.ComposedRecordPreservation
import EverettianDecoherence.Approximation.IteratedRecordPreservation
import EverettianDecoherence.Approximation.UniformTransferOptimality
import EverettianDecoherence.Approximation.StabilitySharpness
```

Limites physiques actuelles : aucune dynamique temporelle, aucun Hamiltonien,
aucun canal, aucun système ouvert, aucun état mixte, aucune suppression
hors diagonale, aucune décohérence, aucune sélection de base, aucune
redondance environnementale et aucune dérivation de Born ne sont formalisées.

La portée et les limitations sont explicites dans `docs/`. Les contributions
se font par incréments atomiques, vérifiés et sans revendication physique non
formalisée. Licence : Apache-2.0.

## English

Status: **ED4B — CLOSED IN ITS FINITE ITERATION-ACCUMULATION SCOPE**;
**transversal T0–T5 cycle — CLOSED; T1–T5 FORMALIZED / AUDITED**. This
repository formalizes in Lean 4 a finite quantitative chain connecting the
exact finite structure exposed by `everettian-probability-lean`, a
record-profile geometry, a state-to-record perturbation bound, projector-
commutation defects, their operator-norm uniformization, fixed-perspective
composition, and accumulation over a finite list of transformations. It
currently contains no time dynamics and no decoherence.

The stable dependency is `everettian-probability-lean v2.0.0`. The local
architecture has an upstream boundary, a `Metrics` tree, an `Approximation`
tree, an audit tree, guards, and CI.

Current local results:

- **ED1** — generic L1 geometry and the Born-sensitive `recordProfileL1`
  profile;
- **ED2A** — explicit state-to-record bound with a cardinality factor;
- **ED2B** — global bound without a cardinality factor, constant 2 for a
  normalized state;
- **ED3A** — statewise projector-commutation defect and its BORN-SENSITIVE
  transfer to `recordProfileL1`;
- **ED3B** — operator-norm uniformization of the ED3A defect, uniform over
  states for a fixed perspective and transformation, with an exact limit to
  global commutation;
- **ED4A — CLOSED IN ITS FINITE FIXED-PERSPECTIVE COMPOSITION SCOPE** —
  composition of two transformations, a subadditive uniform-defect bound,
  and the corresponding BORN-SENSITIVE transfer;
- **ED4B — CLOSED IN ITS FINITE ITERATION-ACCUMULATION SCOPE** — composition
  of a finite list, a bound of the resulting defect by the sum of elementary
  defects, and the iterated BORN-SENSITIVE transfer;
- **T5A/T5B** — exact optimal `sqrt 2` coefficient for the uniform ED3B
  transfer on normalized states: T5A supplies saturation and T5B the universal
  upper bound;
- **post-T5 quantitative-stability front** — exact two-cell saturation
  classification, an explicit fixed-scale modulus, and a three-dimensional
  family establishing the necessity of the `η / ρ^2` dependence up to
  constants.

ED1–ED4B and T1–T5 are formalized and audited in their documented scope.
The principal ED4A and ED4B declarations are also
audited in `EverettianDecoherence/Audit/ComposedRecordPreservation.lean` and
`EverettianDecoherence/Audit/IteratedRecordPreservation.lean`, both imported by
`Audit/MainResults.lean`. No additional publication status is asserted here.

```sh
lake build
bash scripts/guard.sh
bash scripts/validate.sh
```

```lean
import EverettianDecoherence.Metrics.RecordProfileL1
import EverettianDecoherence.Metrics.StateRecordPerturbation
import EverettianDecoherence.Metrics.StateRecordDimensionFree
import EverettianDecoherence.Approximation.ApproximateRecordPreservation
import EverettianDecoherence.Approximation.UniformRecordPreservation
import EverettianDecoherence.Approximation.ComposedRecordPreservation
import EverettianDecoherence.Approximation.IteratedRecordPreservation
import EverettianDecoherence.Approximation.UniformTransferOptimality
import EverettianDecoherence.Approximation.StabilitySharpness
```

Current physical limitations: no time dynamics, Hamiltonian, channel, open
system, mixed state, off-diagonal suppression, decoherence, basis selection,
environmental redundancy, or derivation of Born is formalized.

Scope and limitations are explicit in `docs/`. Contributions are atomic and
verified, with no unformalized physical claim. License: Apache-2.0.

## Logical direction
## Direction logique

**FR.** La chaîne logique actuelle est : mathématiques finies génériques →
continuité état-vers-record → défaut algébrique statewise de commutateur →
uniformisation par norme d'opérateur → composition et accumulation finies →
transfert bornien BORN-SENSITIVE. Cette chaîne n'inclut encore aucune
dynamique, aucune décohérence et aucune émergence de perspective.

**EN.** The current logical chain is: generic finite mathematics → state-to-
record continuity → statewise algebraic commutator defect → operator-norm
uniformization → finite composition and accumulation → BORN-SENSITIVE record
transfer. This chain still includes no dynamics, no decoherence, and no
perspective emergence.

# Program status

## Français

Date : **2026-07-30**. Version : **0.1.0-dev**. Statut :
**ED3B — CLOSED IN ITS FINITE OPERATOR-NORM UNIFORM SCOPE**.

### Résumé par étape

- **ED1** — *CLOSED IN ITS FINITE KINEMATIC SCOPE* : géométrie L1 finie,
  profils borniens BORN-SENSITIVE, équivalence distance nulle/`SameRecord`,
  annulation exacte sur orbite, composition quantitative.
- **ED2A** — *CLOSED IN ITS EXPLICIT FINITE SCOPE* : borne état-vers-record
  élémentaire avec facteur de cardinalité.
- **ED2B** — *CLOSED IN ITS FINITE DECOMPOSITION-AWARE SCOPE* : borne
  principale `(‖x‖ + ‖y‖) * ‖x - y‖`, version normalisée de constante 2, sans
  facteur de cardinalité.
- **ED3A** — *CLOSED IN ITS FINITE STATEWISE UNITARY SCOPE* : défaut
  algébrique statewise, transfert BORN-SENSITIVE, cas normalisé, limite exacte
  vers `SameRecord` pour l'état considéré.
- **ED3B** — *CLOSED IN ITS FINITE OPERATOR-NORM UNIFORM SCOPE* : uniformise
  ED3A par norme d'opérateur ; voir ci-dessous.

### Résultats locaux les plus forts

1. Contrôle statewise par norme d'opérateur :
   `statewiseProjectorCommutatorL2 D U x ≤ operatorNormProjectorCommutatorL2 D U * ‖x‖`.
2. Transfert bornien uniforme :
   `recordProfileL1 D (U x) x ≤ 2 * ‖x‖ ^ 2 * operatorNormProjectorCommutatorL2 D U`,
   et `≤ 2 * operatorNormProjectorCommutatorL2 D U` pour un état normalisé.
3. Caractérisation exacte du défaut nul :
   `operatorNormProjectorCommutatorL2 D U = 0 ↔ ∀ c, perspectiveProjectorCommutator D U c = 0`,
   impliquant `∀ x, SameRecord D (U x) x`.

### Non encore formalisé

Composition de transformations, itération finie et accumulation d'erreurs,
dynamique temporelle, Hamiltonien, canal, système ouvert, état mixte,
suppression hors diagonale, décohérence, sélection de base, redondance
environnementale, dérivation de Born, et uniformité de l'agrégat d'opérateurs
sur les perspectives ou sur le nombre de cellules.

## English

Date: **2026-07-30**. Version: **0.1.0-dev**. Status:
**ED3B — CLOSED IN ITS FINITE OPERATOR-NORM UNIFORM SCOPE**.

### Summary by stage

- **ED1** — *CLOSED IN ITS FINITE KINEMATIC SCOPE*: finite L1 geometry,
  BORN-SENSITIVE record profiles, zero-distance/`SameRecord` equivalence,
  exact vanishing on the orbit, quantitative composition.
- **ED2A** — *CLOSED IN ITS EXPLICIT FINITE SCOPE*: elementary
  state-to-record bound with a cardinality factor.
- **ED2B** — *CLOSED IN ITS FINITE DECOMPOSITION-AWARE SCOPE*: main bound
  `(‖x‖ + ‖y‖) * ‖x - y‖`, normalized version with constant 2, no cardinality
  factor.
- **ED3A** — *CLOSED IN ITS FINITE STATEWISE UNITARY SCOPE*: statewise
  algebraic defect, BORN-SENSITIVE transfer, normalized case, exact
  `SameRecord` limit at the considered state.
- **ED3B** — *CLOSED IN ITS FINITE OPERATOR-NORM UNIFORM SCOPE*: uniformizes
  ED3A by operator norm; see below.

### Current strongest local results

1. Statewise control by operator norm:
   `statewiseProjectorCommutatorL2 D U x ≤ operatorNormProjectorCommutatorL2 D U * ‖x‖`.
2. Uniform Born-sensitive transfer:
   `recordProfileL1 D (U x) x ≤ 2 * ‖x‖ ^ 2 * operatorNormProjectorCommutatorL2 D U`,
   and `≤ 2 * operatorNormProjectorCommutatorL2 D U` for a normalized state.
3. Exact characterization of the zero defect:
   `operatorNormProjectorCommutatorL2 D U = 0 ↔ ∀ c, perspectiveProjectorCommutator D U c = 0`,
   implying `∀ x, SameRecord D (U x) x`.

### Not yet formalized

Composition of transformations, finite iteration and error accumulation, time
dynamics, Hamiltonian, channel, open system, mixed state, off-diagonal
suppression, decoherence, basis selection, environmental redundancy,
derivation of Born, and uniformity of the operator aggregate over
perspectives or over the cell count.

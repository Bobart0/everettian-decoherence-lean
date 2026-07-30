# Architecture

## Français

Les couches actuellement présentes sont :

1. **Core** — frontière amont stable `Core/UpstreamAPI.lean`, seul point
   d'import vers `everettian_probability`.
2. **Metrics** — géométrie L1 finie, géométrie L2 finie, profils de records,
   perturbation état-vers-record, décomposition orthogonale.
3. **Approximation** — commutateurs de projecteurs, défaut statewise,
   version `ContinuousLinearMap`, normes d'opérateur, agrégation L2 uniforme,
   transferts BORN-SENSITIVE.
4. **Audit** — vérifications de signatures et d'axiomes, jamais une
   dépendance de production.
5. **scripts et CI** — gardes, validation, construction.

`Composition`/`ErrorCalculus`, `Dynamics`, `OpenSystems`, `Decoherence`, et une
éventuelle Public API stable restent **futures** et ne sont pas créées.

### Pare-feu logique

Mathématiques génériques → approximation algébrique → dynamiques explicites
futures → décohérence algébrique future → émergence ou stabilité future des
records → transfert sensible à Born → conséquences normatives conditionnelles.

Le dépôt contient déjà le transfert quantitatif (`Metrics` et
`Approximation`), mais pas encore les couches dynamiques et de décohérence qui
devront ultérieurement l'alimenter.

### Détail de `Metrics`

L1 fini, L2 fini, géométrie des profils, perturbation état-vers-record, et
décomposition orthogonale (utilisée pour supprimer le facteur de cardinalité
en ED2B).

### Détail de `Approximation`

Commutateurs de projecteurs (ED3A, algébrique), défaut statewise, version
`ContinuousLinearMap` du commutateur (ED3B), normes d'opérateur, agrégation
L2 uniforme sur les états, et transferts BORN-SENSITIVE vers `recordProfileL1`
et `SameRecord`.

## English

The layers currently present are:

1. **Core** — stable upstream boundary `Core/UpstreamAPI.lean`, the only
   import point into `everettian_probability`.
2. **Metrics** — finite L1 geometry, finite L2 geometry, record profiles,
   state-to-record perturbation, orthogonal decomposition.
3. **Approximation** — projector commutators, statewise defect, the
   `ContinuousLinearMap` version, operator norms, uniform L2 aggregation,
   BORN-SENSITIVE transfers.
4. **Audit** — signature and axiom checks, never a production dependency.
5. **scripts and CI** — guards, validation, build.

`Composition`/`ErrorCalculus`, `Dynamics`, `OpenSystems`, `Decoherence`, and a
possible stable Public API remain **future-only** and are not created.

### Logical firewall

Generic mathematics → algebraic approximation → future explicit dynamics →
future algebraic decoherence → future record emergence or stability →
Born-sensitive transfer → conditional normative consequences.

The repository already contains the quantitative transfer (`Metrics` and
`Approximation`), but not yet the dynamical and decoherence layers that will
later feed it.

### `Metrics` detail

Finite L1, finite L2, profile geometry, state-to-record perturbation, and
orthogonal decomposition (used to remove the cardinality factor in ED2B).

### `Approximation` detail

Projector commutators (ED3A, algebraic), statewise defect, the
`ContinuousLinearMap` version of the commutator (ED3B), operator norms,
uniform L2 aggregation over states, and BORN-SENSITIVE transfers to
`recordProfileL1` and `SameRecord`.

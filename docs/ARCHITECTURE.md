# Architecture

## Français

Les seules couches présentes sont : 1. frontière amont stable
`Core/UpstreamAPI.lean`; 2. arbre source local; 3. arbre d'audit; 4. scripts
de garde; 5. CI. Les couches Metrics, Approximation, Dynamics, Open systems,
Decoherence models, Robustness et Public API sont seulement futures et ne sont
pas créées à ED0.

## English

The only present layers are: 1. stable upstream boundary
`Core/UpstreamAPI.lean`; 2. local source tree; 3. audit tree; 4. guard
scripts; 5. CI. Metrics, Approximation, Dynamics, Open systems, Decoherence
models, Robustness, and Public API are future-only and are not created at ED0.

### Logical firewall

Generic mathematics → explicit dynamics → algebraic decoherence → record
stability → Born-sensitive transfer → conditional decision consequences.
`Metrics` is the only newly created ED1 layer; it does not define
decoherence. All other physical layers remain future-only.

### ED2B metrics additions

**FR.** La couche Metrics contient désormais le calcul L2 fini, la
décomposition orthogonale globale et une borne état-vers-record sans facteur
de cardinalité. Dynamics, OpenSystems et Decoherence restent absentes.

**EN.** The Metrics layer now contains finite L2 calculation, global
orthogonal decomposition, and a state-to-record bound without a cardinality
factor. Dynamics, OpenSystems, and Decoherence remain absent.

# Metrics instructions

## Français

Distinguer strictement métrique générique et métrique de transfert bornienne.
Ne revendiquer aucune décohérence, dynamique ou interprétation probabiliste
supplémentaire. Les domaines et constantes restent explicites ; les métriques
sont réelles et non négatives, avec réflexivité, symétrie, triangle et
séparation lorsqu'ils sont revendiqués. Les modules génériques n'importent pas
l'amont ; les autres passent exclusivement par
`EverettianDecoherence.Core.UpstreamAPI`. Aucun import interne amont. Toute
future structure de prémisses reçoit ses témoins positif et négatif.

## English

Strictly distinguish generic metrics from Born-sensitive transfer metrics. Do
not claim decoherence, dynamics, or an added probabilistic interpretation.
Domains and constants stay explicit; metrics are nonnegative real quantities
with reflexivity, symmetry, triangle, and separation when claimed. Generic
modules do not import upstream; other modules go exclusively through
`EverettianDecoherence.Core.UpstreamAPI`. No upstream internal import. Every
future premise structure receives positive and negative witnesses.

### ED2B vocabulary

**FR.** « Dimension-free » signifie indépendant du nombre de cellules, jamais
une dimension de Hilbert arbitraire. Une suppression de cardinalité doit
utiliser une identité globale de décomposition. Aucune optimalité sans théorème
spécifique et aucune borne `bornRecord` n'est une décohérence.

**EN.** “Dimension-free” means independent of cell count, never arbitrary
Hilbert dimension. Removing cardinality must use a global decomposition
identity. No optimality without a dedicated theorem, and no `bornRecord` bound
is decoherence.

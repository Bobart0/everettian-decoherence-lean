# Factorization source instructions

## Français

Une factorisation bipartite est toujours fournie explicitement comme
donnée ; elle n'est ni canonique, ni sélectionnée, ni émergée. `system` et
`environment` sont de simples étiquettes des deux facteurs, sans dynamique ni
interprétation physique attachée. L'espace produit-indexé
`EuclideanSpace ℂ (Fin s × Fin e)` n'est pas encore un théorème sur le
produit tensoriel hilbertien : aucune structure tensorielle abstraite n'est
formalisée ici. Aucune opération locale, trace partielle, état réduit,
intrication, dynamique ou décohérence n'est introduite dans cette couche.
Aucun transfert BORN-SENSITIVE n'apparaît à ED5A ; `bornRecord`,
`recordProfileL1` et `SameRecord` restent absents. Aucun import interne amont
n'est permis. Les gardes racine restent applicables.

## English

A bipartite factorization is always explicitly supplied as a given; it is
neither canonical, nor selected, nor emergent. `system` and `environment` are
plain labels for the two factors, with no dynamics or physical
interpretation attached. The product-indexed space
`EuclideanSpace ℂ (Fin s × Fin e)` is not yet a theorem about the Hilbert
tensor product: no abstract tensor structure is formalized here. No local
operation, partial trace, reduced state, entanglement, dynamics, or
decoherence is introduced in this layer. No BORN-SENSITIVE transfer appears
in ED5A; `bornRecord`, `recordProfileL1`, and `SameRecord` remain absent. No
upstream internal import is allowed. Root safeguards remain applicable.

# Audit source instructions

## Français

Les audits peuvent utiliser `#check`, `#print axioms` et des `example`
typés, mais ne fournissent aucun lemme au code de production. Ils importent
des façades locales ou l'adaptateur public, jamais des modules internes amont.
Tout futur résultat scientifique reçoit un audit d'axiomes.

## English

Audits may use `#check`, `#print axioms`, and typed `example` forms, but
provide no lemma to production code. They import local facades or the public
adapter, never upstream internal modules. Every future scientific result gets
a foundational-dependency audit.

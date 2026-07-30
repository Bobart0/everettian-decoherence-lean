# AGENTS.md

## Français

### Mission

Ce dépôt prépare une formalisation Lean 4 / Mathlib de résultats quantitatifs
reliant la structure exacte finie exposée par `everettian-probability-lean`,
des notions de proximité explicitement définies, des dynamiques ou canaux
explicitement définis, la préservation approchée des records et des modèles de
décorrélation dont les hypothèses seront formalisées. ED0 ne contient encore
aucun résultat scientifique local.

### Dépendance amont

`everettian_probability` est épinglé sur `v2.0.0`, résolu au commit
`3129833f3207272eddf9437bd7a3806437b7f87d`. Les seuls imports amont directs
autorisés sont `EverettianProbability.API.ConditionalMainResults` et
`EverettianProbability.API.ExactFiniteMainResults`. Ne jamais importer un
module interne ni reproduire une définition amont. Vérifier toute signature
dans `.lake/packages/everettian_probability`, puis dans un fichier Lean
minimal.

### Règles absolues

1. Les déclarations non démontrées, `native_decide` et les heartbeats
   illimités sont interdits dans le code Lean local.
2. Ne jamais affaiblir silencieusement un énoncé ; un changement de signature
   exige un commit dédié et un rapport.
3. `SORRY_BUDGET` vaut zéro. Toute exception future doit être immédiatement
   précédée d'une annotation `-- SATISFIABILITY:`.
4. Toute structure de prémisses reçoit, dans le même commit, un témoin positif
   dans `Nonvacuity.lean` et un témoin négatif dans `NonTriviality.lean`.
5. Les noms de déclarations ne dépassent jamais leur signature physique.
   Toute proximité nomme espace, métrique ou norme, domaine, constantes et
   conditions ; toute division explicite sa condition de dénominateur.
6. Une quasi-commutation n'est pas une commutation exacte. Une petite erreur
   algébrique n'est pas une décorrélation physique sans modèle dynamique.
   Aucune factorisation système/environnement n'est supposée hors des types.
7. Aucun Hamiltonien, canal, semi-groupe, matrice densité, environnement ou
   temps sans incrément d'architecture explicitement approuvé.
8. Exécuter `lake build`, `bash scripts/guard.sh` et `git diff --check`
   avant un commit. Fichiers de 1500 lignes au plus, commits atomiques.
9. Aucun `lake update` après ED0 sans incrément approuvé ; aucun push forcé,
   changement GitHub, tag, release ou push sans autorisation explicite.
10. Markdown et docstrings de module sont bilingues. Après 20–30 minutes sur
    un but résistant, arrêter et rapporter le but, les signatures et essais.

### Conventions Lean anti-lenteur

Utiliser `simp only` dans les assemblages, `generalize` après substitution
d'une grande expression, des lemmes `private` à contexte minimal, et
restructurer avant d'augmenter des heartbeats. Examiner le but avant
d'empiler des tactiques et vérifier chaque signature amont.

### Portée

ED0 n'établit aucun théorème de décorrélation, robustesse, conservation
approchée, dynamique temporelle, système ouvert, sélection de base, lien avec
l'identité personnelle, dérivation de Born ou dérivation de rationalité.

### Git

Utiliser `main` et les messages `feat(scope):`, `fix(scope):`,
`audit(scope):`, `docs(scope):` ou `chore(scope):`. Interdire les pushes
forcés, suppressions de tags et releases sans instruction humaine.

## English

### Mission

This repository prepares a Lean 4 / Mathlib formalization of quantitative
results connecting the exact finite structure exposed by
`everettian-probability-lean`, explicitly defined proximity notions,
explicitly defined dynamics or channels, approximate record preservation, and
decoherence models whose assumptions will be formalized. ED0 has no local
scientific result yet.

### Upstream dependency

`everettian_probability` is pinned to `v2.0.0`, resolving to
`3129833f3207272eddf9437bd7a3806437b7f87d`. Only
`EverettianProbability.API.ConditionalMainResults` and
`EverettianProbability.API.ExactFiniteMainResults` may be directly imported.
Never import upstream internals or duplicate upstream definitions. Check every
signature in `.lake/packages/everettian_probability`, then in a minimal Lean
file.

### Absolute rules

Undischarged declarations, `native_decide`, and unlimited heartbeats are
forbidden in local Lean code. Never silently weaken a statement; signature
changes need a dedicated commit and report. The open-goal budget is zero, and
any future exception needs the immediately preceding `-- SATISFIABILITY:`
annotation. Every premise structure receives positive and negative witnesses
in matching `Nonvacuity.lean` and `NonTriviality.lean` files. Names must
not claim physics beyond their signatures; proximity, denominators,
quasi-commutation, physical models, and tensor factors must stay explicit.
Run the build, guard, and diff check before atomic commits. No dependency
update, force push, GitHub setting change, tag, release, or push without
explicit authorization. Documentation and module docstrings are bilingual.
Stop after 20–30 minutes on a resistant goal and report exact evidence.

### Lean anti-slowness conventions

Prefer `simp only`, use `generalize` after large substitutions, keep
`private` lemmas at minimal context, restructure rather than blindly raising
heartbeats, inspect the exact goal, and verify upstream signatures.

### Scope and Git

ED0 proves no local result about decoherence, robustness, approximate record
preservation, time evolution, open systems, preferred bases, personal identity,
Born, or rationality. Use `main`; allowed commit prefixes are `feat`,
`fix`, `audit`, `docs`, and `chore`. No force push, tag deletion, or
release without human instruction.

### ED2B terminology

**FR.** « Dimension-free » signifie seulement indépendant du nombre de
cellules, jamais une dimension de Hilbert arbitraire. Toute suppression de
cardinalité doit employer une identité globale de décomposition. Aucune
optimalité sans théorème dédié ; une borne `bornRecord` n'est pas décohérence.

**EN.** “Dimension-free” means only independent of cell count, never arbitrary
Hilbert dimension. Removing cardinality must use a global decomposition
identity. No optimality is claimed without a dedicated theorem, and a
`bornRecord` bound is not decoherence.

### ED1 logical firewall

ED1 is a BORN-SENSITIVE quantitative transfer layer: generic mathematics →
explicit dynamics → algebraic decoherence → record stability → Born-sensitive
transfer → conditional decision consequences. No future dynamical theorem may
hide credences, likelihoods, or rationality assumptions.

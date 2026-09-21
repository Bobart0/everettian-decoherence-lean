# Changelog

## Français

### [Unreleased]

- Aucun changement depuis la release archivale v0.1.0.

### [0.1.0] - 2026-09-21

#### Infrastructure

- harnais d'agent ;
- dépendance amont épinglée (`everettian-probability-lean v2.0.0`) ;
- contrat Lean de l'API amont ;
- gardes ;
- CI.

#### Metrics

- ED1 : géométrie L1 finie, profil bornien `recordProfileL1`, équivalence
  distance nulle/`SameRecord`, annulation sur orbite unitaire exacte ;
- ED2A : borne état-vers-record avec facteur de cardinalité ;
- ED2B : Cauchy--Schwarz fini, identité de Pythagore globale, borne sans
  facteur de cardinalité, constante 2 pour les états normalisés.

#### Approximation

- ED3A : commutateurs de projecteurs algébriques, défaut statewise L2, cas
  identité, transfert BORN-SENSITIVE vers `recordProfileL1`, cas normalisé,
  limite exacte vers `SameRecord` en un état ;
- ED3B : commutateurs continus (`ContinuousLinearMap`), normes d'opérateur,
  agrégation L2 uniforme sur les états, contrôle du défaut statewise, borne
  uniforme du profil BORN-SENSITIVE, cas normalisé, défaut uniforme nul
  équivalent à la commutation globale, `SameRecord` pour tout état, audits
  d'axiomes ;
- ED4A/ED4B : composition à perspective fixée et accumulation sur une liste
  finie de transformations ;
- T5A/T5B : constante optimale exacte `sqrt 2` pour le transfert uniforme ;
- front post-T5 : enveloppe des cuts, rigidité exacte à deux cellules, module
  de stabilité v12 avec constante finie `18`, coefficient asymptotique
  général `8`, coefficient ultra-near `4`, et famille continue
  bidimensionnelle réalisée dans `ℂ^3`, avec interpolation
  `4 / max{x,1-x}`.

Aucune dynamique temporelle, aucune décohérence et aucune API stable locale
ne sont introduites.

## English

### [Unreleased]

- No changes since archival release v0.1.0.

### [0.1.0] - 2026-09-21

#### Infrastructure

- agent harness;
- pinned upstream dependency (`everettian-probability-lean v2.0.0`);
- Lean contract for the upstream API;
- guards;
- CI.

#### Metrics

- ED1: finite L1 geometry, the Born-sensitive `recordProfileL1` profile,
  zero-distance/`SameRecord` equivalence, vanishing on the exact unitary
  orbit;
- ED2A: state-to-record bound with a cardinality factor;
- ED2B: finite Cauchy--Schwarz, the global Pythagorean identity, a bound
  without a cardinality factor, constant 2 for normalized states.

#### Approximation

- ED3A: algebraic projector commutators, statewise L2 defect, identity case,
  BORN-SENSITIVE transfer to `recordProfileL1`, normalized case, exact
  `SameRecord` limit at one state;
- ED3B: continuous commutators (`ContinuousLinearMap`), operator norms, an
  L2 aggregation uniform over states, control of the statewise defect, a
  uniform BORN-SENSITIVE profile bound, normalized case, zero uniform defect
  equivalent to global commutation, `SameRecord` for every state, axiom
  audits;
- ED4A/ED4B: fixed-perspective composition and accumulation over a finite list
  of transformations;
- T5A/T5B: exact optimal `sqrt 2` constant for the uniform transfer;
- post-T5 front: cut envelope, exact two-cell rigidity, the v12 finite
  coefficient `18`, general asymptotic coefficient `8`, ultra-near
  coefficient `4`, and a continuous two-parameter `ℂ^3` realization
  interpolating `4 / max{x,1-x}`.

No time dynamics, no decoherence, and no stable local API are introduced.

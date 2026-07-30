# Scope and limitations

## Français

### Formellement établis

- géométrie L1 des profils finis (ED1) ;
- continuité état-vers-record (ED2A, ED2B) ;
- borne sans facteur de cardinalité (ED2B) ;
- défaut statewise de commutation de projecteurs (ED3A) ;
- défaut uniforme par norme d'opérateur (ED3B) ;
- transfert vers `recordProfileL1` pour les défauts statewise et uniforme
  (BORN-SENSITIVE) ;
- limite exacte : défaut nul équivalent à `SameRecord` (ED3A, ponctuel) ou à
  la commutation globale (ED3B, pour tout état).

### Non établis

- composition de transformations ;
- itération finie et accumulation d'erreurs ;
- dynamique temporelle ;
- Hamiltonien ;
- systèmes ouverts ;
- canaux ;
- états mixtes ;
- trace partielle ;
- suppression hors diagonale ;
- décohérence ;
- base préférée ;
- records redondants ;
- rationalité ;
- identité personnelle ;
- règle de Born (dérivation).

Aucun de ces résultats n'est promis par les étapes formalisées.

### Distinctions d'uniformité

- **uniformité sur les états** : établie par ED3B, pour une perspective `D`
  et une transformation `U` fixées (`operatorNormProjectorCommutatorL2 D U`
  ne dépend pas de `x`) ;
- **uniformité sur les perspectives** : non établie — la quantité ED3B dépend
  toujours de `D` ;
- **indépendance du nombre de cellules** : non établie pour l'agrégat
  d'opérateurs ED3B, contrairement à la borne état-vers-record ED2B qui est
  dimension-free au sens du nombre de cellules ;
- **stabilité temporelle** : non établie — aucune dynamique n'est formalisée.

## English

### Formally established

- L1 geometry of finite profiles (ED1);
- state-to-record continuity (ED2A, ED2B);
- bound without a cardinality factor (ED2B);
- statewise projector-commutation defect (ED3A);
- uniform operator-norm defect (ED3B);
- transfer to `recordProfileL1` for both the statewise and uniform defects
  (BORN-SENSITIVE);
- exact limit: zero defect equivalent to `SameRecord` (ED3A, pointwise) or to
  global commutation (ED3B, for every state).

### Not established

- composition of transformations;
- finite iteration and error accumulation;
- time dynamics;
- Hamiltonian;
- open systems;
- channels;
- mixed states;
- partial trace;
- off-diagonal suppression;
- decoherence;
- preferred basis;
- redundant records;
- rationality;
- personal identity;
- derivation of the Born rule.

None of these results is promised by the formalized stages.

### Uniformity distinctions

- **uniformity over states**: established by ED3B, for a fixed perspective
  `D` and transformation `U` (`operatorNormProjectorCommutatorL2 D U` does
  not depend on `x`);
- **uniformity over perspectives**: not established — the ED3B quantity
  always depends on `D`;
- **cell-count independence**: not established for the ED3B operator
  aggregate, unlike the ED2B state-to-record bound, which is dimension-free
  in the sense of cell count;
- **temporal stability**: not established — no dynamics is formalized.

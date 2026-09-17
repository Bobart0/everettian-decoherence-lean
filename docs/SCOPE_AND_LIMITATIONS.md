# Scope and limitations

## Français

### Formellement établis

- géométrie L1 des profils finis (ED1) ;
- continuité état-vers-record (ED2A, ED2B) ;
- borne sans facteur de cardinalité (ED2B) ;
- défaut statewise de commutation de projecteurs (ED3A) ;
- défaut uniforme par norme d'opérateur (ED3B) ;
- composition finie de deux transformations à perspective fixée, avec borne
  sous-additive du défaut uniforme (ED4A) ;
- composition d'une liste finie de transformations et accumulation additive
  des défauts uniformes (ED4B) ;
- transfert vers `recordProfileL1` pour les défauts statewise, uniforme,
  composé et itéré (BORN-SENSITIVE) ;
- limite exacte : défaut nul équivalent à `SameRecord` (ED3A, ponctuel) ou à
  la commutation globale (ED3B, pour tout état), avec stabilité de cette
  propriété sous les compositions ED4A et ED4B lorsque chaque défaut
  élémentaire est nul.

Les résultats ED4A et ED4B sont formalisés et audités. Aucun statut de
publication supplémentaire n'est affirmé ici.

### Non établis

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
- **uniformité sur les perspectives** : non établie — les quantités ED3B–ED4B
  dépendent toujours de `D` ;
- **indépendance du nombre de cellules** : non établie pour les agrégats
  d'opérateurs ED3B–ED4B, contrairement à la borne état-vers-record ED2B qui
  est dimension-free au sens du nombre de cellules ;
- **stabilité temporelle** : non établie — ED4A et ED4B décrivent des
  compositions algébriques finies, pas une dynamique temporelle.

Toute quantité passant par `bornRecord`, notamment les transferts vers
`recordProfileL1`, reste explicitement **BORN-SENSITIVE**. Les défauts de
commutateur et leurs bornes de composition/itération sont algébriques et ne
constituent ni une décohérence physique ni une émergence de perspective.

## English

### Formally established

- L1 geometry of finite profiles (ED1);
- state-to-record continuity (ED2A, ED2B);
- bound without a cardinality factor (ED2B);
- statewise projector-commutation defect (ED3A);
- uniform operator-norm defect (ED3B);
- finite composition of two transformations at a fixed perspective, with a
  subadditive uniform-defect bound (ED4A);
- composition of a finite list of transformations and additive accumulation
  of uniform defects (ED4B);
- transfer to `recordProfileL1` for statewise, uniform, composed, and iterated
  defects (BORN-SENSITIVE);
- exact limit: zero defect equivalent to `SameRecord` (ED3A, pointwise) or to
  global commutation (ED3B, for every state), with this property preserved by
  ED4A and ED4B compositions when every elementary defect is zero.

The ED4A and ED4B results are formalized and audited. No additional
publication status is asserted here.

### Not established

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
- **uniformity over perspectives**: not established — the ED3B–ED4B
  quantities still depend on `D`;
- **cell-count independence**: not established for the ED3B–ED4B operator
  aggregates, unlike the ED2B state-to-record bound, which is dimension-free
  in the sense of cell count;
- **temporal stability**: not established — ED4A and ED4B describe finite
  algebraic compositions, not time dynamics.

Every quantity passing through `bornRecord`, including transfers to
`recordProfileL1`, remains explicitly **BORN-SENSITIVE**. The commutator
defects and their composition/iteration bounds are algebraic and constitute
neither physical decoherence nor perspective emergence.

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
- contrôle direct NON BORN-SENSITIVE de la structure projective : pour chaque
  cellule, l'écart en norme d'opérateur entre le projecteur transporté
  `U P_c U⁻¹` et le projecteur original `P_c` est majoré par le défaut de
  commutation correspondant ; l'agrégat L2 de ces écarts est majoré par
  `operatorNormProjectorCommutatorL2` (T1) ;
- transfert vers `recordProfileL1` pour les défauts statewise, uniforme,
  composé et itéré (BORN-SENSITIVE) ;
- limite exacte : défaut nul équivalent à `SameRecord` (ED3A, ponctuel) ou à
  la commutation globale (ED3B, pour tout état), avec stabilité de cette
  propriété sous les compositions ED4A et ED4B lorsque chaque défaut
  élémentaire est nul.

Les résultats ED4A, ED4B et le contrôle T1 sont formalisés et audités. Aucun
statut de publication supplémentaire n'est affirmé ici.

### Formalisé mais validation de compilation en attente

- **T2 — `DimensionFreeSharpness` (BORN-SENSITIVE)** : le code présent sur
  `main` construit une famille rationnelle explicite d'états normalisés en
  dimension `2`, calcule le rapport `recordProfileL1 / ‖x-y‖`, énonce sa
  convergence vers `2` et le corollaire d'optimalité excluant toute constante
  universelle `K < 2`. Le module et son fichier d'audit ont été intégrés à la
  demande explicite de l'auteur avant vérification locale de compilation.
  Jusqu'à cette vérification, T2 n'est pas classé **AUDITED** ni **PUBLISHED**.

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
  et T1 dépendent toujours de `D` ;
- **indépendance du nombre de cellules** : non établie pour les agrégats
  d'opérateurs ED3B–ED4B et T1, contrairement à la borne état-vers-record ED2B
  qui est dimension-free au sens du nombre de cellules ; T2 étudie la
  sharpness de la constante ED2B sur une perspective binaire fixe et ne change
  pas cette distinction ;
- **stabilité temporelle** : non établie — ED4A et ED4B décrivent des
  compositions algébriques finies, et T1 une comparaison de projecteurs, pas
  une dynamique temporelle.

Toute quantité passant par `bornRecord`, notamment les transferts vers
`recordProfileL1` et T2, reste explicitement **BORN-SENSITIVE**. Le contrôle T1
est explicitement **NON BORN-SENSITIVE** : il porte uniquement sur des
projecteurs, leur conjugaison par `U` et des normes d'opérateur. Les défauts de
commutateur, leurs bornes de composition/itération et T1 sont algébriques et ne
constituent ni une décohérence physique ni une émergence de perspective. T2 ne
constitue pas davantage une définition ou une dérivation de décohérence ; il
porte uniquement sur l'optimalité métrique d'une borne BORN-SENSITIVE.

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
- direct NON BORN-SENSITIVE projector-structure control: for each cell, the
  operator-norm displacement between the transported projector `U P_c U⁻¹`
  and the original projector `P_c` is bounded by the corresponding
  commutator defect, and the L2 aggregate of these displacements is bounded by
  `operatorNormProjectorCommutatorL2` (T1);
- transfer to `recordProfileL1` for statewise, uniform, composed, and iterated
  defects (BORN-SENSITIVE);
- exact limit: zero defect equivalent to `SameRecord` (ED3A, pointwise) or to
  global commutation (ED3B, for every state), with this property preserved by
  ED4A and ED4B compositions when every elementary defect is zero.

The ED4A, ED4B, and T1 results are formalized and audited. No additional
publication status is asserted here.

### Formalized but awaiting compile verification

- **T2 — `DimensionFreeSharpness` (BORN-SENSITIVE)**: the code present on
  `main` builds an explicit rational family of normalized states in dimension
  `2`, computes the `recordProfileL1 / ‖x-y‖` ratio, states convergence to `2`,
  and the sharpness corollary excluding every universal constant `K < 2`. The
  module and its audit file were integrated at the author's explicit request
  before local compilation verification. Until that check, T2 is classified
  as neither **AUDITED** nor **PUBLISHED**.

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
- **uniformity over perspectives**: not established — the ED3B–ED4B and T1
  quantities still depend on `D`;
- **cell-count independence**: not established for the ED3B–ED4B and T1
  operator aggregates, unlike the ED2B state-to-record bound, which is
  dimension-free in the sense of cell count; T2 studies sharpness of the ED2B
  constant on one fixed binary perspective and does not alter that distinction;
- **temporal stability**: not established — ED4A and ED4B describe finite
  algebraic compositions, and T1 compares projectors; none is time dynamics.

Every quantity passing through `bornRecord`, including transfers to
`recordProfileL1` and T2, remains explicitly **BORN-SENSITIVE**. T1 is
explicitly **NON BORN-SENSITIVE**: it uses only projectors, conjugation by `U`,
and operator norms. The commutator defects, their composition/iteration
bounds, and T1 are algebraic and constitute neither physical decoherence nor
perspective emergence. T2 likewise defines or derives no decoherence notion;
it concerns only metric sharpness of a BORN-SENSITIVE bound.

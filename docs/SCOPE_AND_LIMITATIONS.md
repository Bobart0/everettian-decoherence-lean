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
- **T2 — `DimensionFreeSharpness` (BORN-SENSITIVE)** : famille rationnelle
  explicite d'états normalisés en dimension `2`, calcul exact du rapport
  `recordProfileL1 / ‖x-y‖`, convergence de ce rapport vers `2`, et corollaire
  excluant toute constante universelle `K < 2` dans la borne normalisée ED2B ;
- **T3 — `IterationSharpness` (NON BORN-SENSITIVE)** : famille explicite de
  deux rotations rationnelles identiques sur la perspective binaire fixe,
  calcul exact du défaut du composé et de la somme ED4B, identité du ratio
  composé/somme avec `iterationSharpnessC`, convergence de ce ratio vers `1`,
  et corollaire excluant tout coefficient uniforme `K < 1` devant la somme
  additive ED4B, déjà pour des listes de longueur deux ;
- transfert vers `recordProfileL1` pour les défauts statewise, uniforme,
  composé et itéré (BORN-SENSITIVE) ;
- limite exacte : défaut nul équivalent à `SameRecord` (ED3A, ponctuel) ou à
  la commutation globale (ED3B, pour tout état), avec stabilité de cette
  propriété sous les compositions ED4A et ED4B lorsque chaque défaut
  élémentaire est nul.

Les résultats ED4A, ED4B, T1, T2 et T3 sont formalisés et audités. Aucun
statut de publication supplémentaire n'est affirmé ici.

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
- **uniformité sur les perspectives** : non établie — les quantités ED3B–ED4B,
  T1 et T3 dépendent toujours d'une perspective fournie ;
- **indépendance du nombre de cellules** : non établie pour les agrégats
  d'opérateurs ED3B–ED4B, T1 et T3, contrairement à la borne état-vers-record
  ED2B qui est dimension-free au sens du nombre de cellules ; T2 étudie la
  sharpness de la constante ED2B sur une perspective binaire fixe et T3 la
  sharpness du coefficient additif ED4B sur cette même géométrie binaire ;
- **stabilité temporelle** : non établie — ED4A et ED4B décrivent des
  compositions algébriques finies, T1 une comparaison de projecteurs, et T3
  une famille algébrique de deux compositions ; aucune de ces constructions
  n'est une dynamique temporelle.

Toute quantité passant par `bornRecord`, notamment les transferts vers
`recordProfileL1` et T2, reste explicitement **BORN-SENSITIVE**. Les contrôles
T1 et T3 sont explicitement **NON BORN-SENSITIVE** : ils portent uniquement
sur des projecteurs, transformations linéaires isométriques et normes
d'opérateur. Les défauts de commutateur, leurs bornes de composition/itération,
T1 et T3 sont algébriques et ne constituent ni une décohérence physique ni une
émergence de perspective. T2 ne constitue pas davantage une définition ou une
dérivation de décohérence ; il porte uniquement sur l'optimalité métrique d'une
borne BORN-SENSITIVE.

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
- **T2 — `DimensionFreeSharpness` (BORN-SENSITIVE)**: an explicit rational
  family of normalized states in dimension `2`, exact calculation of the
  `recordProfileL1 / ‖x-y‖` ratio, convergence of that ratio to `2`, and the
  corollary excluding every universal constant `K < 2` in the normalized ED2B
  bound;
- **T3 — `IterationSharpness` (NON BORN-SENSITIVE)**: an explicit family of
  two identical rational rotations on the fixed binary perspective, exact
  calculation of the composite defect and ED4B sum, identification of the
  composite/sum ratio with `iterationSharpnessC`, convergence of that ratio to
  `1`, and the corollary excluding every uniform coefficient `K < 1` in front
  of the ED4B additive sum, already for lists of length two;
- transfer to `recordProfileL1` for statewise, uniform, composed, and iterated
  defects (BORN-SENSITIVE);
- exact limit: zero defect equivalent to `SameRecord` (ED3A, pointwise) or to
  global commutation (ED3B, for every state), with this property preserved by
  ED4A and ED4B compositions when every elementary defect is zero.

The ED4A, ED4B, T1, T2, and T3 results are formalized and audited. No
additional publication status is asserted here.

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
- **uniformity over perspectives**: not established — the ED3B–ED4B, T1, and
  T3 quantities still depend on a supplied perspective;
- **cell-count independence**: not established for the ED3B–ED4B, T1, and T3
  operator aggregates, unlike the ED2B state-to-record bound, which is
  dimension-free in the sense of cell count; T2 studies sharpness of the ED2B
  constant on one fixed binary perspective, and T3 studies sharpness of the
  ED4B additive coefficient on that same binary geometry;
- **temporal stability**: not established — ED4A and ED4B describe finite
  algebraic compositions, T1 compares projectors, and T3 uses an algebraic
  family of two compositions; none is time dynamics.

Every quantity passing through `bornRecord`, including transfers to
`recordProfileL1` and T2, remains explicitly **BORN-SENSITIVE**. T1 and T3 are
explicitly **NON BORN-SENSITIVE**: they use only projectors, linear-isometric
transformations, and operator norms. The commutator defects, their
composition/iteration bounds, T1, and T3 are algebraic and constitute neither
physical decoherence nor perspective emergence. T2 likewise defines or
derives no decoherence notion; it concerns only metric sharpness of a
BORN-SENSITIVE bound.

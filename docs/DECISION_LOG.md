# Decision log

## Français

- **D0001 — Separate downstream repository** : isoler le programme
  approximatif et dynamique du dépôt exact. Motif : ne pas mélanger les
  garanties exactes amont avec des couches approchées. Portée : ce dépôt
  seul ; aucune modification amont.
- **D0002 — Stable upstream facades only** : n'importer que
  `ConditionalMainResults` et `ExactFiniteMainResults`. Motif : empêcher les
  dépendances internes fragiles. Portée : exclut tout import interne amont.
- **D0003 — Zero open-goal budget** : `SORRY_BUDGET = 0`. Motif : partir d'un
  socle sans dette formelle. Portée : toute exception future exige une
  annotation `-- SATISFIABILITY:`.
- **D0004 — No scientific roadmap at bootstrap** : ne pas figer la feuille de
  route physique à ED0. Motif : soumettre ED1 à un audit d'architecture
  séparé. Portée : ED0 seulement.
- **D0005 — Ambitious staged physical programme** : viser une chaîne
  explicite allant des dynamiques à la décohérence puis aux records et au
  transfert quantitatif. Motif : structurer le programme conditionnel
  ED1–ED12. Portée : aucune étape n'est ouverte par cette seule décision.
- **D0006 — Born-sensitive transfer separated from decoherence** : toute
  quantité utilisant `bornRecord` appartient au transfert, pas à une
  définition autonome. Motif : éviter de confondre proximité de profil et
  décohérence physique. Portée : s'applique à ED1 et à toutes les étapes
  ultérieures utilisant `bornRecord`.
- **D0007 — ED1 begins with finite profile geometry** : commencer par une
  géométrie finie auditée avant tout modèle dynamique. Motif : disposer d'une
  base métrique solide avant la physique. Portée : ED1 seulement.
- **D0008 — Coarse explicit bound before global sharpening** : ED2A prouve
  d'abord une borne élémentaire avec facteur de cardinalité
  `recordCellCount` avant toute borne globale. Motif : disposer d'une preuve
  coordonnée simple et auditée servant de base de comparaison. Portée : ED2A
  seulement ; ED2B affine ensuite cette borne sans la remplacer.
- **D0009 — Use global orthogonality to remove the cell-count factor** :
  renforcer ED2A par Cauchy--Schwarz et Pythagore pour obtenir une borne
  uniforme sur la perspective finie. Motif : obtenir une borne plus
  informative dès que le nombre de cellules dépasse un. Portée : ED2B
  seulement ; ED2A reste correct et disponible.
- **D0010 — "Dimension-free" means cell-count independent** : ED2B ne
  revendique aucune extension aux espaces de Hilbert de dimension infinie.
  Motif : éviter toute confusion terminologique. Portée : s'applique à tout
  usage futur du terme « dimension-free ».
- **D0011 — No optimality claim** : la constante normalisée 2 suffit, sans
  étude de saturation ni preuve de meilleure constante. Motif : limiter la
  portée d'ED2B à ce qui est effectivement démontré. Portée : ED2B seulement.
- **D0012 — Statewise commutator before operator norm** : ED3A prouve d'abord
  un défaut de commutation relatif à un état avant toute norme d'opérateur.
  Motif : disposer d'un résultat algébrique simple avant la généralisation
  uniforme. Portée : ED3A seulement ; ED3B généralise ensuite sans remplacer
  ED3A.
- **D0013 — Algebraic defect separated from Born transfer** : le commutateur
  de projecteurs est défini sans `bornRecord`; son transfert vers
  `recordProfileL1` est une étape séparée et BORN-SENSITIVE. Motif : préserver
  la distinction entre quasi-commutation algébrique et interprétation
  bornienne. Portée : ED3A et ED3B.
- **D0014 — Supplied perspective is not emergent** : la perspective `D`
  utilisée par ED3A et ED3B reste une donnée fournie, jamais un résultat.
  Motif : empêcher toute lecture d'émergence de base préférée. Portée : ED3A,
  ED3B, et toute étape future les réutilisant.
- **D0015 — L2 aggregate of per-cell operator norms** : `operatorNormProjectorCommutatorL2`
  agrège par une somme L2 les normes d'opérateur par cellule, plutôt qu'un
  maximum ou une autre norme. Motif : rester cohérent avec l'agrégation L2
  déjà utilisée en ED1–ED3A. Portée : ED3B seulement ; aucune optimalité de ce
  choix d'agrégation n'est revendiquée.
- **D0016 — Uniform means state-independent** : le mot « uniforme » dans
  `operatorNormProjectorCommutatorL2` signifie uniquement indépendant de
  l'état, pour `D` et `U` fixés. Motif : éviter toute confusion avec une
  uniformité sur les perspectives ou sur le nombre de cellules. Portée :
  s'applique à tout usage futur du terme « uniforme » en ED3B.
- **D0017 — No cell-count-independence claim for the operator aggregate** :
  contrairement à ED2B, l'agrégat ED3B peut dépendre du nombre de cellules de
  `D`. Motif : aucune identité de type Pythagore n'est utilisée pour
  supprimer cette dépendance ici. Portée : ED3B seulement.
- **D0018 — Exact zero characterizes global projector commutation** : un
  défaut uniforme nul équivaut à `∀ c, perspectiveProjectorCommutator D U c = 0`,
  et implique `∀ x, SameRecord D (U x) x`. Motif : offrir une limite exacte et
  vérifiable au résultat d'approximation. Portée : ED3B seulement ; ne
  constitue ni une décohérence ni une émergence de perspective.

## English

- **D0001 — Separate downstream repository**: isolate the approximate and
  dynamic program from the exact repository. Reason: avoid mixing exact
  upstream guarantees with approximate layers. Scope: this repository only;
  no upstream modification.
- **D0002 — Stable upstream facades only**: import only
  `ConditionalMainResults` and `ExactFiniteMainResults`. Reason: prevent
  fragile internal dependencies. Scope: excludes any upstream internal
  import.
- **D0003 — Zero open-goal budget**: `SORRY_BUDGET = 0`. Reason: begin
  without formal debt. Scope: any future exception requires a
  `-- SATISFIABILITY:` annotation.
- **D0004 — No scientific roadmap at bootstrap**: do not fix the physical
  roadmap at ED0. Reason: subject ED1 to a separate architecture audit.
  Scope: ED0 only.
- **D0005 — Ambitious staged physical programme**: target an explicit chain
  from dynamics through decoherence to records and quantitative transfer.
  Reason: structure the conditional ED1–ED12 programme. Scope: no stage is
  opened by this decision alone.
- **D0006 — Born-sensitive transfer separated from decoherence**: any
  `bornRecord` quantity belongs to transfer, not to a stand-alone definition.
  Reason: avoid conflating profile proximity with physical decoherence.
  Scope: applies to ED1 and to every later stage using `bornRecord`.
- **D0007 — ED1 begins with finite profile geometry**: begin with audited
  finite geometry before dynamical models. Reason: secure a solid metric
  base before physics. Scope: ED1 only.
- **D0008 — Coarse explicit bound before global sharpening**: ED2A first
  proves an elementary bound with the `recordCellCount` cardinality factor
  before any global bound. Reason: have a simple, audited coordinatewise
  proof as a comparison baseline. Scope: ED2A only; ED2B later sharpens this
  bound without replacing it.
- **D0009 — Use global orthogonality to remove the cell-count factor**:
  strengthen ED2A through Cauchy--Schwarz and Pythagoras to obtain a uniform
  finite-perspective bound. Reason: obtain a more informative bound once
  there is more than one cell. Scope: ED2B only; ED2A remains correct and
  available.
- **D0010 — "Dimension-free" means cell-count independent**: ED2B does not
  claim any extension to infinite Hilbert-space dimension. Reason: avoid
  terminological confusion. Scope: applies to every future use of
  "dimension-free".
- **D0011 — No optimality claim**: normalized constant 2 is sufficient,
  without a saturation study or best-constant proof. Reason: keep ED2B's
  scope to what is actually proved. Scope: ED2B only.
- **D0012 — Statewise commutator before operator norm**: ED3A first proves a
  state-relative commutation defect before any operator norm. Reason: have a
  simple algebraic result before the uniform generalization. Scope: ED3A
  only; ED3B later generalizes without replacing ED3A.
- **D0013 — Algebraic defect separated from Born transfer**: the projector
  commutator is defined without `bornRecord`; its transfer to
  `recordProfileL1` is a separate, BORN-SENSITIVE step. Reason: preserve the
  distinction between algebraic quasi-commutation and Born-sensitive
  interpretation. Scope: ED3A and ED3B.
- **D0014 — Supplied perspective is not emergent**: the perspective `D` used
  by ED3A and ED3B remains a supplied given, never a result. Reason: prevent
  any reading of emergent preferred-basis selection. Scope: ED3A, ED3B, and
  any future stage reusing them.
- **D0015 — L2 aggregate of per-cell operator norms**:
  `operatorNormProjectorCommutatorL2` aggregates per-cell operator norms by
  an L2 sum, rather than a maximum or another norm. Reason: stay consistent
  with the L2 aggregation already used in ED1–ED3A. Scope: ED3B only; no
  optimality of this aggregation choice is claimed.
- **D0016 — Uniform means state-independent**: the word "uniform" in
  `operatorNormProjectorCommutatorL2` means only independent of the state,
  for fixed `D` and `U`. Reason: avoid confusion with uniformity over
  perspectives or over cell count. Scope: applies to every future use of
  "uniform" in ED3B.
- **D0017 — No cell-count-independence claim for the operator aggregate**:
  unlike ED2B, the ED3B aggregate may depend on the cell count of `D`.
  Reason: no Pythagorean-type identity is used here to remove that
  dependence. Scope: ED3B only.
- **D0018 — Exact zero characterizes global projector commutation**: a zero
  uniform defect is equivalent to `∀ c, perspectiveProjectorCommutator D U c = 0`,
  and implies `∀ x, SameRecord D (U x) x`. Reason: offer an exact, checkable
  limit to the approximation result. Scope: ED3B only; it is neither
  decoherence nor perspective emergence.

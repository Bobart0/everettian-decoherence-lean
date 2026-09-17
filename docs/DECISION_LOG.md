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
- **D0019 — Reconcile documented status with existing ED4 formalization** :
  ED4A et ED4B sont reclassés comme jalons clos dans leur portée finie réelle,
  car les modules de composition/itération et leurs audits existent déjà.
  Motif : distinguer fidèlement prévu, formalisé, audité et publié. Portée :
  correction documentaire T0 uniquement ; aucune nouvelle preuve et aucune
  revendication de publication.
- **D0020 — Projector-structure control remains non-Born-sensitive** : T1
  encode le projecteur transporté d'une cellule par conjugaison `U P_c U⁻¹`
  et compare directement ce projecteur à `P_c`; l'écart en norme d'opérateur,
  puis son agrégat L2, sont contrôlés par le défaut de commutation ED3B. Motif :
  obtenir un résultat de stabilité structurelle indépendant de `bornRecord`.
  Portée : résultat algébrique uniquement, sans dynamique, décohérence,
  émergence de perspective ni nouvelle prémisse.
- **D0021 — T2 sharpness code may be integrated before local compile verification only by explicit author request** :
  T2 utilise une famille rationnelle de type Pell en dimension `2` pour viser
  l'optimalité de la constante `2` de la borne ED2B. Le module reste
  BORN-SENSITIVE. À la demande explicite de l'auteur, le code et son audit sont
  poussés sur `main` avant la vérification locale de compilation afin qu'ils
  puissent être récupérés et testés sur son poste. Motif : permettre cette
  vérification sans présenter le résultat comme déjà audité. Portée : T2
  seulement ; tant que `lake build`, `guard.sh` et `validate.sh` n'ont pas
  réussi sur ce commit, le statut est FORMALIZED / NOT YET COMPILE-VERIFIED,
  et aucune revendication AUDITED ou PUBLISHED n'est autorisée.
- **D0022 — Two steps suffice to prove sharpness of the ED4B additive coefficient** :
  T3 utilise deux copies identiques de la rotation rationnelle `Uₙ` sur la
  perspective binaire fixe. Le défaut élémentaire L2 vaut `sqrt 2 * sₙ`, le
  défaut exact du composé vaut `sqrt 2 * (2 cₙ sₙ)`, et la somme additive ED4B
  vaut `2 * sqrt 2 * sₙ`; le ratio est donc exactement `cₙ`. La forme
  rationnelle `cₙ = 1 - 2/(pₙ^2+1)` et `pₙ → +∞` donnent un ratio tendant vers
  `1`, puis un contre-exemple explicite à tout coefficient uniforme `K < 1`.
  Motif : établir l'optimalité asymptotique de la constante additive sans
  ouvrir un formalisme général de puissances ni renforcer les hypothèses ED4B.
  Portée : résultat algébrique fini, dimension `2`, perspective fournie,
  listes de longueur deux ; **NON BORN-SENSITIVE**, sans temps, dynamique
  physique, décohérence, émergence de perspective ni revendication de
  publication.
- **D0023 — One exact qubit instance should expose both sides of the Born firewall** :
  T4 instancie au rang `n = 1` la rotation rationnelle déjà formalisée sur la
  perspective binaire fixe et l'état `e₀`. La matrice est exactement
  `[[24/25,-7/25],[7/25,24/25]]`; le défaut L2 uniforme vaut
  `7 * sqrt 2 / 25` et satisfait le certificat rationnel `≤ 2/5`, tandis que
  les poids borniens passent de `(1,0)` à `(576/625,49/625)`, le profil L1 réel
  vaut `98/625`, la borne rationnelle retenue vaut `4/5` et le gap vaut
  `402/625`. Motif : fournir un exemple calculé de bout en bout qui rende
  visible la séparation entre le défaut de commutateur **NON BORN-SENSITIVE**
  et son transfert profil/gap **BORN-SENSITIVE**, sans modifier aucun théorème
  ni hypothèse. Portée : calcul statique en dimension `2`, perspective fournie,
  aucun temps, Hamiltonien, canal, décohérence, base émergente ou statut de
  publication.

- **D0024 — T5A and T5B fix the optimal ED3B transfer coefficient at `sqrt 2`** :
  T5A fournit une famille normalisée explicite dont le ratio
  `recordProfileL1 / operatorNormProjectorCommutatorL2` vaut exactement
  `sqrt 2`. T5B utilise l'identité de variation totale, un projecteur agrégé
  sur les cellules de variation positive, la décomposition subset/complément
  et le partage quadratique du défaut pour établir la borne universelle
  correspondante. Leur combinaison prouve qu'un coefficient réel `K` est
  universel sur les états normalisés si et seulement si `sqrt 2 ≤ K`.
  Portée : perspectives finies fournies et unitaires fournis ; le défaut reste
  **NON BORN-SENSITIVE** tandis que le transfert de profil est
  **BORN-SENSITIVE**. Aucun temps, dynamique physique, décohérence, émergence
  de perspective ou statut de publication n'est revendiqué.

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
- **D0019 — Reconcile documented status with existing ED4 formalization**:
  ED4A and ED4B are reclassified as closed milestones in their actual finite
  scope because the composition/iteration modules and their audits already
  exist. Reason: faithfully distinguish planned, formalized, audited, and
  published material. Scope: T0 documentation correction only; no new proof
  and no publication claim.
- **D0020 — Projector-structure control remains non-Born-sensitive**: T1
  encodes a cell's transported projector by conjugation `U P_c U⁻¹` and
  compares it directly with `P_c`; the operator-norm displacement and then its
  L2 aggregate are controlled by the ED3B commutator defect. Reason: obtain a
  structural stability result independent of `bornRecord`. Scope: algebraic
  result only, with no dynamics, decoherence, perspective emergence, or new
  premise.
- **D0021 — T2 sharpness code may be integrated before local compile verification only by explicit author request**:
  T2 uses a Pell-type rational family in dimension `2` to target sharpness of
  the ED2B constant `2`. The module remains BORN-SENSITIVE. At the author's
  explicit request, the code and its audit are pushed to `main` before local
  compilation verification so they can be retrieved and tested on the
  author's workstation. Reason: enable that check without representing the
  result as already audited. Scope: T2 only; until `lake build`, `guard.sh`,
  and `validate.sh` succeed on this commit, the status is FORMALIZED / NOT YET
  COMPILE-VERIFIED, and no AUDITED or PUBLISHED claim is permitted.
- **D0022 — Two steps suffice to prove sharpness of the ED4B additive coefficient**:
  T3 uses two identical copies of the rational rotation `Uₙ` on the fixed
  binary perspective. The elementary L2 defect is `sqrt 2 * sₙ`, the exact
  composite defect is `sqrt 2 * (2 cₙ sₙ)`, and the ED4B additive sum is
  `2 * sqrt 2 * sₙ`; hence the ratio is exactly `cₙ`. The rational form
  `cₙ = 1 - 2/(pₙ^2+1)` together with `pₙ → +∞` makes this ratio tend to `1`,
  yielding an explicit counterexample to every uniform coefficient `K < 1`.
  Reason: establish asymptotic optimality of the additive constant without
  opening a general power formalism or strengthening the ED4B assumptions.
  Scope: finite algebraic result in dimension `2`, supplied perspective,
  length-two lists; **NON BORN-SENSITIVE**, with no time, physical dynamics,
  decoherence, perspective emergence, or publication claim.
- **D0023 — One exact qubit instance should expose both sides of the Born firewall**:
  T4 instantiates the already-formalized rational rotation at `n = 1` on the
  fixed binary perspective and state `e₀`. The matrix is exactly
  `[[24/25,-7/25],[7/25,24/25]]`; the uniform L2 defect is
  `7 * sqrt 2 / 25` with rational certificate `≤ 2/5`, while the Born weights
  move from `(1,0)` to `(576/625,49/625)`, the actual L1 profile is `98/625`,
  the chosen rational bound is `4/5`, and the gap is `402/625`. Reason: provide
  a fully worked end-to-end example that makes the separation between the
  **NON BORN-SENSITIVE** commutator defect and its **BORN-SENSITIVE**
  profile/gap transfer explicit, without changing any theorem or assumption.
  Scope: static dimension-`2` calculation, supplied perspective, no time,
  Hamiltonian, channel, decoherence, emergent basis, or publication claim.
- **D0024 — T5A and T5B fix the optimal ED3B transfer coefficient at `sqrt 2`**:
  T5A supplies an explicit normalized family whose
  `recordProfileL1 / operatorNormProjectorCommutatorL2` ratio is exactly
  `sqrt 2`. T5B uses the total-variation identity, an aggregate projector on
  the positive-variation cells, the subset/complement decomposition, and the
  quadratic split of the defect to prove the matching universal upper bound.
  Together they show that a real coefficient `K` is universal on normalized
  states if and only if `sqrt 2 ≤ K`. Scope: supplied finite perspectives
  and supplied unitaries; the defect remains **NON BORN-SENSITIVE** while the
  profile transfer is **BORN-SENSITIVE**. No time, physical dynamics,
  decoherence, perspective emergence, or publication status is claimed.

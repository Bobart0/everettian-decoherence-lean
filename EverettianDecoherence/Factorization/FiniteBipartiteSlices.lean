import EverettianDecoherence.Factorization.FiniteBipartiteFactorization

/-!
**FR.** Pour une factorisation `F` choisie et fournie, les tranches
bipartites sont de purs vecteurs de coordonnées : à indice système fixé, le
vecteur des coordonnées environnement, et symétriquement à indice
environnement fixé, le vecteur des coordonnées système. Les profils des
carrés de leurs normes sont des budgets quadratiques algébriques, sommant à
`‖x‖ ^ 2`. Ils ne sont ni des probabilités, ni des distributions, ni des
marginales probabilistes, ni des états réduits, ni des traces partielles.
Aucune mesure d'intrication, aucune opération locale, aucune dynamique et
aucune décohérence ne sont introduites. Aucun `bornRecord`,
`recordProfileL1` ou `SameRecord` n'apparaît.

**EN.** For a chosen, explicitly supplied factorization `F`, bipartite
slices are pure coordinate vectors: at a fixed system index, the vector of
environment coordinates, and symmetrically at a fixed environment index,
the vector of system coordinates. The profiles of their squared norms are
algebraic quadratic budgets, summing to `‖x‖ ^ 2`. They are neither
probabilities, distributions, probabilistic marginals, reduced states, nor
partial traces. No entanglement measure, local operation, dynamics, or
decoherence is introduced. No `bornRecord`, `recordProfileL1`, or
`SameRecord` appears.
-/

namespace EverettianDecoherence.Factorization

abbrev FiniteSystemCoordinateSpace (s : ℕ) :=
  EuclideanSpace ℂ (Fin s)

abbrev FiniteEnvironmentCoordinateSpace (e : ℕ) :=
  EuclideanSpace ℂ (Fin e)

noncomputable def environmentSliceAtSystemIndex
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e)
    (x : Gleason.H n)
    (i : Fin s) :
    FiniteEnvironmentCoordinateSpace e :=
  WithLp.toLp 2 (fun j => bipartiteCoordinate F x i j)

noncomputable def systemSliceAtEnvironmentIndex
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e)
    (x : Gleason.H n)
    (j : Fin e) :
    FiniteSystemCoordinateSpace s :=
  WithLp.toLp 2 (fun i => bipartiteCoordinate F x i j)

theorem environmentSliceAtSystemIndex_apply
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e)
    (x : Gleason.H n) (i : Fin s) (j : Fin e) :
    environmentSliceAtSystemIndex F x i j = bipartiteCoordinate F x i j :=
  rfl

theorem systemSliceAtEnvironmentIndex_apply
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e)
    (x : Gleason.H n) (j : Fin e) (i : Fin s) :
    systemSliceAtEnvironmentIndex F x j i = bipartiteCoordinate F x i j :=
  rfl

theorem environmentSliceAtSystemIndex_zero
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (i : Fin s) :
    environmentSliceAtSystemIndex F 0 i = 0 := by
  apply PiLp.ext
  intro j
  rw [environmentSliceAtSystemIndex_apply, bipartiteCoordinate_zero]
  rfl

theorem environmentSliceAtSystemIndex_add
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x y : Gleason.H n) (i : Fin s) :
    environmentSliceAtSystemIndex F (x + y) i =
      environmentSliceAtSystemIndex F x i + environmentSliceAtSystemIndex F y i := by
  apply PiLp.ext
  intro j
  rw [environmentSliceAtSystemIndex_apply, bipartiteCoordinate_add]
  rfl

theorem environmentSliceAtSystemIndex_smul
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (c : ℂ) (x : Gleason.H n) (i : Fin s) :
    environmentSliceAtSystemIndex F (c • x) i = c • environmentSliceAtSystemIndex F x i := by
  apply PiLp.ext
  intro j
  rw [environmentSliceAtSystemIndex_apply, bipartiteCoordinate_smul]
  rfl

theorem systemSliceAtEnvironmentIndex_zero
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (j : Fin e) :
    systemSliceAtEnvironmentIndex F 0 j = 0 := by
  apply PiLp.ext
  intro i
  rw [systemSliceAtEnvironmentIndex_apply, bipartiteCoordinate_zero]
  rfl

theorem systemSliceAtEnvironmentIndex_add
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x y : Gleason.H n) (j : Fin e) :
    systemSliceAtEnvironmentIndex F (x + y) j =
      systemSliceAtEnvironmentIndex F x j + systemSliceAtEnvironmentIndex F y j := by
  apply PiLp.ext
  intro i
  rw [systemSliceAtEnvironmentIndex_apply, bipartiteCoordinate_add]
  rfl

theorem systemSliceAtEnvironmentIndex_smul
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (c : ℂ) (x : Gleason.H n) (j : Fin e) :
    systemSliceAtEnvironmentIndex F (c • x) j = c • systemSliceAtEnvironmentIndex F x j := by
  apply PiLp.ext
  intro i
  rw [systemSliceAtEnvironmentIndex_apply, bipartiteCoordinate_smul]
  rfl

noncomputable def systemIndexSliceNormSqProfile
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e)
    (x : Gleason.H n) :
    Fin s → ℝ :=
  fun i => ‖environmentSliceAtSystemIndex F x i‖ ^ 2

noncomputable def environmentIndexSliceNormSqProfile
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e)
    (x : Gleason.H n) :
    Fin e → ℝ :=
  fun j => ‖systemSliceAtEnvironmentIndex F x j‖ ^ 2

theorem systemIndexSliceNormSqProfile_nonneg
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x : Gleason.H n) (i : Fin s) :
    0 ≤ systemIndexSliceNormSqProfile F x i :=
  sq_nonneg _

theorem environmentIndexSliceNormSqProfile_nonneg
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x : Gleason.H n) (j : Fin e) :
    0 ≤ environmentIndexSliceNormSqProfile F x j :=
  sq_nonneg _

theorem environmentSliceAtSystemIndex_norm_sq
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x : Gleason.H n) (i : Fin s) :
    ‖environmentSliceAtSystemIndex F x i‖ ^ 2 =
      ∑ j : Fin e, ‖bipartiteCoordinate F x i j‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

theorem systemSliceAtEnvironmentIndex_norm_sq
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x : Gleason.H n) (j : Fin e) :
    ‖systemSliceAtEnvironmentIndex F x j‖ ^ 2 =
      ∑ i : Fin s, ‖bipartiteCoordinate F x i j‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

theorem sum_systemIndexSliceNormSqProfile_eq_norm_sq
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x : Gleason.H n) :
    ∑ i : Fin s, systemIndexSliceNormSqProfile F x i = ‖x‖ ^ 2 := by
  unfold systemIndexSliceNormSqProfile
  simp_rw [environmentSliceAtSystemIndex_norm_sq]
  exact sum_sum_sq_bipartiteCoordinate_eq_norm_sq F x

theorem sum_environmentIndexSliceNormSqProfile_eq_norm_sq
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x : Gleason.H n) :
    ∑ j : Fin e, environmentIndexSliceNormSqProfile F x j = ‖x‖ ^ 2 := by
  unfold environmentIndexSliceNormSqProfile
  simp_rw [systemSliceAtEnvironmentIndex_norm_sq]
  rw [Finset.sum_comm]
  exact sum_sum_sq_bipartiteCoordinate_eq_norm_sq F x

theorem sum_systemIndexSliceNormSqProfile_eq_one_of_normalized
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x : Gleason.H n) (hx : ‖x‖ = 1) :
    ∑ i : Fin s, systemIndexSliceNormSqProfile F x i = 1 := by
  rw [sum_systemIndexSliceNormSqProfile_eq_norm_sq, hx]
  norm_num

theorem sum_environmentIndexSliceNormSqProfile_eq_one_of_normalized
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x : Gleason.H n) (hx : ‖x‖ = 1) :
    ∑ j : Fin e, environmentIndexSliceNormSqProfile F x j = 1 := by
  rw [sum_environmentIndexSliceNormSqProfile_eq_norm_sq, hx]
  norm_num

theorem eq_of_environmentSliceAtSystemIndex_eq
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x y : Gleason.H n)
    (h : ∀ i, environmentSliceAtSystemIndex F x i = environmentSliceAtSystemIndex F y i) :
    x = y := by
  apply eq_of_bipartiteCoordinate_eq F x y
  intro i j
  have hij := congrArg (fun v => v j) (h i)
  simpa [environmentSliceAtSystemIndex_apply] using hij

theorem eq_of_systemSliceAtEnvironmentIndex_eq
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x y : Gleason.H n)
    (h : ∀ j, systemSliceAtEnvironmentIndex F x j = systemSliceAtEnvironmentIndex F y j) :
    x = y := by
  apply eq_of_bipartiteCoordinate_eq F x y
  intro i j
  have hij := congrArg (fun v => v i) (h j)
  simpa [systemSliceAtEnvironmentIndex_apply] using hij

end EverettianDecoherence.Factorization

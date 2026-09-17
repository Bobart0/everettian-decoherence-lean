import EverettianDecoherence.Metrics.FiniteL2Comparison
import EverettianDecoherence.Approximation.ProjectorCommutator

/-!
**FR.** Couche algébrique sans `bornRecord` ni `recordProfileL1` : normes
d'opérateur des commutateurs d'une perspective fournie, uniformes sur les états
mais non sur les perspectives. Aucune dynamique ni décohérence n'est formalisée.

**EN.** Algebraic layer without `bornRecord` or `recordProfileL1`: operator
norms of supplied-perspective commutators, uniform over states but not over
perspectives. No dynamics or decoherence is formalized.
-/

namespace EverettianDecoherence.Approximation

noncomputable def perspectiveProjectorCommutatorCLM
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    Gleason.H n →L[ℂ] Gleason.H n :=
  (perspectiveProjectorCommutator D U c).toContinuousLinearMap

theorem perspectiveProjectorCommutatorCLM_apply
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D)
    (x : Gleason.H n) :
    perspectiveProjectorCommutatorCLM D U c x = perspectiveProjectorCommutator D U c x := rfl

theorem perspectiveProjectorCommutatorCLM_toLinearMap
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    (perspectiveProjectorCommutatorCLM D U c).toLinearMap = perspectiveProjectorCommutator D U c := rfl

noncomputable def perspectiveProjectorCommutatorOpNormProfile
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) :
    (EverettianProbability.Abstract.Projective.interface n).Cell D → ℝ :=
  fun c => ‖perspectiveProjectorCommutatorCLM D U c‖

noncomputable def operatorNormProjectorCommutatorL2
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) : ℝ :=
  EverettianDecoherence.Metrics.finiteL2 (perspectiveProjectorCommutatorOpNormProfile D U)

def operatorNormProjectorCommutatorWithin
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (ε : ℝ) : Prop :=
  operatorNormProjectorCommutatorL2 D U ≤ ε

theorem perspectiveProjectorCommutatorOpNormProfile_nonneg
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    0 ≤ perspectiveProjectorCommutatorOpNormProfile D U c :=
  ContinuousLinearMap.opNorm_nonneg _

theorem operatorNormProjectorCommutatorL2_nonneg
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) :
    0 ≤ operatorNormProjectorCommutatorL2 D U :=
  EverettianDecoherence.Metrics.finiteL2_nonneg _

theorem operatorNormProjectorCommutatorWithin_mono
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (ε δ : ℝ) :
    operatorNormProjectorCommutatorWithin D U ε → ε ≤ δ →
      operatorNormProjectorCommutatorWithin D U δ := by
  intro h hεδ
  exact h.trans hεδ

theorem perspectiveProjectorCommutatorNormProfile_le_opNorm_mul_norm
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    perspectiveProjectorCommutatorNormProfile D U x c ≤
      perspectiveProjectorCommutatorOpNormProfile D U c * ‖x‖ := by
  unfold perspectiveProjectorCommutatorNormProfile
    perspectiveProjectorCommutatorOpNormProfile
  rw [← perspectiveProjectorCommutatorCLM_apply]
  exact ContinuousLinearMap.le_opNorm _ _

theorem statewiseProjectorCommutatorL2_le_operatorNormProjectorCommutatorL2_mul_norm
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) :
    statewiseProjectorCommutatorL2 D U x ≤ operatorNormProjectorCommutatorL2 D U * ‖x‖ := by
  exact EverettianDecoherence.Metrics.finiteL2_le_mul_of_pointwise
    (perspectiveProjectorCommutatorNormProfile D U x)
    (perspectiveProjectorCommutatorOpNormProfile D U) ‖x‖
    (perspectiveProjectorCommutatorNormProfile_nonneg D U x)
    (perspectiveProjectorCommutatorOpNormProfile_nonneg D U) (norm_nonneg _)
    (perspectiveProjectorCommutatorNormProfile_le_opNorm_mul_norm D U x)

theorem perspectiveProjectorCommutatorCLM_refl
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    perspectiveProjectorCommutatorCLM D (LinearIsometryEquiv.refl ℂ (Gleason.H n)) c = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [perspectiveProjectorCommutatorCLM_apply, perspectiveProjectorCommutator_refl]
  rfl

theorem operatorNormProjectorCommutatorL2_eq_zero_of_global_commutation
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (h : ∀ c, perspectiveProjectorCommutator D U c = 0) :
    operatorNormProjectorCommutatorL2 D U = 0 := by
  unfold operatorNormProjectorCommutatorL2
  apply (EverettianDecoherence.Metrics.finiteL2_eq_zero_iff
    (perspectiveProjectorCommutatorOpNormProfile D U)
    (perspectiveProjectorCommutatorOpNormProfile_nonneg D U)).mpr
  intro c
  unfold perspectiveProjectorCommutatorOpNormProfile
  rw [show perspectiveProjectorCommutatorCLM D U c = 0 by
    apply ContinuousLinearMap.ext
    intro x
    rw [perspectiveProjectorCommutatorCLM_apply, h c]
    rfl]
  exact ContinuousLinearMap.opNorm_zero

theorem global_commutation_of_operatorNormProjectorCommutatorL2_eq_zero
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (h : operatorNormProjectorCommutatorL2 D U = 0) :
    ∀ c, perspectiveProjectorCommutator D U c = 0 := by
  have hz := (EverettianDecoherence.Metrics.finiteL2_eq_zero_iff
    (perspectiveProjectorCommutatorOpNormProfile D U)
    (perspectiveProjectorCommutatorOpNormProfile_nonneg D U)).mp h
  intro c
  rw [← perspectiveProjectorCommutatorCLM_toLinearMap]
  have hc : perspectiveProjectorCommutatorCLM D U c = 0 := norm_eq_zero.mp (hz c)
  simp [hc]

theorem operatorNormProjectorCommutatorL2_eq_zero_iff_global_commutation
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) :
    operatorNormProjectorCommutatorL2 D U = 0 ↔ ∀ c, perspectiveProjectorCommutator D U c = 0 :=
  ⟨global_commutation_of_operatorNormProjectorCommutatorL2_eq_zero D U,
    operatorNormProjectorCommutatorL2_eq_zero_of_global_commutation D U⟩

theorem operatorNormProjectorCommutatorL2_refl
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) :
    operatorNormProjectorCommutatorL2 D (LinearIsometryEquiv.refl ℂ (Gleason.H n)) = 0 :=
  operatorNormProjectorCommutatorL2_eq_zero_of_global_commutation D
    (LinearIsometryEquiv.refl ℂ (Gleason.H n))
    (fun c => perspectiveProjectorCommutator_refl D c)

theorem statewiseProjectorCommutatorWithin_of_operatorNormProjectorCommutatorWithin
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) (ε : ℝ)
    (h : operatorNormProjectorCommutatorWithin D U ε) :
    statewiseProjectorCommutatorWithin D U x (ε * ‖x‖) := by
  exact (statewiseProjectorCommutatorL2_le_operatorNormProjectorCommutatorL2_mul_norm D U x).trans
    (mul_le_mul_of_nonneg_right h (norm_nonneg _))

theorem statewiseProjectorCommutatorWithin_of_normalized_operatorNormWithin
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) (ε : ℝ)
    (hx : ‖x‖ = 1) (h : operatorNormProjectorCommutatorWithin D U ε) :
    statewiseProjectorCommutatorWithin D U x ε := by
  simpa [hx] using
    statewiseProjectorCommutatorWithin_of_operatorNormProjectorCommutatorWithin D U x ε h


/-- Applying the inverse unitary turns the inverse commutator into the original
commutator, up to an isometric image and a sign. -/
theorem perspectiveProjectorCommutator_symm_apply
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D)
    (y : Gleason.H n) :
    perspectiveProjectorCommutator D U.symm c y =
      - U.symm (perspectiveProjectorCommutator D U c (U.symm y)) := by
  rw [perspectiveProjectorCommutator_apply, perspectiveProjectorCommutator_apply]
  simp [map_sub]

/-- One-sided operator-norm comparison under inversion. Kept separate so
the reverse inequality can reuse the same argument without duplicating an
expensive elaboration. -/
theorem perspectiveProjectorCommutatorCLM_norm_symm_le
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    ‖perspectiveProjectorCommutatorCLM D U.symm c‖ ≤
      ‖perspectiveProjectorCommutatorCLM D U c‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
      (ContinuousLinearMap.opNorm_nonneg
        (perspectiveProjectorCommutatorCLM D U c))
  intro y
  rw [perspectiveProjectorCommutatorCLM_apply,
    perspectiveProjectorCommutator_symm_apply, norm_neg, U.symm.norm_map]
  calc
    ‖perspectiveProjectorCommutator D U c (U.symm y)‖ =
        ‖perspectiveProjectorCommutatorCLM D U c (U.symm y)‖ := rfl
    _ ≤ ‖perspectiveProjectorCommutatorCLM D U c‖ * ‖U.symm y‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖perspectiveProjectorCommutatorCLM D U c‖ * ‖y‖ := by
      rw [U.symm.norm_map]

/-- The operator norm of every cell commutator is invariant under replacing a
unitary by its inverse. -/
theorem perspectiveProjectorCommutatorCLM_norm_symm
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    ‖perspectiveProjectorCommutatorCLM D U.symm c‖ =
      ‖perspectiveProjectorCommutatorCLM D U c‖ := by
  apply le_antisymm
  · exact perspectiveProjectorCommutatorCLM_norm_symm_le D U c
  · simpa using perspectiveProjectorCommutatorCLM_norm_symm_le D U.symm c

/-- The cellwise operator-norm defect profile is invariant under inversion. -/
theorem perspectiveProjectorCommutatorOpNormProfile_symm
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    perspectiveProjectorCommutatorOpNormProfile D U.symm c =
      perspectiveProjectorCommutatorOpNormProfile D U c := by
  exact perspectiveProjectorCommutatorCLM_norm_symm D U c

end EverettianDecoherence.Approximation

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

end EverettianDecoherence.Approximation

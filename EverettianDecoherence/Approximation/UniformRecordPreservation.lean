import EverettianDecoherence.Approximation.OperatorNormProjectorCommutator
import EverettianDecoherence.Approximation.ApproximateRecordPreservation

/-!
**FR.** Le défaut uniforme est algébrique et sans `bornRecord`; son transfert
vers le profil est BORN-SENSITIVE, uniforme sur les états pour une perspective
fournie. Aucune dynamique ni décohérence n'est impliquée.

**EN.** The uniform defect is algebraic and contains no `bornRecord`; its
profile transfer is BORN-SENSITIVE and uniform over states for a supplied
perspective. No dynamics or decoherence is involved.
-/

namespace EverettianDecoherence.Approximation

noncomputable def uniformRecordPreservationBudget
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) : ℝ :=
  2 * ‖x‖ ^ 2 * operatorNormProjectorCommutatorL2 D U

theorem uniformRecordPreservationBudget_nonneg
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) :
    0 ≤ uniformRecordPreservationBudget D U x :=
  mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (operatorNormProjectorCommutatorL2_nonneg D U)

theorem recordProfileL1_unitary_le_two_mul_norm_sq_mul_operatorNormCommutatorL2
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) :
    EverettianDecoherence.Metrics.recordProfileL1 D (U x) x ≤
      2 * ‖x‖ ^ 2 * operatorNormProjectorCommutatorL2 D U := by
  calc
    EverettianDecoherence.Metrics.recordProfileL1 D (U x) x ≤
        2 * ‖x‖ * statewiseProjectorCommutatorL2 D U x :=
      recordProfileL1_unitary_le_two_mul_norm_mul_statewiseCommutatorL2 D U x
    _ ≤ 2 * ‖x‖ * (operatorNormProjectorCommutatorL2 D U * ‖x‖) :=
      mul_le_mul_of_nonneg_left
        (statewiseProjectorCommutatorL2_le_operatorNormProjectorCommutatorL2_mul_norm D U x)
        (mul_nonneg (by norm_num) (norm_nonneg _))
    _ = 2 * ‖x‖ ^ 2 * operatorNormProjectorCommutatorL2 D U := by ring

theorem recordProfileL1_unitary_le_uniformRecordPreservationBudget
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) :
    EverettianDecoherence.Metrics.recordProfileL1 D (U x) x ≤
      uniformRecordPreservationBudget D U x :=
  recordProfileL1_unitary_le_two_mul_norm_sq_mul_operatorNormCommutatorL2 D U x

theorem recordProfileL1_unitary_le_two_mul_operatorNormCommutatorL2
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) (hx : ‖x‖ = 1) :
    EverettianDecoherence.Metrics.recordProfileL1 D (U x) x ≤
      2 * operatorNormProjectorCommutatorL2 D U := by
  calc
    EverettianDecoherence.Metrics.recordProfileL1 D (U x) x ≤
        2 * ‖x‖ ^ 2 * operatorNormProjectorCommutatorL2 D U :=
      recordProfileL1_unitary_le_two_mul_norm_sq_mul_operatorNormCommutatorL2 D U x
    _ = 2 * operatorNormProjectorCommutatorL2 D U := by rw [hx]; ring

theorem recordProfileWithin_of_operatorNormProjectorCommutatorWithin
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) (ε : ℝ)
    (h : operatorNormProjectorCommutatorWithin D U ε) :
    EverettianDecoherence.Metrics.recordProfileWithin D (2 * ‖x‖ ^ 2 * ε) (U x) x := by
  unfold EverettianDecoherence.Metrics.recordProfileWithin
  exact (recordProfileL1_unitary_le_two_mul_norm_sq_mul_operatorNormCommutatorL2 D U x).trans
    (mul_le_mul_of_nonneg_left h (mul_nonneg (by norm_num) (sq_nonneg _)))

theorem recordProfileWithin_of_normalized_operatorNormProjectorCommutatorWithin
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) (ε : ℝ)
    (hx : ‖x‖ = 1) (h : operatorNormProjectorCommutatorWithin D U ε) :
    EverettianDecoherence.Metrics.recordProfileWithin D (2 * ε) (U x) x := by
  simpa [hx] using recordProfileWithin_of_operatorNormProjectorCommutatorWithin D U x ε h

theorem sameRecord_forall_of_operatorNormProjectorCommutatorL2_eq_zero
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (h : operatorNormProjectorCommutatorL2 D U = 0) :
    ∀ x, EverettianProbability.API.ExactFinite.SameRecord D (U x) x := by
  intro x
  exact sameRecord_of_exact_projector_commutation_at_state D U x
    (fun c => congrArg (fun T : Gleason.H n →ₗ[ℂ] Gleason.H n => T x)
      (global_commutation_of_operatorNormProjectorCommutatorL2_eq_zero D U h c))

end EverettianDecoherence.Approximation

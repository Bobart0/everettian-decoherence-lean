import EverettianDecoherence.Approximation.ProjectorCommutator
import EverettianDecoherence.Metrics.StateRecordDimensionFree

/-!
**FR.** Le défaut est algébrique et le transfert vers le profil est
BORN-SENSITIVE, pour une perspective, une transformation et un état fournis.
Ce résultat n'est ni uniforme en norme d'opérateur ni une décohérence.

**EN.** The defect is algebraic and transfer to the profile is BORN-SENSITIVE,
for a supplied perspective, transformation, and state. This is neither uniform
in operator norm nor decoherence.
-/

namespace EverettianDecoherence.Approximation

open scoped BigOperators

theorem abs_recordCellNormProfile_unitary_sub_le_commutator
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    |EverettianDecoherence.Metrics.recordCellNormProfile D (U x) c -
        EverettianDecoherence.Metrics.recordCellNormProfile D x c| ≤
      perspectiveProjectorCommutatorNormProfile D U x c := by
  unfold EverettianDecoherence.Metrics.recordCellNormProfile
    perspectiveProjectorCommutatorNormProfile
  rw [perspectiveProjectorCommutator_apply, ← U.norm_map (Gleason.projL c.val x)]
  exact abs_norm_sub_norm_le _ _

noncomputable def statewiseRecordPreservationBudget
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) : ℝ :=
  2 * ‖x‖ * statewiseProjectorCommutatorL2 D U x

theorem statewiseRecordPreservationBudget_nonneg
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) :
    0 ≤ statewiseRecordPreservationBudget D U x :=
  mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))
    (statewiseProjectorCommutatorL2_nonneg D U x)

theorem recordProfileL1_unitary_le_two_mul_norm_mul_statewiseCommutatorL2
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) :
    EverettianDecoherence.Metrics.recordProfileL1 D (U x) x ≤
      2 * ‖x‖ * statewiseProjectorCommutatorL2 D U x := by
  change EverettianDecoherence.Metrics.finiteProfileL1
      (fun c => (EverettianDecoherence.Metrics.recordCellNormProfile D (U x) c) ^ 2)
      (fun c => (EverettianDecoherence.Metrics.recordCellNormProfile D x c) ^ 2) ≤ _
  calc
    EverettianDecoherence.Metrics.finiteProfileL1
        (fun c => (EverettianDecoherence.Metrics.recordCellNormProfile D (U x) c) ^ 2)
        (fun c => (EverettianDecoherence.Metrics.recordCellNormProfile D x c) ^ 2) ≤
        Real.sqrt (∑ c, (perspectiveProjectorCommutatorNormProfile D U x c) ^ 2) *
          (Real.sqrt (∑ c, (EverettianDecoherence.Metrics.recordCellNormProfile D (U x) c) ^ 2) +
            Real.sqrt (∑ c, (EverettianDecoherence.Metrics.recordCellNormProfile D x c) ^ 2)) :=
      EverettianDecoherence.Metrics.finite_sq_profile_l1_le_of_difference_bound
        (EverettianDecoherence.Metrics.recordCellNormProfile D (U x))
        (EverettianDecoherence.Metrics.recordCellNormProfile D x)
        (perspectiveProjectorCommutatorNormProfile D U x)
        (EverettianDecoherence.Metrics.recordCellNormProfile_nonneg D (U x))
        (EverettianDecoherence.Metrics.recordCellNormProfile_nonneg D x)
        (perspectiveProjectorCommutatorNormProfile_nonneg D U x)
        (abs_recordCellNormProfile_unitary_sub_le_commutator D U x)
    _ = 2 * ‖x‖ * statewiseProjectorCommutatorL2 D U x := by
      rw [EverettianDecoherence.Metrics.sqrt_sum_sq_recordCellNormProfile_eq_norm,
        EverettianDecoherence.Metrics.sqrt_sum_sq_recordCellNormProfile_eq_norm,
        U.norm_map]
      unfold statewiseProjectorCommutatorL2 EverettianDecoherence.Metrics.finiteL2
        EverettianDecoherence.Metrics.finiteL2Sq
      ring

theorem recordProfileL1_unitary_le_statewiseRecordPreservationBudget
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) :
    EverettianDecoherence.Metrics.recordProfileL1 D (U x) x ≤
      statewiseRecordPreservationBudget D U x :=
  recordProfileL1_unitary_le_two_mul_norm_mul_statewiseCommutatorL2 D U x

theorem recordProfileL1_unitary_le_two_mul_statewiseCommutatorL2
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) (hx : ‖x‖ = 1) :
    EverettianDecoherence.Metrics.recordProfileL1 D (U x) x ≤
      2 * statewiseProjectorCommutatorL2 D U x := by
  calc
    EverettianDecoherence.Metrics.recordProfileL1 D (U x) x ≤
        2 * ‖x‖ * statewiseProjectorCommutatorL2 D U x :=
      recordProfileL1_unitary_le_two_mul_norm_mul_statewiseCommutatorL2 D U x
    _ = 2 * statewiseProjectorCommutatorL2 D U x := by rw [hx]; ring

theorem recordProfileWithin_of_statewiseProjectorCommutatorWithin
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) (ε : ℝ)
    (h : statewiseProjectorCommutatorWithin D U x ε) :
    EverettianDecoherence.Metrics.recordProfileWithin D (2 * ‖x‖ * ε) (U x) x := by
  unfold EverettianDecoherence.Metrics.recordProfileWithin
  exact (recordProfileL1_unitary_le_two_mul_norm_mul_statewiseCommutatorL2 D U x).trans
    (mul_le_mul_of_nonneg_left h (mul_nonneg (by norm_num) (norm_nonneg _)))

theorem recordProfileWithin_of_normalized_statewiseProjectorCommutatorWithin
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) (ε : ℝ)
    (hx : ‖x‖ = 1) (h : statewiseProjectorCommutatorWithin D U x ε) :
    EverettianDecoherence.Metrics.recordProfileWithin D (2 * ε) (U x) x := by
  simpa [hx] using recordProfileWithin_of_statewiseProjectorCommutatorWithin D U x ε h

theorem recordProfileL1_eq_zero_of_statewiseProjectorCommutatorL2_eq_zero
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n)
    (h : statewiseProjectorCommutatorL2 D U x = 0) :
    EverettianDecoherence.Metrics.recordProfileL1 D (U x) x = 0 := by
  apply le_antisymm
  · simpa [h] using recordProfileL1_unitary_le_two_mul_norm_mul_statewiseCommutatorL2 D U x
  · exact EverettianDecoherence.Metrics.recordProfileL1_nonneg D (U x) x

theorem sameRecord_of_statewiseProjectorCommutatorL2_eq_zero
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n)
    (h : statewiseProjectorCommutatorL2 D U x = 0) :
    EverettianProbability.API.ExactFinite.SameRecord D (U x) x :=
  (EverettianDecoherence.Metrics.recordProfileL1_eq_zero_iff_sameRecord D (U x) x).mp
    (recordProfileL1_eq_zero_of_statewiseProjectorCommutatorL2_eq_zero D U x h)

theorem sameRecord_of_exact_projector_commutation_at_state
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n)
    (h : ∀ c, perspectiveProjectorCommutator D U c x = 0) :
    EverettianProbability.API.ExactFinite.SameRecord D (U x) x :=
  sameRecord_of_statewiseProjectorCommutatorL2_eq_zero D U x
    (statewiseProjectorCommutatorL2_eq_zero_of_apply_eq_zero D U x h)

end EverettianDecoherence.Approximation

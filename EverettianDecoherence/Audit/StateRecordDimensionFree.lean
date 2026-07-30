import EverettianDecoherence.Metrics.StateRecordDimensionFree

/-!
**FR.** Audit des bornes ED2B fondées sur la décomposition orthogonale globale.

**EN.** Audit of ED2B bounds based on global orthogonal decomposition.
-/

open EverettianDecoherence.Metrics

#check finiteL2Sq
#check finiteL2
#check finiteL2Sq_nonneg
#check finiteL2_nonneg
#check finiteL2_sq
#check finite_sum_mul_le_l2_mul_l2
#check finite_sq_profile_l1_le_of_difference_bound
#check recordCellNormProfile
#check recordCellNormProfile_nonneg
#check recordCellNormProfile_sq_eq_bornRecord
#check sum_sq_recordCellNormProfile_eq_norm_sq
#check sqrt_sum_sq_recordCellNormProfile_eq_norm
#check abs_recordCellNormProfile_sub_le
#check recordProfileDimensionFreeBudget
#check recordProfileDimensionFreeBudget_nonneg
#check recordProfileL1_le_dimensionFreeBudget
#check recordProfileL1_le_norm_sum_mul_norm_sub
#check recordProfileL1_le_two_mul_norm_sub
#check recordProfileWithin_of_norm_sub_le_dimensionFree
#check recordProfileWithin_of_normalized_norm_sub_le_dimensionFree
#check dimensionFreeBudget_le_cardinalityBudget

example :
    ∑ i : Fin 2, (if i = 0 then (1 : ℝ) else 0) *
      (if i = 0 then (1 : ℝ) else 0) ≤
      Real.sqrt (∑ i : Fin 2, (if i = 0 then (1 : ℝ) else 0) ^ 2) *
        Real.sqrt (∑ i : Fin 2, (if i = 0 then (1 : ℝ) else 0) ^ 2) := by
  apply finite_sum_mul_le_l2_mul_l2

example {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) (z : Gleason.H n) :
    (∑ c : (EverettianProbability.Abstract.Projective.interface n).Cell D,
      (recordCellNormProfile D z c) ^ 2) = ‖z‖ ^ 2 :=
  sum_sq_recordCellNormProfile_eq_norm_sq D z

example {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (x y : Gleason.H n) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    recordProfileL1 D x y ≤ 2 * ‖x - y‖ :=
  recordProfileL1_le_two_mul_norm_sub D x y hx hy

#print axioms EverettianDecoherence.Metrics.finite_sum_mul_le_l2_mul_l2
#print axioms EverettianDecoherence.Metrics.finite_sq_profile_l1_le_of_difference_bound
#print axioms EverettianDecoherence.Metrics.sum_sq_recordCellNormProfile_eq_norm_sq
#print axioms EverettianDecoherence.Metrics.sqrt_sum_sq_recordCellNormProfile_eq_norm
#print axioms EverettianDecoherence.Metrics.recordProfileL1_le_dimensionFreeBudget
#print axioms EverettianDecoherence.Metrics.recordProfileL1_le_two_mul_norm_sub
#print axioms EverettianDecoherence.Metrics.recordProfileWithin_of_normalized_norm_sub_le_dimensionFree

import EverettianDecoherence.Metrics.StateRecordPerturbation

/-!
**FR.** Audit des bornes cinématiques état-vers-record ED2A.

**EN.** Audit of ED2A kinematic state-to-record bounds.
-/

open EverettianDecoherence.Metrics

#check finiteProfileL1_le_sum_of_pointwise
#check finiteProfileL1_le_card_mul_of_pointwise
#check abs_norm_sq_sub_norm_sq_le
#check recordCellCount
#check recordProfilePerturbationBudget
#check recordCellCount_nonneg_cast
#check recordProfilePerturbationBudget_nonneg
#check abs_bornRecord_sub_le_norm_sum_mul_norm_sub
#check recordProfileL1_le_recordProfilePerturbationBudget
#check recordProfileL1_le_card_mul_norm_sum_mul_norm_sub
#check recordProfileL1_le_two_mul_recordCellCount_mul_norm_sub
#check recordProfileWithin_of_norm_sub_le
#check recordProfileWithin_of_normalized_norm_sub_le

example :
    |‖(1 : ℝ)‖ ^ 2 - ‖(0 : ℝ)‖ ^ 2| ≤
      (‖(1 : ℝ)‖ + ‖(0 : ℝ)‖) * ‖(1 : ℝ) - (0 : ℝ)‖ := by
  simpa using abs_norm_sq_sub_norm_sq_le (1 : ℝ) (0 : ℝ)

example :
    finiteProfileL1 (fun _ : Unit => 0) (fun _ : Unit => 1) ≤
      (Fintype.card Unit : ℝ) * 1 := by
  apply finiteProfileL1_le_card_mul_of_pointwise
  intro _
  norm_num

#print axioms EverettianDecoherence.Metrics.finiteProfileL1_le_card_mul_of_pointwise
#print axioms EverettianDecoherence.Metrics.abs_norm_sq_sub_norm_sq_le
#print axioms EverettianDecoherence.Metrics.abs_bornRecord_sub_le_norm_sum_mul_norm_sub
#print axioms EverettianDecoherence.Metrics.recordProfileL1_le_recordProfilePerturbationBudget
#print axioms EverettianDecoherence.Metrics.recordProfileL1_le_two_mul_recordCellCount_mul_norm_sub
#print axioms EverettianDecoherence.Metrics.recordProfileWithin_of_normalized_norm_sub_le

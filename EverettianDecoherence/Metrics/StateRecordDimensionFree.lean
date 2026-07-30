import EverettianDecoherence.Metrics.OrthogonalRecordDecomposition
import EverettianDecoherence.Metrics.StateRecordPerturbation

/-!
**FR.** Ce résultat renforce ED2A en supprimant la dépendance explicite au
nombre de cellules grâce à l'orthogonalité globale de la perspective. Il reste
BORN-SENSITIVE et cinématique : ce n'est pas un théorème de décohérence, et
l'optimalité de la constante n'est pas revendiquée.

**EN.** This result strengthens ED2A by removing explicit dependence on cell
count through the perspective's global orthogonality. It remains BORN-SENSITIVE
and kinematic: it is not a decoherence theorem, and no optimality claim is
made for its constant.
-/

namespace EverettianDecoherence.Metrics

noncomputable def recordProfileDimensionFreeBudget
    {n : ℕ} (x y : Gleason.H n) : ℝ :=
  (‖x‖ + ‖y‖) * ‖x - y‖

theorem recordProfileDimensionFreeBudget_nonneg
    {n : ℕ} (x y : Gleason.H n) :
    0 ≤ recordProfileDimensionFreeBudget x y :=
  mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)

theorem recordProfileL1_le_dimensionFreeBudget
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (x y : Gleason.H n) :
    recordProfileL1 D x y ≤ recordProfileDimensionFreeBudget x y := by
  change finiteProfileL1
      (fun c => (recordCellNormProfile D x c) ^ 2)
      (fun c => (recordCellNormProfile D y c) ^ 2) ≤ _
  calc
    finiteProfileL1
        (fun c => (recordCellNormProfile D x c) ^ 2)
        (fun c => (recordCellNormProfile D y c) ^ 2) ≤
        Real.sqrt (∑ c, (recordCellNormProfile D (x - y) c) ^ 2) *
          (Real.sqrt (∑ c, (recordCellNormProfile D x c) ^ 2) +
            Real.sqrt (∑ c, (recordCellNormProfile D y c) ^ 2)) :=
      finite_sq_profile_l1_le_of_difference_bound
        (recordCellNormProfile D x) (recordCellNormProfile D y)
        (recordCellNormProfile D (x - y))
        (recordCellNormProfile_nonneg D x)
        (recordCellNormProfile_nonneg D y)
        (recordCellNormProfile_nonneg D (x - y))
        (abs_recordCellNormProfile_sub_le D x y)
    _ = recordProfileDimensionFreeBudget x y := by
      rw [sqrt_sum_sq_recordCellNormProfile_eq_norm,
        sqrt_sum_sq_recordCellNormProfile_eq_norm,
        sqrt_sum_sq_recordCellNormProfile_eq_norm]
      unfold recordProfileDimensionFreeBudget
      ring

theorem recordProfileL1_le_norm_sum_mul_norm_sub
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (x y : Gleason.H n) :
    recordProfileL1 D x y ≤ (‖x‖ + ‖y‖) * ‖x - y‖ :=
  recordProfileL1_le_dimensionFreeBudget D x y

theorem recordProfileL1_le_two_mul_norm_sub
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (x y : Gleason.H n) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    recordProfileL1 D x y ≤ 2 * ‖x - y‖ := by
  calc
    recordProfileL1 D x y ≤ (‖x‖ + ‖y‖) * ‖x - y‖ :=
      recordProfileL1_le_norm_sum_mul_norm_sub D x y
    _ = 2 * ‖x - y‖ := by rw [hx, hy]; ring

theorem recordProfileWithin_of_norm_sub_le_dimensionFree
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (x y : Gleason.H n) (δ : ℝ) (hxy : ‖x - y‖ ≤ δ) :
    recordProfileWithin D ((‖x‖ + ‖y‖) * δ) x y := by
  unfold recordProfileWithin
  exact (recordProfileL1_le_norm_sum_mul_norm_sub D x y).trans
    (mul_le_mul_of_nonneg_left hxy
      (add_nonneg (norm_nonneg _) (norm_nonneg _)))

theorem recordProfileWithin_of_normalized_norm_sub_le_dimensionFree
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (x y : Gleason.H n) (δ : ℝ)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ‖x - y‖ ≤ δ) :
    recordProfileWithin D (2 * δ) x y := by
  unfold recordProfileWithin
  exact (recordProfileL1_le_two_mul_norm_sub D x y hx hy).trans
    (mul_le_mul_of_nonneg_left hxy (by norm_num))

theorem dimensionFreeBudget_le_cardinalityBudget
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (x y : Gleason.H n) (hcard : 1 ≤ recordCellCount D) :
    recordProfileDimensionFreeBudget x y ≤ recordProfilePerturbationBudget D x y := by
  unfold recordProfileDimensionFreeBudget recordProfilePerturbationBudget
  have hcardReal : (1 : ℝ) ≤ (recordCellCount D : ℝ) := by
    exact_mod_cast hcard
  have hbudget : 0 ≤ (‖x‖ + ‖y‖) * ‖x - y‖ :=
    mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  nlinarith [mul_nonneg (sub_nonneg.mpr hcardReal) hbudget]

end EverettianDecoherence.Metrics

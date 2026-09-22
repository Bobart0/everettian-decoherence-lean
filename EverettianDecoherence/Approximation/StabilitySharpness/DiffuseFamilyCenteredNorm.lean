import EverettianDecoherence.Approximation.StabilitySharpness.DiffuseFamilyGeometry
import EverettianDecoherence.Approximation.CenteredCutBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Exact norm of the centered diffuse rotation.  Instead of invoking spectral
theory, we decompose every vector into the orthonormal plane spanned by the
two diffuse modes and its orthogonal residual.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped Classical InnerProductSpace

noncomputable section

noncomputable def diffuseLeftCoeff
    (m : ℕ) (x : H (m + m)) : ℂ :=
  inner ℂ (diffuseLeftMode m) x

noncomputable def diffuseRightCoeff
    (m : ℕ) (x : H (m + m)) : ℂ :=
  inner ℂ (diffuseRightMode m) x

noncomputable def diffusePlanePart
    (m : ℕ) (x : H (m + m)) : H (m + m) :=
  diffuseLeftCoeff m x • diffuseLeftMode m +
    diffuseRightCoeff m x • diffuseRightMode m

noncomputable def diffusePlaneResidual
    (m : ℕ) (x : H (m + m)) : H (m + m) :=
  x - diffusePlanePart m x

theorem diffusePlane_decomp
    (m : ℕ) (x : H (m + m)) :
    x = diffusePlanePart m x + diffusePlaneResidual m x := by
  unfold diffusePlaneResidual
  module

theorem diffuseLeftMode_inner_planeResidual
    {m : ℕ} (hm : 0 < m) (x : H (m + m)) :
    inner ℂ (diffuseLeftMode m) (diffusePlaneResidual m x) = 0 := by
  unfold diffusePlaneResidual diffusePlanePart
    diffuseLeftCoeff diffuseRightCoeff
  rw [inner_sub_right, inner_add_right,
    inner_smul_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K,
    diffuseLeftMode_norm hm,
    diffuseLeftMode_inner_rightMode hm]
  simp

theorem diffuseRightMode_inner_planeResidual
    {m : ℕ} (hm : 0 < m) (x : H (m + m)) :
    inner ℂ (diffuseRightMode m) (diffusePlaneResidual m x) = 0 := by
  unfold diffusePlaneResidual diffusePlanePart
    diffuseLeftCoeff diffuseRightCoeff
  rw [inner_sub_right, inner_add_right,
    inner_smul_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K,
    diffuseRightMode_norm hm,
    diffuseRightMode_inner_leftMode hm]
  simp

theorem diffusePlanePart_inner_residual
    {m : ℕ} (hm : 0 < m) (x : H (m + m)) :
    inner ℂ (diffusePlanePart m x) (diffusePlaneResidual m x) = 0 := by
  unfold diffusePlanePart
  rw [inner_add_left, inner_smul_left, inner_smul_left,
    diffuseLeftMode_inner_planeResidual hm x,
    diffuseRightMode_inner_planeResidual hm x]
  simp

theorem diffusePlanePart_norm_sq
    {m : ℕ} (hm : 0 < m) (x : H (m + m)) :
    ‖diffusePlanePart m x‖ ^ 2 =
      ‖diffuseLeftCoeff m x‖ ^ 2 +
        ‖diffuseRightCoeff m x‖ ^ 2 := by
  unfold diffusePlanePart
  have horth :
      inner ℂ
          (diffuseLeftCoeff m x • diffuseLeftMode m)
          (diffuseRightCoeff m x • diffuseRightMode m) = 0 := by
    simp [inner_smul_left, inner_smul_right,
      diffuseLeftMode_inner_rightMode hm]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    _ _ horth]
  simp [norm_smul, diffuseLeftMode_norm hm,
    diffuseRightMode_norm hm, mul_pow]

theorem diffusePlane_pythagoras
    {m : ℕ} (hm : 0 < m) (x : H (m + m)) :
    ‖x‖ ^ 2 =
      ‖diffusePlanePart m x‖ ^ 2 +
        ‖diffusePlaneResidual m x‖ ^ 2 := by
  nth_rw 1 [diffusePlane_decomp m x]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    _ _ (diffusePlanePart_inner_residual hm x)]

noncomputable def diffuseQuarterTurnPart
    (m : ℕ) (x : H (m + m)) : H (m + m) :=
  diffuseLeftCoeff m x • diffuseRightMode m -
    diffuseRightCoeff m x • diffuseLeftMode m

theorem diffuseQuarterTurnPart_norm_sq
    {m : ℕ} (hm : 0 < m) (x : H (m + m)) :
    ‖diffuseQuarterTurnPart m x‖ ^ 2 =
      ‖diffusePlanePart m x‖ ^ 2 := by
  have horthQ :
      inner ℂ
          (diffuseLeftCoeff m x • diffuseRightMode m)
          (- diffuseRightCoeff m x • diffuseLeftMode m) = 0 := by
    simp [inner_smul_left, inner_smul_right,
      diffuseRightMode_inner_leftMode hm]
  have hQ :
      ‖diffuseQuarterTurnPart m x‖ ^ 2 =
        ‖diffuseLeftCoeff m x‖ ^ 2 +
          ‖diffuseRightCoeff m x‖ ^ 2 := by
    unfold diffuseQuarterTurnPart
    rw [sub_eq_add_neg]
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      _ _ horthQ]
    simp [norm_smul, diffuseLeftMode_norm hm,
      diffuseRightMode_norm hm, mul_pow]
  rw [hQ, diffusePlanePart_norm_sq hm x]

theorem diffuseQuarterTurnPart_inner_residual
    {m : ℕ} (hm : 0 < m) (x : H (m + m)) :
    inner ℂ (diffuseQuarterTurnPart m x)
      (diffusePlaneResidual m x) = 0 := by
  unfold diffuseQuarterTurnPart
  rw [inner_sub_left, inner_smul_left, inner_smul_left,
    diffuseRightMode_inner_planeResidual hm x,
    diffuseLeftMode_inner_planeResidual hm x]
  simp

theorem diffuseRotation_apply_planeResidual
    {m : ℕ} (hm : 0 < m) (θ : ℝ) (x : H (m + m)) :
    diffuseRotation m θ (diffusePlaneResidual m x) =
      diffusePlaneResidual m x :=
  diffuseRotation_apply_of_orthogonal hm θ (diffusePlaneResidual m x)
    (diffuseLeftMode_inner_planeResidual hm x)
    (diffuseRightMode_inner_planeResidual hm x)

theorem diffuseCentered_apply
    {m : ℕ} (hm : 0 < m) (θ : ℝ) (x : H (m + m)) :
    centeredUnitaryCLM (diffuseRotation m θ) (Real.cos θ : ℂ) x =
      (Real.sin θ : ℂ) • diffuseQuarterTurnPart m x +
        ((1 - Real.cos θ : ℝ) : ℂ) • diffusePlaneResidual m x := by
  have hx := diffusePlane_decomp m x
  rw [centeredUnitaryCLM_apply]
  calc
    diffuseRotation m θ x - (Real.cos θ : ℂ) • x =
        diffuseRotation m θ
            (diffusePlanePart m x + diffusePlaneResidual m x) -
          (Real.cos θ : ℂ) •
            (diffusePlanePart m x + diffusePlaneResidual m x) := by
              rw [← hx]
    _ = (Real.sin θ : ℂ) • diffuseQuarterTurnPart m x +
        ((1 - Real.cos θ : ℝ) : ℂ) • diffusePlaneResidual m x := by
      unfold diffusePlanePart
      simp only [map_add, map_smul]
      rw [diffuseRotation_apply_left hm θ,
        diffuseRotation_apply_right hm θ,
        diffuseRotation_apply_planeResidual hm θ x]
      unfold diffuseQuarterTurnPart
      module

theorem diffuseCentered_norm_sq
    {m : ℕ} (hm : 0 < m) (θ : ℝ) (x : H (m + m)) :
    ‖centeredUnitaryCLM (diffuseRotation m θ) (Real.cos θ : ℂ) x‖ ^ 2 =
      Real.sin θ ^ 2 * ‖diffusePlanePart m x‖ ^ 2 +
        (1 - Real.cos θ) ^ 2 * ‖diffusePlaneResidual m x‖ ^ 2 := by
  rw [diffuseCentered_apply hm θ x]
  have horth :
      inner ℂ
          ((Real.sin θ : ℂ) • diffuseQuarterTurnPart m x)
          (((1 - Real.cos θ : ℝ) : ℂ) • diffusePlaneResidual m x) = 0 := by
    simp [inner_smul_left, inner_smul_right,
      diffuseQuarterTurnPart_inner_residual hm x]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    _ _ horth]
  rw [norm_smul, norm_smul, diffuseQuarterTurnPart_norm_sq hm x]
  simp only [Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

theorem diffuse_defect_sq_le_sin_sq
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi2 : θ < Real.pi / 2) :
    (1 - Real.cos θ) ^ 2 ≤ Real.sin θ ^ 2 := by
  have hneg : -(Real.pi / 2) < θ := by
    linarith [Real.pi_pos]
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨hneg, hθpi2⟩
  have hθpi : θ < Real.pi := by
    linarith [Real.pi_pos]
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 hθpi
  have htrig := Real.sin_sq_add_cos_sq θ
  nlinarith

theorem diffuseCentered_norm_le_sin
    {m : ℕ} (hm : 0 < m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi2 : θ < Real.pi / 2) :
    ‖centeredUnitaryCLM (diffuseRotation m θ) (Real.cos θ : ℂ)‖ ≤
      Real.sin θ := by
  have hθpi : θ < Real.pi := by
    linarith [Real.pi_pos]
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 hθpi
  apply ContinuousLinearMap.opNorm_le_bound _ hsin.le
  intro x
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hsin.le (norm_nonneg x))).1
  rw [mul_pow, diffuseCentered_norm_sq hm θ x]
  have hd := diffuse_defect_sq_le_sin_sq hθ0 hθpi2
  have hplane := diffusePlane_pythagoras hm x
  calc
    Real.sin θ ^ 2 * ‖diffusePlanePart m x‖ ^ 2 +
        (1 - Real.cos θ) ^ 2 * ‖diffusePlaneResidual m x‖ ^ 2
        ≤
      Real.sin θ ^ 2 * ‖diffusePlanePart m x‖ ^ 2 +
        Real.sin θ ^ 2 * ‖diffusePlaneResidual m x‖ ^ 2 := by
          gcongr
          exact sq_nonneg _
    _ = Real.sin θ ^ 2 *
        (‖diffusePlanePart m x‖ ^ 2 +
          ‖diffusePlaneResidual m x‖ ^ 2) := by ring
    _ = Real.sin θ ^ 2 * ‖x‖ ^ 2 := by rw [← hplane]

theorem diffuseCentered_apply_leftMode
    {m : ℕ} (hm : 0 < m) (θ : ℝ) :
    centeredUnitaryCLM (diffuseRotation m θ) (Real.cos θ : ℂ)
        (diffuseLeftMode m) =
      (Real.sin θ : ℂ) • diffuseRightMode m := by
  rw [centeredUnitaryCLM_apply, diffuseRotation_apply_left hm θ]
  module

theorem sin_le_diffuseCentered_norm
    {m : ℕ} (hm : 0 < m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi2 : θ < Real.pi / 2) :
    Real.sin θ ≤
      ‖centeredUnitaryCLM (diffuseRotation m θ) (Real.cos θ : ℂ)‖ := by
  have hθpi : θ < Real.pi := by
    linarith [Real.pi_pos]
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 hθpi
  have h :=
    (centeredUnitaryCLM (diffuseRotation m θ) (Real.cos θ : ℂ)).le_opNorm
      (diffuseLeftMode m)
  rw [diffuseCentered_apply_leftMode hm θ,
    norm_smul, diffuseRightMode_norm hm,
    diffuseLeftMode_norm hm] at h
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsin] using h

theorem diffuseCentered_norm_eq_sin
    {m : ℕ} (hm : 0 < m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi2 : θ < Real.pi / 2) :
    ‖centeredUnitaryCLM (diffuseRotation m θ) (Real.cos θ : ℂ)‖ =
      Real.sin θ := by
  exact le_antisymm
    (diffuseCentered_norm_le_sin hm hθ0 hθpi2)
    (sin_le_diffuseCentered_norm hm hθ0 hθpi2)

end
end EverettianDecoherence.Approximation

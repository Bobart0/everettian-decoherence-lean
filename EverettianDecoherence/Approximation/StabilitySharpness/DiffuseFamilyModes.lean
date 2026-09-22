import EverettianDecoherence.Approximation.StabilitySharpness.CoordinatePerspective
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
**FR.** Modes uniformes des deux demi-blocs de la famille diffuse à `2m`
cellules. Pour `m > 0`, les vecteurs normalisés gauche et droite sont
orthonormaux.

**EN.** Uniform modes of the two half-blocks in the diffuse `2m`-cell
family. For `m > 0`, the normalized left and right vectors are orthonormal.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open scoped Classical InnerProductSpace BigOperators

noncomputable section

def diffuseLeftFamily (m : ℕ) (i : Fin m) : H (m + m) :=
  coordinateOrthonormalBasis (m + m) (Fin.castAdd m i)

def diffuseRightFamily (m : ℕ) (i : Fin m) : H (m + m) :=
  coordinateOrthonormalBasis (m + m) (Fin.natAdd m i)

theorem diffuseLeftFamily_orthonormal (m : ℕ) :
    Orthonormal ℂ (diffuseLeftFamily m) := by
  unfold diffuseLeftFamily
  simpa [Function.comp_def] using
    (coordinateOrthonormalBasis (m + m)).orthonormal.comp
      (Fin.castAdd m) (Fin.castAdd_injective m m)

theorem diffuseRightFamily_orthonormal (m : ℕ) :
    Orthonormal ℂ (diffuseRightFamily m) := by
  unfold diffuseRightFamily
  simpa [Function.comp_def] using
    (coordinateOrthonormalBasis (m + m)).orthonormal.comp
      (Fin.natAdd m) (Fin.natAdd_injective m m)

theorem diffuseLeftFamily_inner_rightFamily
    (m : ℕ) (i j : Fin m) :
    inner ℂ (diffuseLeftFamily m i) (diffuseRightFamily m j) = 0 := by
  apply (coordinateOrthonormalBasis (m + m)).orthonormal.2
  intro h
  have hv := congrArg Fin.val h
  simp [diffuseLeftFamily, diffuseRightFamily] at hv
  omega

noncomputable def diffuseLeftSum (m : ℕ) : H (m + m) :=
  ∑ i : Fin m, diffuseLeftFamily m i

noncomputable def diffuseRightSum (m : ℕ) : H (m + m) :=
  ∑ i : Fin m, diffuseRightFamily m i

theorem diffuseLeftSum_inner_family (m : ℕ) (i : Fin m) :
    inner ℂ (diffuseLeftSum m) (diffuseLeftFamily m i) = 1 := by
  simpa [diffuseLeftSum] using
    (diffuseLeftFamily_orthonormal m).inner_left_fintype
      (fun _ : Fin m => (1 : ℂ)) i

theorem diffuseRightSum_inner_family (m : ℕ) (i : Fin m) :
    inner ℂ (diffuseRightSum m) (diffuseRightFamily m i) = 1 := by
  simpa [diffuseRightSum] using
    (diffuseRightFamily_orthonormal m).inner_left_fintype
      (fun _ : Fin m => (1 : ℂ)) i

theorem diffuseLeftSum_inner_self (m : ℕ) :
    inner ℂ (diffuseLeftSum m) (diffuseLeftSum m) = (m : ℂ) := by
  unfold diffuseLeftSum
  rw [inner_sum]
  simp [diffuseLeftSum_inner_family]

theorem diffuseRightSum_inner_self (m : ℕ) :
    inner ℂ (diffuseRightSum m) (diffuseRightSum m) = (m : ℂ) := by
  unfold diffuseRightSum
  rw [inner_sum]
  simp [diffuseRightSum_inner_family]

theorem diffuseLeftSum_inner_rightSum (m : ℕ) :
    inner ℂ (diffuseLeftSum m) (diffuseRightSum m) = 0 := by
  unfold diffuseLeftSum diffuseRightSum
  simp_rw [sum_inner, inner_sum]
  simp [diffuseLeftFamily_inner_rightFamily]

noncomputable def diffuseModeScale (m : ℕ) : ℝ :=
  (Real.sqrt (m : ℝ))⁻¹

noncomputable def diffuseLeftMode (m : ℕ) : H (m + m) :=
  ((diffuseModeScale m : ℝ) : ℂ) • diffuseLeftSum m

noncomputable def diffuseRightMode (m : ℕ) : H (m + m) :=
  ((diffuseModeScale m : ℝ) : ℂ) • diffuseRightSum m

theorem diffuseModeScale_pos {m : ℕ} (hm : 0 < m) :
    0 < diffuseModeScale m := by
  unfold diffuseModeScale
  exact inv_pos.mpr (Real.sqrt_pos.2 (by exact_mod_cast hm))

theorem diffuseLeftSum_norm_sq (m : ℕ) :
    ‖diffuseLeftSum m‖ ^ 2 = (m : ℝ) := by
  rw [@norm_sq_eq_re_inner ℂ]
  rw [diffuseLeftSum_inner_self]
  simp

theorem diffuseRightSum_norm_sq (m : ℕ) :
    ‖diffuseRightSum m‖ ^ 2 = (m : ℝ) := by
  rw [@norm_sq_eq_re_inner ℂ]
  rw [diffuseRightSum_inner_self]
  simp

theorem diffuseLeftMode_norm {m : ℕ} (hm : 0 < m) :
    ‖diffuseLeftMode m‖ = 1 := by
  have hscale := diffuseModeScale_pos hm
  have hsqrt : 0 < Real.sqrt (m : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hsum := diffuseLeftSum_norm_sq m
  have hsq : ‖diffuseLeftMode m‖ ^ 2 = 1 := by
    unfold diffuseLeftMode
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hscale]
    unfold diffuseModeScale at hscale ⊢
    field_simp [ne_of_gt hsqrt]
    nlinarith [Real.sq_sqrt (show 0 ≤ (m : ℝ) by positivity)]
  nlinarith [norm_nonneg (diffuseLeftMode m)]

theorem diffuseRightMode_norm {m : ℕ} (hm : 0 < m) :
    ‖diffuseRightMode m‖ = 1 := by
  have hscale := diffuseModeScale_pos hm
  have hsqrt : 0 < Real.sqrt (m : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hsum := diffuseRightSum_norm_sq m
  have hsq : ‖diffuseRightMode m‖ ^ 2 = 1 := by
    unfold diffuseRightMode
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hscale]
    unfold diffuseModeScale at hscale ⊢
    field_simp [ne_of_gt hsqrt]
    nlinarith [Real.sq_sqrt (show 0 ≤ (m : ℝ) by positivity)]
  nlinarith [norm_nonneg (diffuseRightMode m)]

theorem diffuseLeftMode_inner_rightMode {m : ℕ} (hm : 0 < m) :
    inner ℂ (diffuseLeftMode m) (diffuseRightMode m) = 0 := by
  unfold diffuseLeftMode diffuseRightMode
  rw [inner_smul_left, inner_smul_right, diffuseLeftSum_inner_rightSum]
  simp


theorem diffuseLeftMode_inner_leftFamily
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    inner ℂ (diffuseLeftMode m) (diffuseLeftFamily m i) =
      (diffuseModeScale m : ℂ) := by
  unfold diffuseLeftMode
  rw [inner_smul_left, diffuseLeftSum_inner_family]
  simp [diffuseModeScale]

theorem diffuseLeftFamily_inner_leftMode
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    inner ℂ (diffuseLeftFamily m i) (diffuseLeftMode m) =
      (diffuseModeScale m : ℂ) := by
  rw [← inner_conj_symm, diffuseLeftMode_inner_leftFamily hm i]
  simp [diffuseModeScale]

theorem diffuseRightMode_inner_rightFamily
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    inner ℂ (diffuseRightMode m) (diffuseRightFamily m i) =
      (diffuseModeScale m : ℂ) := by
  unfold diffuseRightMode
  rw [inner_smul_left, diffuseRightSum_inner_family]
  simp [diffuseModeScale]

theorem diffuseRightFamily_inner_rightMode
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    inner ℂ (diffuseRightFamily m i) (diffuseRightMode m) =
      (diffuseModeScale m : ℂ) := by
  rw [← inner_conj_symm, diffuseRightMode_inner_rightFamily hm i]
  simp [diffuseModeScale]

theorem diffuseLeftMode_inner_rightFamily
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    inner ℂ (diffuseLeftMode m) (diffuseRightFamily m i) = 0 := by
  unfold diffuseLeftMode diffuseLeftSum
  rw [inner_smul_left]
  simp_rw [sum_inner]
  simp [diffuseLeftFamily_inner_rightFamily]

theorem diffuseLeftFamily_inner_rightMode
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    inner ℂ (diffuseLeftFamily m i) (diffuseRightMode m) = 0 := by
  unfold diffuseRightMode diffuseRightSum
  rw [inner_smul_right]
  simp_rw [inner_sum]
  simp [diffuseLeftFamily_inner_rightFamily]

theorem diffuseRightMode_inner_leftFamily
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    inner ℂ (diffuseRightMode m) (diffuseLeftFamily m i) = 0 := by
  rw [← inner_conj_symm, diffuseLeftFamily_inner_rightMode hm i]
  simp

theorem diffuseRightFamily_inner_leftMode
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    inner ℂ (diffuseRightFamily m i) (diffuseLeftMode m) = 0 := by
  rw [← inner_conj_symm, diffuseLeftMode_inner_rightFamily hm i]
  simp

theorem diffuseModes_orthonormal {m : ℕ} (hm : 0 < m) :
    Orthonormal ℂ (fun i : Fin 2 =>
      if i = 0 then diffuseLeftMode m else diffuseRightMode m) := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j
  · simp [diffuseLeftMode_norm hm, inner_self_eq_norm_sq_to_K]
  · simp [diffuseLeftMode_inner_rightMode hm]
  · rw [inner_conj_symm, diffuseLeftMode_inner_rightMode hm]
    simp
  · simp [diffuseRightMode_norm hm, inner_self_eq_norm_sq_to_K]

end
end EverettianDecoherence.Approximation

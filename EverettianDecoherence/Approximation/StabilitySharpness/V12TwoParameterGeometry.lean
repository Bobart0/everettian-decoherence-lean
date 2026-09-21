import EverettianDecoherence.Approximation.StabilitySharpness.V12TwoParameterScalar
import EverettianDecoherence.Approximation.StabilitySharpness.Perspective3
import EverettianDecoherence.Approximation.RankOneCellCommutatorFormula
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
**FR.** Réalisation géométrique C3 de la famille continue v12 à deux
paramètres. Pour 0 ≤ x ≤ 1 et 0 ≤ d ≤ 2, on pose
  a_x = sqrt(1-x), b_x = sqrt(x),
  c_d = 1-d, s_d = sqrt(2d-d^2),
puis U_{d,x}=Q_x R_d Q_x^*. Les trois cellules coordonnées ont exactement
les budgets f_d(1-x), f_d(x), f_d(1).

**EN.** C3 geometric realization of the continuous two-parameter v12 family.
For 0 ≤ x ≤ 1 and 0 ≤ d ≤ 2, set
  a_x = sqrt(1-x), b_x = sqrt(x),
  c_d = 1-d, s_d = sqrt(2d-d^2),
and U_{d,x}=Q_x R_d Q_x^*. The three coordinate cells have exactly the
budgets f_d(1-x), f_d(x), f_d(1).
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped Classical InnerProductSpace Matrix BigOperators

noncomputable section

def v12TwoParamA (x : ℝ) : ℝ := Real.sqrt (1 - x)
def v12TwoParamB (x : ℝ) : ℝ := Real.sqrt x
def v12TwoParamC (d : ℝ) : ℝ := 1 - d
def v12TwoParamS (d : ℝ) : ℝ := Real.sqrt (2 * d - d ^ 2)

theorem v12TwoParamA_sq_add_B_sq
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    v12TwoParamA x ^ 2 + v12TwoParamB x ^ 2 = 1 := by
  unfold v12TwoParamA v12TwoParamB
  rw [Real.sq_sqrt (sub_nonneg.mpr hx1), Real.sq_sqrt hx0]
  ring

theorem v12TwoParamC_sq_add_S_sq
    (d : ℝ) (hd0 : 0 ≤ d) (hd2 : d ≤ 2) :
    v12TwoParamC d ^ 2 + v12TwoParamS d ^ 2 = 1 := by
  have hrad : 0 ≤ 2 * d - d ^ 2 := by
    nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hd2)]
  unfold v12TwoParamC v12TwoParamS
  rw [Real.sq_sqrt hrad]
  ring

def v12TwoParamBasisMatrix (x : ℝ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![(v12TwoParamA x : ℂ), -(v12TwoParamB x : ℂ), 0;
     (v12TwoParamB x : ℂ),  (v12TwoParamA x : ℂ), 0;
     0,                       0,                       1]

def v12TwoParamPlaneRotationMatrix (d : ℝ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![(v12TwoParamC d : ℂ), 0, -(v12TwoParamS d : ℂ);
     0,                       1, 0;
     (v12TwoParamS d : ℂ), 0,  (v12TwoParamC d : ℂ)]

theorem v12TwoParamA_sq_add_B_sq_complex
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (v12TwoParamA x : ℂ) ^ 2 + (v12TwoParamB x : ℂ) ^ 2 = 1 := by
  exact_mod_cast v12TwoParamA_sq_add_B_sq x hx0 hx1

theorem v12TwoParamC_sq_add_S_sq_complex
    (d : ℝ) (hd0 : 0 ≤ d) (hd2 : d ≤ 2) :
    (v12TwoParamC d : ℂ) ^ 2 + (v12TwoParamS d : ℂ) ^ 2 = 1 := by
  exact_mod_cast v12TwoParamC_sq_add_S_sq d hd0 hd2

theorem v12TwoParamBasisMatrix_mem_unitary
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    v12TwoParamBasisMatrix x ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [v12TwoParamBasisMatrix, Matrix.mul_apply,
      Fin.sum_univ_three, pow_two]
      using v12TwoParamA_sq_add_B_sq_complex x hx0 hx1
  · simp [v12TwoParamBasisMatrix, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  · simp [v12TwoParamBasisMatrix, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [v12TwoParamBasisMatrix, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  · simpa [v12TwoParamBasisMatrix, Matrix.mul_apply,
      Fin.sum_univ_three, pow_two, add_comm]
      using v12TwoParamA_sq_add_B_sq_complex x hx0 hx1
  · simp [v12TwoParamBasisMatrix, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [v12TwoParamBasisMatrix, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [v12TwoParamBasisMatrix, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [v12TwoParamBasisMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem v12TwoParamPlaneRotationMatrix_mem_unitary
    (d : ℝ) (hd0 : 0 ≤ d) (hd2 : d ≤ 2) :
    v12TwoParamPlaneRotationMatrix d ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [v12TwoParamPlaneRotationMatrix, Matrix.mul_apply,
      Fin.sum_univ_three, pow_two]
      using v12TwoParamC_sq_add_S_sq_complex d hd0 hd2
  · simp [v12TwoParamPlaneRotationMatrix, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [v12TwoParamPlaneRotationMatrix, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  · simp [v12TwoParamPlaneRotationMatrix, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [v12TwoParamPlaneRotationMatrix, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [v12TwoParamPlaneRotationMatrix, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [v12TwoParamPlaneRotationMatrix, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  · simp [v12TwoParamPlaneRotationMatrix, Matrix.mul_apply, Fin.sum_univ_three]
  · simpa [v12TwoParamPlaneRotationMatrix, Matrix.mul_apply,
      Fin.sum_univ_three, pow_two, add_comm]
      using v12TwoParamC_sq_add_S_sq_complex d hd0 hd2

def v12TwoParamRotationMatrix (d x : ℝ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  v12TwoParamBasisMatrix x *
    v12TwoParamPlaneRotationMatrix d *
      star (v12TwoParamBasisMatrix x)

theorem v12TwoParamRotationMatrix_mem_unitary
    (d x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hd0 : 0 ≤ d) (hd2 : d ≤ 2) :
    v12TwoParamRotationMatrix d x ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  have hQ := v12TwoParamBasisMatrix_mem_unitary x hx0 hx1
  have hR := v12TwoParamPlaneRotationMatrix_mem_unitary d hd0 hd2
  have hQstar :
      star (v12TwoParamBasisMatrix x) ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    simpa using (Matrix.mem_unitaryGroup_iff'.mp hQ)
  exact (Matrix.unitaryGroup (Fin 3) ℂ).mul_mem
    ((Matrix.unitaryGroup (Fin 3) ℂ).mul_mem hQ hR) hQstar

noncomputable def v12TwoParamRotationUnitary
    (d x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hd0 : 0 ≤ d) (hd2 : d ≤ 2) :
    unitary (H 3 →L[ℂ] H 3) := by
  refine ⟨Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ)
    (v12TwoParamRotationMatrix d x), ?_⟩
  have h := v12TwoParamRotationMatrix_mem_unitary d x hx0 hx1 hd0 hd2
  rw [Unitary.mem_iff] at h ⊢
  constructor
  · simpa only [map_star, map_mul, map_one] using congrArg
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ)) h.1
  · simpa only [map_star, map_mul, map_one] using congrArg
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ)) h.2

noncomputable def v12TwoParamRotation
    (d x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hd0 : 0 ≤ d) (hd2 : d ≤ 2) :
    H 3 ≃ₗᵢ[ℂ] H 3 :=
  Unitary.linearIsometryEquiv
    (v12TwoParamRotationUnitary d x hx0 hx1 hd0 hd2)

@[simp] theorem v12TwoParamRotationMatrix_00
    (d x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    v12TwoParamRotationMatrix d x (0 : Fin 3) (0 : Fin 3) =
      (1 - d * v12TwoParamA x ^ 2 : ℝ) := by
  unfold v12TwoParamRotationMatrix v12TwoParamBasisMatrix
    v12TwoParamPlaneRotationMatrix v12TwoParamC
  simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hAB := v12TwoParamA_sq_add_B_sq_complex x hx0 hx1
  linear_combination hAB

@[simp] theorem v12TwoParamRotationMatrix_11
    (d x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    v12TwoParamRotationMatrix d x (1 : Fin 3) (1 : Fin 3) =
      (1 - d * v12TwoParamB x ^ 2 : ℝ) := by
  unfold v12TwoParamRotationMatrix v12TwoParamBasisMatrix
    v12TwoParamPlaneRotationMatrix v12TwoParamC
  simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hAB := v12TwoParamA_sq_add_B_sq_complex x hx0 hx1
  linear_combination hAB

@[simp] theorem v12TwoParamRotationMatrix_22
    (d x : ℝ) :
    v12TwoParamRotationMatrix d x (2 : Fin 3) (2 : Fin 3) =
      (1 - d : ℝ) := by
  unfold v12TwoParamRotationMatrix v12TwoParamBasisMatrix
    v12TwoParamPlaneRotationMatrix v12TwoParamC
  simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem v12TwoParamRotation_inner_basis
    (d x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hd0 : 0 ≤ d) (hd2 : d ≤ 2)
    (i : Fin 3) :
    inner ℂ (stabilitySharpnessBasis3 i : H 3)
      (v12TwoParamRotation d x hx0 hx1 hd0 hd2
        (stabilitySharpnessBasis3 i : H 3)) =
      v12TwoParamRotationMatrix d x i i := by
  unfold v12TwoParamRotation
  change inner ℂ (EuclideanSpace.basisFun (Fin 3) ℂ i)
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ)
      (v12TwoParamRotationMatrix d x)
      (EuclideanSpace.basisFun (Fin 3) ℂ i)) = _
  rw [EuclideanSpace.basisFun_inner]
  change
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ)
      (v12TwoParamRotationMatrix d x)
      (EuclideanSpace.basisFun (Fin 3) ℂ i)).ofLp i = _
  rw [Matrix.ofLp_toEuclideanCLM]
  simp [Matrix.mulVec, dotProduct, EuclideanSpace.basisFun_apply,
    PiLp.ofLp_single]

theorem v12TwoParamCell0_budget_sq
    (d x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hd0 : 0 ≤ d) (hd2 : d ≤ 2) :
    cellCommutatorOpNormSq stabilitySharpnessPerspective3
      (v12TwoParamRotation d x hx0 hx1 hd0 hd2)
      (stabilitySharpnessCell3 (0 : Fin 3)) =
      v12TwoParamGap d (1 - x) := by
  change
    perspectiveProjectorCommutatorOpNormProfile
      stabilitySharpnessPerspective3
      (v12TwoParamRotation d x hx0 hx1 hd0 hd2)
      (stabilitySharpnessCell3 (0 : Fin 3)) ^ 2 = _
  rw [perspectiveProjectorCommutatorOpNormProfile_sq_rankOne
    stabilitySharpnessPerspective3
    (v12TwoParamRotation d x hx0 hx1 hd0 hd2)
    (stabilitySharpnessCell3 (0 : Fin 3))
    (stabilitySharpnessBasis3 (0 : Fin 3))
    (stabilitySharpnessBasis3_norm (0 : Fin 3))
    (stabilitySharpnessCell3_val (0 : Fin 3))]
  rw [v12TwoParamRotation_inner_basis,
    v12TwoParamRotationMatrix_00 d x hx0 hx1]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hA := v12TwoParamA_sq_add_B_sq x hx0 hx1
  have hBsq : v12TwoParamB x ^ 2 = x := by
    unfold v12TwoParamB
    exact Real.sq_sqrt hx0
  have hAsq : v12TwoParamA x ^ 2 = 1 - x := by
    linarith
  rw [hAsq]
  unfold v12TwoParamGap
  ring

theorem v12TwoParamCell1_budget_sq
    (d x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hd0 : 0 ≤ d) (hd2 : d ≤ 2) :
    cellCommutatorOpNormSq stabilitySharpnessPerspective3
      (v12TwoParamRotation d x hx0 hx1 hd0 hd2)
      (stabilitySharpnessCell3 (1 : Fin 3)) =
      v12TwoParamGap d x := by
  change
    perspectiveProjectorCommutatorOpNormProfile
      stabilitySharpnessPerspective3
      (v12TwoParamRotation d x hx0 hx1 hd0 hd2)
      (stabilitySharpnessCell3 (1 : Fin 3)) ^ 2 = _
  rw [perspectiveProjectorCommutatorOpNormProfile_sq_rankOne
    stabilitySharpnessPerspective3
    (v12TwoParamRotation d x hx0 hx1 hd0 hd2)
    (stabilitySharpnessCell3 (1 : Fin 3))
    (stabilitySharpnessBasis3 (1 : Fin 3))
    (stabilitySharpnessBasis3_norm (1 : Fin 3))
    (stabilitySharpnessCell3_val (1 : Fin 3))]
  rw [v12TwoParamRotation_inner_basis,
    v12TwoParamRotationMatrix_11 d x hx0 hx1]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hBsq : v12TwoParamB x ^ 2 = x := by
    unfold v12TwoParamB
    exact Real.sq_sqrt hx0
  rw [hBsq]
  unfold v12TwoParamGap
  ring

theorem v12TwoParamCell2_budget_sq
    (d x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hd0 : 0 ≤ d) (hd2 : d ≤ 2) :
    cellCommutatorOpNormSq stabilitySharpnessPerspective3
      (v12TwoParamRotation d x hx0 hx1 hd0 hd2)
      (stabilitySharpnessCell3 (2 : Fin 3)) =
      v12TwoParamGap d 1 := by
  change
    perspectiveProjectorCommutatorOpNormProfile
      stabilitySharpnessPerspective3
      (v12TwoParamRotation d x hx0 hx1 hd0 hd2)
      (stabilitySharpnessCell3 (2 : Fin 3)) ^ 2 = _
  rw [perspectiveProjectorCommutatorOpNormProfile_sq_rankOne
    stabilitySharpnessPerspective3
    (v12TwoParamRotation d x hx0 hx1 hd0 hd2)
    (stabilitySharpnessCell3 (2 : Fin 3))
    (stabilitySharpnessBasis3 (2 : Fin 3))
    (stabilitySharpnessBasis3_norm (2 : Fin 3))
    (stabilitySharpnessCell3_val (2 : Fin 3))]
  rw [v12TwoParamRotation_inner_basis,
    v12TwoParamRotationMatrix_22]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  unfold v12TwoParamGap
  ring

end
end EverettianDecoherence.Approximation

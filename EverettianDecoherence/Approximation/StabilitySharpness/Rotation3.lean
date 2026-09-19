import EverettianDecoherence.Approximation.StabilitySharpness.Parameters
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
**FR.** Rotation explicite de dimension trois pour la sharpness du théorème de
stabilité. On factorise l'unitaire comme Q_n R_m Q_n^*, où Q_n envoie le
premier axe de coordonnées sur u_n = (A_n,B_n,0), et R_m effectue la rotation
(c_m,s_m) dans le plan engendré par le premier et le troisième axes.

**EN.** Explicit three-dimensional rotation for stability sharpness. We
factor the unitary as Q_n R_m Q_n^*, where Q_n sends the first coordinate axis
to u_n = (A_n,B_n,0), and R_m performs the (c_m,s_m) rotation in the plane
spanned by the first and third coordinate axes.
-/

namespace EverettianDecoherence.Approximation

open EverettianDecoherence.Metrics Gleason
open scoped Matrix

noncomputable section

/-- Basis-change matrix with first column u_n=(A_n,B_n,0). -/
def stabilitySharpnessBasisMatrix (n : ℕ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![(stabilitySharpnessA n : ℂ), -(stabilitySharpnessB n : ℂ), 0;
     (stabilitySharpnessB n : ℂ),  (stabilitySharpnessA n : ℂ), 0;
     0,                                0,                          1]

/-- Plane rotation in the first/third coordinate plane. -/
def stabilitySharpnessPlaneRotationMatrix (m : ℕ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![(iterationSharpnessC m : ℂ), 0, -(iterationSharpnessS m : ℂ);
     0,                              1, 0;
     (iterationSharpnessS m : ℂ), 0,  (iterationSharpnessC m : ℂ)]

theorem stabilitySharpnessA_sq_add_B_sq_complex (n : ℕ) :
    (stabilitySharpnessA n : ℂ) ^ 2 +
        (stabilitySharpnessB n : ℂ) ^ 2 = 1 := by
  exact_mod_cast stabilitySharpnessA_sq_add_B_sq n

theorem stabilitySharpnessC_sq_add_S_sq_complex (m : ℕ) :
    (iterationSharpnessC m : ℂ) ^ 2 +
        (iterationSharpnessS m : ℂ) ^ 2 = 1 := by
  exact_mod_cast iterationSharpnessC_sq_add_S_sq m

theorem stabilitySharpnessBasisMatrix_mem_unitary (n : ℕ) :
    stabilitySharpnessBasisMatrix n ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [stabilitySharpnessBasisMatrix, Matrix.mul_apply,
      Fin.sum_univ_three, pow_two]
      using stabilitySharpnessA_sq_add_B_sq_complex n
  · simp [stabilitySharpnessBasisMatrix, Matrix.mul_apply,
      Fin.sum_univ_three]
    ring
  · simp [stabilitySharpnessBasisMatrix, Matrix.mul_apply,
      Fin.sum_univ_three]
  · simp [stabilitySharpnessBasisMatrix, Matrix.mul_apply,
      Fin.sum_univ_three]
    ring
  · simpa [stabilitySharpnessBasisMatrix, Matrix.mul_apply,
      Fin.sum_univ_three, pow_two, add_comm]
      using stabilitySharpnessA_sq_add_B_sq_complex n
  · simp [stabilitySharpnessBasisMatrix, Matrix.mul_apply,
      Fin.sum_univ_three]
  · simp [stabilitySharpnessBasisMatrix, Matrix.mul_apply,
      Fin.sum_univ_three]
  · simp [stabilitySharpnessBasisMatrix, Matrix.mul_apply,
      Fin.sum_univ_three]
  · simp [stabilitySharpnessBasisMatrix, Matrix.mul_apply,
      Fin.sum_univ_three]

theorem stabilitySharpnessPlaneRotationMatrix_mem_unitary (m : ℕ) :
    stabilitySharpnessPlaneRotationMatrix m ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [stabilitySharpnessPlaneRotationMatrix, Matrix.mul_apply,
      Fin.sum_univ_three, pow_two]
      using stabilitySharpnessC_sq_add_S_sq_complex m
  · simp [stabilitySharpnessPlaneRotationMatrix, Matrix.mul_apply,
      Fin.sum_univ_three]
  · simp [stabilitySharpnessPlaneRotationMatrix, Matrix.mul_apply,
      Fin.sum_univ_three]
    ring
  · simp [stabilitySharpnessPlaneRotationMatrix, Matrix.mul_apply,
      Fin.sum_univ_three]
  · simp [stabilitySharpnessPlaneRotationMatrix, Matrix.mul_apply,
      Fin.sum_univ_three]
  · simp [stabilitySharpnessPlaneRotationMatrix, Matrix.mul_apply,
      Fin.sum_univ_three]
  · simp [stabilitySharpnessPlaneRotationMatrix, Matrix.mul_apply,
      Fin.sum_univ_three]
    ring
  · simp [stabilitySharpnessPlaneRotationMatrix, Matrix.mul_apply,
      Fin.sum_univ_three]
  · simpa [stabilitySharpnessPlaneRotationMatrix, Matrix.mul_apply,
      Fin.sum_univ_three, pow_two, add_comm]
      using stabilitySharpnessC_sq_add_S_sq_complex m

/-- The explicit stability-sharpness matrix Q_n R_m Q_n^*. -/
def stabilitySharpnessRotationMatrix (n m : ℕ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  stabilitySharpnessBasisMatrix n *
    stabilitySharpnessPlaneRotationMatrix m *
      star (stabilitySharpnessBasisMatrix n)

theorem stabilitySharpnessRotationMatrix_mem_unitary (n m : ℕ) :
    stabilitySharpnessRotationMatrix n m ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  have hQ := stabilitySharpnessBasisMatrix_mem_unitary n
  have hR := stabilitySharpnessPlaneRotationMatrix_mem_unitary m
  have hQstar :
      star (stabilitySharpnessBasisMatrix n) ∈
        Matrix.unitaryGroup (Fin 3) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    simpa using (Matrix.mem_unitaryGroup_iff'.mp hQ)
  exact (Matrix.unitaryGroup (Fin 3) ℂ).mul_mem
    ((Matrix.unitaryGroup (Fin 3) ℂ).mul_mem hQ hR) hQstar

/-- Bundled continuous unitary on H 3. -/
noncomputable def stabilitySharpnessRotationUnitary (n m : ℕ) :
    unitary (H 3 →L[ℂ] H 3) := by
  refine ⟨Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ)
    (stabilitySharpnessRotationMatrix n m), ?_⟩
  have h := stabilitySharpnessRotationMatrix_mem_unitary n m
  rw [Unitary.mem_iff] at h ⊢
  constructor
  · simpa only [map_star, map_mul, map_one] using congrArg
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ)) h.1
  · simpa only [map_star, map_mul, map_one] using congrArg
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ)) h.2

/-- The three-dimensional sharpness rotation as a linear isometry equivalence. -/
noncomputable def stabilitySharpnessRotation (n m : ℕ) :
    H 3 ≃ₗᵢ[ℂ] H 3 :=
  Unitary.linearIsometryEquiv (stabilitySharpnessRotationUnitary n m)

end
end EverettianDecoherence.Approximation

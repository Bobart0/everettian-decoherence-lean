import EverettianDecoherence.Approximation.StabilitySharpness.Perspective3

/-!
**FR.** Coefficients fermés de la rotation tridimensionnelle de sharpness.
Avec d_m = 1-c_m, la matrice Q_n R_m Q_n^* possède les coefficients attendus
de la rotation du plan engendré par u_n=(A_n,B_n,0) et e_2.

**EN.** Closed coefficients of the three-dimensional stability-sharpness
rotation. With d_m = 1-c_m, the matrix Q_n R_m Q_n^* has the expected entries
for the rotation of the plane spanned by u_n=(A_n,B_n,0) and e_2.
-/

namespace EverettianDecoherence.Approximation

open EverettianDecoherence.Metrics Gleason
open scoped Matrix

noncomputable section

def stabilitySharpnessD (m : ℕ) : ℝ :=
  1 - iterationSharpnessC m

@[simp] theorem stabilitySharpnessRotationMatrix_00 (n m : ℕ) :
    stabilitySharpnessRotationMatrix n m (0 : Fin 3) (0 : Fin 3) =
      (1 - stabilitySharpnessD m * stabilitySharpnessA n ^ 2 : ℝ) := by
  unfold stabilitySharpnessRotationMatrix stabilitySharpnessBasisMatrix
    stabilitySharpnessPlaneRotationMatrix stabilitySharpnessD
  simp [Matrix.mul_apply, Fin.sum_univ_three]
  ring

@[simp] theorem stabilitySharpnessRotationMatrix_01 (n m : ℕ) :
    stabilitySharpnessRotationMatrix n m (0 : Fin 3) (1 : Fin 3) =
      (-(stabilitySharpnessD m * stabilitySharpnessA n *
        stabilitySharpnessB n) : ℝ) := by
  unfold stabilitySharpnessRotationMatrix stabilitySharpnessBasisMatrix
    stabilitySharpnessPlaneRotationMatrix stabilitySharpnessD
  simp [Matrix.mul_apply, Fin.sum_univ_three]
  ring

@[simp] theorem stabilitySharpnessRotationMatrix_02 (n m : ℕ) :
    stabilitySharpnessRotationMatrix n m (0 : Fin 3) (2 : Fin 3) =
      (-(iterationSharpnessS m * stabilitySharpnessA n) : ℝ) := by
  unfold stabilitySharpnessRotationMatrix stabilitySharpnessBasisMatrix
    stabilitySharpnessPlaneRotationMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_three]
  ring

@[simp] theorem stabilitySharpnessRotationMatrix_10 (n m : ℕ) :
    stabilitySharpnessRotationMatrix n m (1 : Fin 3) (0 : Fin 3) =
      (-(stabilitySharpnessD m * stabilitySharpnessA n *
        stabilitySharpnessB n) : ℝ) := by
  unfold stabilitySharpnessRotationMatrix stabilitySharpnessBasisMatrix
    stabilitySharpnessPlaneRotationMatrix stabilitySharpnessD
  simp [Matrix.mul_apply, Fin.sum_univ_three]
  ring

@[simp] theorem stabilitySharpnessRotationMatrix_11 (n m : ℕ) :
    stabilitySharpnessRotationMatrix n m (1 : Fin 3) (1 : Fin 3) =
      (1 - stabilitySharpnessD m * stabilitySharpnessB n ^ 2 : ℝ) := by
  unfold stabilitySharpnessRotationMatrix stabilitySharpnessBasisMatrix
    stabilitySharpnessPlaneRotationMatrix stabilitySharpnessD
  simp [Matrix.mul_apply, Fin.sum_univ_three]
  ring

@[simp] theorem stabilitySharpnessRotationMatrix_12 (n m : ℕ) :
    stabilitySharpnessRotationMatrix n m (1 : Fin 3) (2 : Fin 3) =
      (-(iterationSharpnessS m * stabilitySharpnessB n) : ℝ) := by
  unfold stabilitySharpnessRotationMatrix stabilitySharpnessBasisMatrix
    stabilitySharpnessPlaneRotationMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_three]
  ring

@[simp] theorem stabilitySharpnessRotationMatrix_20 (n m : ℕ) :
    stabilitySharpnessRotationMatrix n m (2 : Fin 3) (0 : Fin 3) =
      (iterationSharpnessS m * stabilitySharpnessA n : ℝ) := by
  unfold stabilitySharpnessRotationMatrix stabilitySharpnessBasisMatrix
    stabilitySharpnessPlaneRotationMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_three]
  ring

@[simp] theorem stabilitySharpnessRotationMatrix_21 (n m : ℕ) :
    stabilitySharpnessRotationMatrix n m (2 : Fin 3) (1 : Fin 3) =
      (iterationSharpnessS m * stabilitySharpnessB n : ℝ) := by
  unfold stabilitySharpnessRotationMatrix stabilitySharpnessBasisMatrix
    stabilitySharpnessPlaneRotationMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_three]
  ring

@[simp] theorem stabilitySharpnessRotationMatrix_22 (n m : ℕ) :
    stabilitySharpnessRotationMatrix n m (2 : Fin 3) (2 : Fin 3) =
      (iterationSharpnessC m : ℝ) := by
  unfold stabilitySharpnessRotationMatrix stabilitySharpnessBasisMatrix
    stabilitySharpnessPlaneRotationMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_three]
  ring

end
end EverettianDecoherence.Approximation

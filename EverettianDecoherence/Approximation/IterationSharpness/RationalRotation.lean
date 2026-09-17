import EverettianDecoherence.Approximation.IterationSharpness.RotationParameters
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
**FR.** Deuxième brique de T3. On construit la rotation rationnelle de `H 2`
associée aux paramètres `iterationSharpnessC n` et `iterationSharpnessS n`.
La construction est purement algébrique : une matrice unitaire réelle vue sur
`ℂ`, puis son transport canonique en `LinearIsometryEquiv`. Aucune quantité
BORN-SENSITIVE n'est introduite dans ce module.

**EN.** Second T3 building block. We construct the rational rotation of `H 2`
associated with `iterationSharpnessC n` and `iterationSharpnessS n`. The
construction is purely algebraic: a real unitary matrix viewed over `ℂ`, then
its canonical transport to a `LinearIsometryEquiv`. No BORN-SENSITIVE quantity
is introduced in this module.
-/

namespace EverettianDecoherence.Approximation

open EverettianDecoherence.Metrics Gleason
open scoped Matrix

noncomputable section

/-- The explicit two-dimensional rational rotation matrix. -/
def iterationSharpnessRotationMatrix (n : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(iterationSharpnessC n : ℂ), -(iterationSharpnessS n : ℂ);
     (iterationSharpnessS n : ℂ),  (iterationSharpnessC n : ℂ)]

/-- Complex form of the exact unit-circle identity for the rotation parameters. -/
theorem iterationSharpnessC_sq_add_S_sq_complex (n : ℕ) :
    (iterationSharpnessC n : ℂ) ^ 2 + (iterationSharpnessS n : ℂ) ^ 2 = 1 := by
  exact_mod_cast iterationSharpnessC_sq_add_S_sq n

/-- The explicit rational rotation matrix is unitary. -/
theorem iterationSharpnessRotationMatrix_mem_unitary (n : ℕ) :
    iterationSharpnessRotationMatrix n ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [iterationSharpnessRotationMatrix, Matrix.mul_apply, Fin.sum_univ_two, pow_two]
      using iterationSharpnessC_sq_add_S_sq_complex n
  · simp [iterationSharpnessRotationMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [iterationSharpnessRotationMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simpa [iterationSharpnessRotationMatrix, Matrix.mul_apply, Fin.sum_univ_two, pow_two, add_comm]
      using iterationSharpnessC_sq_add_S_sq_complex n

/-- The same rotation, bundled as a unitary continuous linear operator on `H 2`. -/
noncomputable def iterationSharpnessRotationUnitary (n : ℕ) :
    unitary (H 2 →L[ℂ] H 2) := by
  refine ⟨Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
    (iterationSharpnessRotationMatrix n), ?_⟩
  have h := iterationSharpnessRotationMatrix_mem_unitary n
  rw [Unitary.mem_iff] at h ⊢
  constructor
  · simpa only [map_star, map_mul, map_one] using congrArg
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)) h.1
  · simpa only [map_star, map_mul, map_one] using congrArg
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)) h.2

/-- The T3 rational rotation as the `LinearIsometryEquiv` expected by ED4. -/
noncomputable def iterationSharpnessRotation (n : ℕ) : H 2 ≃ₗᵢ[ℂ] H 2 :=
  Unitary.linearIsometryEquiv (iterationSharpnessRotationUnitary n)

/-- First coordinate of the rational rotation. -/
@[simp] theorem iterationSharpnessRotation_zero (n : ℕ) (x : H 2) :
    iterationSharpnessRotation n x (0 : Fin 2) =
      (iterationSharpnessC n : ℂ) * x (0 : Fin 2) -
        (iterationSharpnessS n : ℂ) * x (1 : Fin 2) := by
  change (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
    (iterationSharpnessRotationMatrix n) x).ofLp (0 : Fin 2) = _
  rw [Matrix.ofLp_toEuclideanCLM]
  simp [iterationSharpnessRotationMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, sub_eq_add_neg]

/-- Second coordinate of the rational rotation. -/
@[simp] theorem iterationSharpnessRotation_one (n : ℕ) (x : H 2) :
    iterationSharpnessRotation n x (1 : Fin 2) =
      (iterationSharpnessS n : ℂ) * x (0 : Fin 2) +
        (iterationSharpnessC n : ℂ) * x (1 : Fin 2) := by
  change (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
    (iterationSharpnessRotationMatrix n) x).ofLp (1 : Fin 2) = _
  rw [Matrix.ofLp_toEuclideanCLM]
  simp [iterationSharpnessRotationMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

end
end EverettianDecoherence.Approximation

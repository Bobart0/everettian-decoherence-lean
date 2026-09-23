import EverettianDecoherence.Approximation.StabilitySharpness.DiffuseFamilyGeometry

/-!
**FR.** Décomposition des vecteurs coordonnées de la famille diffuse en une
composante sur le mode uniforme de leur demi-bloc et un résidu orthogonal aux
deux modes.  Le résidu est fixé par la rotation diffuse, ce qui donne le
coefficient diagonal exact sans calcul matriciel 2m x 2m.

**EN.** Decomposition of diffuse coordinate vectors into their half-block
uniform-mode component and a residual orthogonal to both uniform modes.  The
residual is fixed by the diffuse rotation, yielding the exact diagonal
coefficient without a 2m-by-2m matrix calculation.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open scoped Classical InnerProductSpace BigOperators

noncomputable section

noncomputable def diffuseLeftResidual
    (m : ℕ) (i : Fin m) : H (m + m) :=
  diffuseLeftFamily m i -
    (diffuseModeScale m : ℂ) • diffuseLeftMode m

noncomputable def diffuseRightResidual
    (m : ℕ) (i : Fin m) : H (m + m) :=
  diffuseRightFamily m i -
    (diffuseModeScale m : ℂ) • diffuseRightMode m

theorem diffuseLeftFamily_decomp
    (m : ℕ) (i : Fin m) :
    diffuseLeftFamily m i =
      (diffuseModeScale m : ℂ) • diffuseLeftMode m +
        diffuseLeftResidual m i := by
  unfold diffuseLeftResidual
  module

theorem diffuseRightFamily_decomp
    (m : ℕ) (i : Fin m) :
    diffuseRightFamily m i =
      (diffuseModeScale m : ℂ) • diffuseRightMode m +
        diffuseRightResidual m i := by
  unfold diffuseRightResidual
  module

theorem diffuseLeftMode_inner_leftResidual
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    inner ℂ (diffuseLeftMode m) (diffuseLeftResidual m i) = 0 := by
  unfold diffuseLeftResidual
  rw [inner_sub_right, inner_smul_right,
    diffuseLeftMode_inner_leftFamily hm i,
    inner_self_eq_norm_sq_to_K, diffuseLeftMode_norm hm]
  simp

theorem diffuseRightMode_inner_leftResidual
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    inner ℂ (diffuseRightMode m) (diffuseLeftResidual m i) = 0 := by
  unfold diffuseLeftResidual
  rw [inner_sub_right, inner_smul_right,
    diffuseRightMode_inner_leftFamily hm i,
    diffuseRightMode_inner_leftMode hm]
  simp

theorem diffuseLeftMode_inner_rightResidual
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    inner ℂ (diffuseLeftMode m) (diffuseRightResidual m i) = 0 := by
  unfold diffuseRightResidual
  rw [inner_sub_right, inner_smul_right,
    diffuseLeftMode_inner_rightFamily hm i,
    diffuseLeftMode_inner_rightMode hm]
  simp

theorem diffuseRightMode_inner_rightResidual
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    inner ℂ (diffuseRightMode m) (diffuseRightResidual m i) = 0 := by
  unfold diffuseRightResidual
  rw [inner_sub_right, inner_smul_right,
    diffuseRightMode_inner_rightFamily hm i,
    inner_self_eq_norm_sq_to_K, diffuseRightMode_norm hm]
  simp

theorem diffuseRotation_apply_leftResidual
    {m : ℕ} (hm : 0 < m) (θ : ℝ) (i : Fin m) :
    diffuseRotation m θ (diffuseLeftResidual m i) =
      diffuseLeftResidual m i :=
  diffuseRotation_apply_of_orthogonal hm θ (diffuseLeftResidual m i)
    (diffuseLeftMode_inner_leftResidual hm i)
    (diffuseRightMode_inner_leftResidual hm i)

theorem diffuseRotation_apply_rightResidual
    {m : ℕ} (hm : 0 < m) (θ : ℝ) (i : Fin m) :
    diffuseRotation m θ (diffuseRightResidual m i) =
      diffuseRightResidual m i :=
  diffuseRotation_apply_of_orthogonal hm θ (diffuseRightResidual m i)
    (diffuseLeftMode_inner_rightResidual hm i)
    (diffuseRightMode_inner_rightResidual hm i)

theorem diffuseLeftFamily_inner_leftResidual
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    inner ℂ (diffuseLeftFamily m i) (diffuseLeftResidual m i) =
      1 - (diffuseModeScale m : ℂ) ^ 2 := by
  unfold diffuseLeftResidual
  rw [inner_sub_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K,
    (diffuseLeftFamily_orthonormal m).1 i,
    diffuseLeftFamily_inner_leftMode hm i]
  norm_num
  ring

theorem diffuseRightFamily_inner_rightResidual
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    inner ℂ (diffuseRightFamily m i) (diffuseRightResidual m i) =
      1 - (diffuseModeScale m : ℂ) ^ 2 := by
  unfold diffuseRightResidual
  rw [inner_sub_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K,
    (diffuseRightFamily_orthonormal m).1 i,
    diffuseRightFamily_inner_rightMode hm i]
  norm_num
  ring

theorem diffuseRotation_apply_leftFamily
    {m : ℕ} (hm : 0 < m) (θ : ℝ) (i : Fin m) :
    diffuseRotation m θ (diffuseLeftFamily m i) =
      ((diffuseModeScale m : ℂ) * (Real.cos θ : ℂ)) •
          diffuseLeftMode m +
        ((diffuseModeScale m : ℂ) * (Real.sin θ : ℂ)) •
          diffuseRightMode m +
        diffuseLeftResidual m i := by
  rw [diffuseLeftFamily_decomp m i]
  simp only [map_add, map_smul]
  rw [diffuseRotation_apply_left hm θ,
    diffuseRotation_apply_leftResidual hm θ i]
  module

theorem diffuseRotation_apply_rightFamily
    {m : ℕ} (hm : 0 < m) (θ : ℝ) (i : Fin m) :
    diffuseRotation m θ (diffuseRightFamily m i) =
      -((diffuseModeScale m : ℂ) * (Real.sin θ : ℂ)) •
          diffuseLeftMode m +
        ((diffuseModeScale m : ℂ) * (Real.cos θ : ℂ)) •
          diffuseRightMode m +
        diffuseRightResidual m i := by
  rw [diffuseRightFamily_decomp m i]
  simp only [map_add, map_smul]
  rw [diffuseRotation_apply_right hm θ,
    diffuseRotation_apply_rightResidual hm θ i]
  module

theorem diffuseLeftFamily_diagonal
    {m : ℕ} (hm : 0 < m) (θ : ℝ) (i : Fin m) :
    inner ℂ (diffuseLeftFamily m i)
        (diffuseRotation m θ (diffuseLeftFamily m i)) =
      1 - (diffuseModeScale m : ℂ) ^ 2 *
        (1 - (Real.cos θ : ℂ)) := by
  rw [diffuseRotation_apply_leftFamily hm θ i]
  simp only [inner_add_right, inner_smul_right]
  rw [diffuseLeftFamily_inner_leftMode hm i,
    diffuseLeftFamily_inner_rightMode hm i,
    diffuseLeftFamily_inner_leftResidual hm i]
  ring

theorem diffuseRightFamily_diagonal
    {m : ℕ} (hm : 0 < m) (θ : ℝ) (i : Fin m) :
    inner ℂ (diffuseRightFamily m i)
        (diffuseRotation m θ (diffuseRightFamily m i)) =
      1 - (diffuseModeScale m : ℂ) ^ 2 *
        (1 - (Real.cos θ : ℂ)) := by
  rw [diffuseRotation_apply_rightFamily hm θ i]
  simp only [inner_add_right, inner_smul_right]
  rw [diffuseRightFamily_inner_leftMode hm i,
    diffuseRightFamily_inner_rightMode hm i,
    diffuseRightFamily_inner_rightResidual hm i]
  ring

end
end EverettianDecoherence.Approximation

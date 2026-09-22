import EverettianDecoherence.Approximation.StabilitySharpness.DiffuseFamilyCenteredNorm
import EverettianDecoherence.Approximation.StabilitySharpness.DiffuseFamilyCellInvariants
import EverettianDecoherence.Approximation.CutEnvelope

/-!
Exact maximal cut for the diffuse family.  The upper bound uses the generic
centered-operator estimate; the lower bound is attained by the cut containing
the first half of the coordinate cells.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped Classical InnerProductSpace BigOperators

noncomputable section

noncomputable def diffuseLeftCut (m : ℕ) :
    Finset ((Projective.interface (m + m)).Cell
      (coordinatePerspective (m + m))) :=
  Finset.univ.image fun i : Fin m =>
    coordinateCell (Fin.castAdd m i)

theorem coordinateLeftCell_mem_diffuseLeftCut
    (m : ℕ) (i : Fin m) :
    (coordinateCell (Fin.castAdd m i) :
      (Projective.interface (m + m)).Cell
        (coordinatePerspective (m + m))) ∈ diffuseLeftCut m := by
  simp [diffuseLeftCut]

theorem diffuseLeftFamily_mem_leftCutSubspace
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    diffuseLeftFamily m i ∈
      recordSubsetSubspace (coordinatePerspective (m + m))
        (diffuseLeftCut m) := by
  let c :
      (Projective.interface (m + m)).Cell
        (coordinatePerspective (m + m)) :=
    coordinateCell (Fin.castAdd m i)
  have hc : c ∈ diffuseLeftCut m := by
    dsimp [c]
    exact coordinateLeftCell_mem_diffuseLeftCut m i
  have hle :=
    recordCell_le_recordSubsetSubspace
      (coordinatePerspective (m + m)) (diffuseLeftCut m) c hc
  have hmem : diffuseLeftFamily m i ∈ c.val := by
    dsimp [c]
    rw [diffuseLeftCell_val]
    exact Submodule.mem_span_singleton_self _
  exact hle hmem

theorem diffuseLeftMode_mem_leftCutSubspace
    {m : ℕ} (hm : 0 < m) :
    diffuseLeftMode m ∈
      recordSubsetSubspace (coordinatePerspective (m + m))
        (diffuseLeftCut m) := by
  unfold diffuseLeftMode diffuseLeftSum
  apply Submodule.smul_mem
  exact Submodule.sum_mem _ fun i _ =>
    diffuseLeftFamily_mem_leftCutSubspace hm i

theorem diffuseLeftCut_projector_leftMode
    {m : ℕ} (hm : 0 < m) :
    Gleason.projL
        (recordSubsetSubspace (coordinatePerspective (m + m))
          (diffuseLeftCut m))
        (diffuseLeftMode m) =
      diffuseLeftMode m := by
  unfold Gleason.projL
  exact Submodule.starProjection_eq_self_iff.mpr
    (diffuseLeftMode_mem_leftCutSubspace hm)

theorem coordinateLeftCell_projector_rightMode
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    Gleason.projL
        (coordinateCell (Fin.castAdd m i) :
          (Projective.interface (m + m)).Cell
            (coordinatePerspective (m + m))).val
        (diffuseRightMode m) = 0 := by
  rw [diffuseLeftCell_val]
  change (ℂ ∙ diffuseLeftFamily m i).starProjection
      (diffuseRightMode m) = 0
  rw [Submodule.starProjection_unit_singleton ℂ
    ((diffuseLeftFamily_orthonormal m).1 i)]
  rw [diffuseLeftFamily_inner_rightMode hm i]
  simp

theorem diffuseLeftCut_projector_rightMode
    {m : ℕ} (hm : 0 < m) :
    Gleason.projL
        (recordSubsetSubspace (coordinatePerspective (m + m))
          (diffuseLeftCut m))
        (diffuseRightMode m) = 0 := by
  rw [recordSubsetProjector_eq_sum]
  simp only [LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro c hc
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hc
  exact coordinateLeftCell_projector_rightMode hm i

theorem diffuseLeftCut_projector_rotatedLeft
    {m : ℕ} (hm : 0 < m) (θ : ℝ) :
    Gleason.projL
        (recordSubsetSubspace (coordinatePerspective (m + m))
          (diffuseLeftCut m))
        (diffuseRotation m θ (diffuseLeftMode m)) =
      (Real.cos θ : ℂ) • diffuseLeftMode m := by
  rw [diffuseRotation_apply_left hm θ, map_add, map_smul, map_smul,
    diffuseLeftCut_projector_leftMode hm,
    diffuseLeftCut_projector_rightMode hm]
  simp

theorem diffuseLeftCut_commutator_apply_leftMode
    {m : ℕ} (hm : 0 < m) (θ : ℝ) :
    recordSubsetProjectorCommutatorCLM
        (coordinatePerspective (m + m)) (diffuseRotation m θ)
        (diffuseLeftCut m) (diffuseLeftMode m) =
      - (Real.sin θ : ℂ) • diffuseRightMode m := by
  rw [recordSubsetProjectorCommutatorCLM_apply,
    recordSubsetProjectorCommutator_apply,
    diffuseLeftCut_projector_rotatedLeft hm θ,
    diffuseLeftCut_projector_leftMode hm,
    diffuseRotation_apply_left hm θ]
  module

theorem sin_le_diffuseLeftCut_commutator_norm
    {m : ℕ} (hm : 0 < m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi2 : θ < Real.pi / 2) :
    Real.sin θ ≤
      ‖recordSubsetProjectorCommutatorCLM
        (coordinatePerspective (m + m)) (diffuseRotation m θ)
        (diffuseLeftCut m)‖ := by
  have hθpi : θ < Real.pi := by
    linarith [Real.pi_pos]
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 hθpi
  have h :=
    (recordSubsetProjectorCommutatorCLM
      (coordinatePerspective (m + m)) (diffuseRotation m θ)
      (diffuseLeftCut m)).le_opNorm (diffuseLeftMode m)
  rw [diffuseLeftCut_commutator_apply_leftMode hm θ,
    norm_neg, norm_smul, diffuseLeftMode_norm hm] at h
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsin] using h

theorem sin_le_diffuseMaxCut
    {m : ℕ} (hm : 0 < m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi2 : θ < Real.pi / 2) :
    Real.sin θ ≤
      maxSubsetCommutatorOpNorm
        (coordinatePerspective (m + m)) (diffuseRotation m θ) := by
  exact (sin_le_diffuseLeftCut_commutator_norm hm hθ0 hθpi2).trans
    (subsetCommutatorOpNorm_le_max
      (coordinatePerspective (m + m)) (diffuseRotation m θ)
      (diffuseLeftCut m))

theorem diffuseMaxCut_le_sin
    {m : ℕ} (hm : 0 < m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi2 : θ < Real.pi / 2) :
    maxSubsetCommutatorOpNorm
        (coordinatePerspective (m + m)) (diffuseRotation m θ) ≤
      Real.sin θ := by
  calc
    maxSubsetCommutatorOpNorm
        (coordinatePerspective (m + m)) (diffuseRotation m θ)
      ≤ ‖centeredUnitaryCLM (diffuseRotation m θ) (Real.cos θ : ℂ)‖ :=
        maxSubsetCommutatorOpNorm_le_centered
          (coordinatePerspective (m + m)) (diffuseRotation m θ)
          (Real.cos θ : ℂ)
    _ = Real.sin θ :=
      diffuseCentered_norm_eq_sin hm hθ0 hθpi2

theorem diffuseMaxCut_eq_sin
    {m : ℕ} (hm : 0 < m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi2 : θ < Real.pi / 2) :
    maxSubsetCommutatorOpNorm
        (coordinatePerspective (m + m)) (diffuseRotation m θ) =
      Real.sin θ := by
  exact le_antisymm
    (diffuseMaxCut_le_sin hm hθ0 hθpi2)
    (sin_le_diffuseMaxCut hm hθ0 hθpi2)

theorem diffuseMaxCut_sq_eq
    {m : ℕ} (hm : 0 < m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi2 : θ < Real.pi / 2) :
    maxSubsetCommutatorOpNorm
        (coordinatePerspective (m + m)) (diffuseRotation m θ) ^ 2 =
      v18DiffuseMaxCutSq (diffuseAngularDefect θ) := by
  rw [diffuseMaxCut_eq_sin hm hθ0 hθpi2]
  unfold v18DiffuseMaxCutSq diffuseAngularDefect
  have htrig := Real.sin_sq_add_cos_sq θ
  nlinarith

end
end EverettianDecoherence.Approximation

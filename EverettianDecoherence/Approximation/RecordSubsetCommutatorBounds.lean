import EverettianDecoherence.Approximation.RecordSubsetProjectorCommutator
import EverettianDecoherence.Approximation.SubsetCommutatorBudget
import EverettianDecoherence.Approximation.OperatorNormProjectorCommutator

/-!
**FR.** Bornes quadratiques sur les deux blocs croisés associés à un
sous-ensemble de cellules. Cette couche reste algébrique et NON BORN-SENSITIVE.

**EN.** Quadratic bounds for the two cross blocks associated with a subset of
cells. This layer remains algebraic and NON BORN-SENSITIVE.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical InnerProductSpace

noncomputable section

private theorem cell_commutator_on_complement_projection
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : (Projective.interface n).Cell D) (hc : c ∈ S) (x : H n) :
    perspectiveProjectorCommutator D U c
        (Gleason.projL (recordSubsetSubspace D Sᶜ) x) =
      Gleason.projL c.val
        (U (Gleason.projL (recordSubsetSubspace D Sᶜ) x)) := by
  rw [perspectiveProjectorCommutator_apply,
    recordCellProjector_compl_apply_eq_zero_of_mem D S c hc x,
    map_zero, sub_zero]

private theorem cell_commutator_on_subset_projection_of_mem_compl
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : (Projective.interface n).Cell D) (hc : c ∈ Sᶜ) (x : H n) :
    perspectiveProjectorCommutator D U c
        (Gleason.projL (recordSubsetSubspace D S) x) =
      Gleason.projL c.val
        (U (Gleason.projL (recordSubsetSubspace D S) x)) := by
  rw [perspectiveProjectorCommutator_apply,
    recordCellProjector_apply_eq_zero_of_mem_compl D S c hc x,
    map_zero, sub_zero]

/-- Output-side bound for the block entering `S`. -/
theorem norm_sq_recordSubsetIncoming_le_subsetSq_mul_compl_norm_sq
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    ‖recordSubsetIncoming D U S x‖ ^ 2 ≤
      subsetProjectorCommutatorOpNormSq D U S *
        ‖Gleason.projL (recordSubsetSubspace D Sᶜ) x‖ ^ 2 := by
  unfold recordSubsetIncoming
  rw [norm_sq_recordSubsetProjector_eq_sum D S
    (U (Gleason.projL (recordSubsetSubspace D Sᶜ) x))]
  calc
    (∑ c ∈ S,
        ‖Gleason.projL c.val
          (U (Gleason.projL (recordSubsetSubspace D Sᶜ) x))‖ ^ 2) ≤
      ∑ c ∈ S,
        (perspectiveProjectorCommutatorOpNormProfile D U c *
          ‖Gleason.projL (recordSubsetSubspace D Sᶜ) x‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro c hc
      have hle :=
        perspectiveProjectorCommutatorNormProfile_le_opNorm_mul_norm
          D U (Gleason.projL (recordSubsetSubspace D Sᶜ) x) c
      unfold perspectiveProjectorCommutatorNormProfile at hle
      rw [cell_commutator_on_complement_projection D U S c hc x] at hle
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg
          (perspectiveProjectorCommutatorOpNormProfile_nonneg D U c)
          (norm_nonneg _))).2 hle
    _ = subsetProjectorCommutatorOpNormSq D U S *
        ‖Gleason.projL (recordSubsetSubspace D Sᶜ) x‖ ^ 2 := by
      unfold subsetProjectorCommutatorOpNormSq
      simp_rw [mul_pow]
      rw [Finset.sum_mul]

/-- Output-side bound for the block leaving `S`. -/
theorem norm_sq_recordSubsetOutgoing_le_complSq_mul_subset_norm_sq
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    ‖recordSubsetOutgoing D U S x‖ ^ 2 ≤
      subsetProjectorCommutatorOpNormSq D U Sᶜ *
        ‖Gleason.projL (recordSubsetSubspace D S) x‖ ^ 2 := by
  unfold recordSubsetOutgoing
  rw [norm_sq_recordSubsetProjector_eq_sum D Sᶜ
    (U (Gleason.projL (recordSubsetSubspace D S) x))]
  calc
    (∑ c ∈ Sᶜ,
        ‖Gleason.projL c.val
          (U (Gleason.projL (recordSubsetSubspace D S) x))‖ ^ 2) ≤
      ∑ c ∈ Sᶜ,
        (perspectiveProjectorCommutatorOpNormProfile D U c *
          ‖Gleason.projL (recordSubsetSubspace D S) x‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro c hc
      have hle :=
        perspectiveProjectorCommutatorNormProfile_le_opNorm_mul_norm
          D U (Gleason.projL (recordSubsetSubspace D S) x) c
      unfold perspectiveProjectorCommutatorNormProfile at hle
      rw [cell_commutator_on_subset_projection_of_mem_compl D U S c hc x] at hle
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg
          (perspectiveProjectorCommutatorOpNormProfile_nonneg D U c)
          (norm_nonneg _))).2 hle
    _ = subsetProjectorCommutatorOpNormSq D U Sᶜ *
        ‖Gleason.projL (recordSubsetSubspace D S) x‖ ^ 2 := by
      unfold subsetProjectorCommutatorOpNormSq
      simp_rw [mul_pow]
      rw [Finset.sum_mul]

end
end EverettianDecoherence.Approximation

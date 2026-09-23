import EverettianDecoherence.Approximation.RecordSubsetCrossBlockOpNorm
import EverettianDecoherence.Approximation.CutEnvelope
import EverettianDecoherence.Metrics.RecordSubsetProjector

/-!
Generic centered-operator bound for aggregate cut commutators.
For every scalar c, the cross blocks of U and U - c I coincide, hence
the cut commutator norm is bounded by ||U - c I||.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped Classical InnerProductSpace

noncomputable section

noncomputable def centeredUnitaryCLM
    {n : ℕ} (U : H n ≃ₗᵢ[ℂ] H n) (c : ℂ) :
    H n →L[ℂ] H n :=
  U.toLinearIsometry.toContinuousLinearMap -
    c • ContinuousLinearMap.id ℂ (H n)

@[simp]
theorem centeredUnitaryCLM_apply
    {n : ℕ} (U : H n ≃ₗᵢ[ℂ] H n) (c : ℂ) (x : H n) :
    centeredUnitaryCLM U c x = U x - c • x := by
  rfl

theorem recordSubsetProjector_apply_compl_projector_eq_zero
    {n : ℕ} (D : Perspective n)
    (S : Finset ((Projective.interface n).Cell D))
    (x : H n) :
    Gleason.projL (recordSubsetSubspace D S)
        (Gleason.projL (recordSubsetSubspace D Sᶜ) x) = 0 := by
  rw [recordSubsetProjector_compl_apply_eq_sub D S x, map_sub]
  have hidem :
      Gleason.projL (recordSubsetSubspace D S)
          (Gleason.projL (recordSubsetSubspace D S) x) =
        Gleason.projL (recordSubsetSubspace D S) x := by
    unfold Gleason.projL
    exact Submodule.starProjection_eq_self_iff.mpr
      (Submodule.starProjection_apply_mem (recordSubsetSubspace D S) x)
  rw [hidem, sub_self]

theorem recordSubsetComplementProjector_apply_projector_eq_zero
    {n : ℕ} (D : Perspective n)
    (S : Finset ((Projective.interface n).Cell D))
    (x : H n) :
    Gleason.projL (recordSubsetSubspace D Sᶜ)
        (Gleason.projL (recordSubsetSubspace D S) x) = 0 := by
  simpa using
    (recordSubsetProjector_apply_compl_projector_eq_zero D Sᶜ x)

theorem recordSubsetIncoming_eq_centered
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : ℂ) (x : H n) :
    recordSubsetIncoming D U S x =
      Gleason.projL (recordSubsetSubspace D S)
        (centeredUnitaryCLM U c
          (Gleason.projL (recordSubsetSubspace D Sᶜ) x)) := by
  unfold recordSubsetIncoming
  rw [centeredUnitaryCLM_apply, map_sub, map_smul,
    recordSubsetProjector_apply_compl_projector_eq_zero]
  simp

theorem recordSubsetOutgoing_eq_centered
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : ℂ) (x : H n) :
    recordSubsetOutgoing D U S x =
      Gleason.projL (recordSubsetSubspace D Sᶜ)
        (centeredUnitaryCLM U c
          (Gleason.projL (recordSubsetSubspace D S) x)) := by
  unfold recordSubsetOutgoing
  rw [centeredUnitaryCLM_apply, map_sub, map_smul,
    recordSubsetComplementProjector_apply_projector_eq_zero]
  simp

theorem recordSubsetIncomingCLM_opNorm_le_centered
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : ℂ) :
    ‖recordSubsetIncomingCLM D U S‖ ≤
      ‖centeredUnitaryCLM U c‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [recordSubsetIncomingCLM_apply,
    recordSubsetIncoming_eq_centered D U S c x]
  calc
    ‖Gleason.projL (recordSubsetSubspace D S)
        (centeredUnitaryCLM U c
          (Gleason.projL (recordSubsetSubspace D Sᶜ) x))‖ ≤
        ‖centeredUnitaryCLM U c
          (Gleason.projL (recordSubsetSubspace D Sᶜ) x)‖ := by
      unfold Gleason.projL
      exact Submodule.norm_starProjection_apply_le _ _
    _ ≤ ‖centeredUnitaryCLM U c‖ *
        ‖Gleason.projL (recordSubsetSubspace D Sᶜ) x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖centeredUnitaryCLM U c‖ * ‖x‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      unfold Gleason.projL
      exact Submodule.norm_starProjection_apply_le _ _

theorem recordSubsetOutgoingCLM_opNorm_le_centered
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : ℂ) :
    ‖recordSubsetOutgoingCLM D U S‖ ≤
      ‖centeredUnitaryCLM U c‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [recordSubsetOutgoingCLM_apply,
    recordSubsetOutgoing_eq_centered D U S c x]
  calc
    ‖Gleason.projL (recordSubsetSubspace D Sᶜ)
        (centeredUnitaryCLM U c
          (Gleason.projL (recordSubsetSubspace D S) x))‖ ≤
        ‖centeredUnitaryCLM U c
          (Gleason.projL (recordSubsetSubspace D S) x)‖ := by
      unfold Gleason.projL
      exact Submodule.norm_starProjection_apply_le _ _
    _ ≤ ‖centeredUnitaryCLM U c‖ *
        ‖Gleason.projL (recordSubsetSubspace D S) x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖centeredUnitaryCLM U c‖ * ‖x‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      unfold Gleason.projL
      exact Submodule.norm_starProjection_apply_le _ _

theorem recordSubsetProjectorCommutatorCLM_opNorm_le_centered
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : ℂ) :
    ‖recordSubsetProjectorCommutatorCLM D U S‖ ≤
      ‖centeredUnitaryCLM U c‖ := by
  rw [recordSubsetProjectorCommutatorCLM_opNorm_eq_max_cross]
  exact max_le
    (recordSubsetIncomingCLM_opNorm_le_centered D U S c)
    (recordSubsetOutgoingCLM_opNorm_le_centered D U S c)

theorem maxSubsetCommutatorOpNorm_le_centered
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (c : ℂ) :
    maxSubsetCommutatorOpNorm D U ≤
      ‖centeredUnitaryCLM U c‖ := by
  obtain ⟨S, hS⟩ := exists_subsetCommutatorOpNorm_eq_max D U
  rw [← hS]
  exact recordSubsetProjectorCommutatorCLM_opNorm_le_centered D U S c

end
end EverettianDecoherence.Approximation

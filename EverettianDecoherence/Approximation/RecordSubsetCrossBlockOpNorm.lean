import EverettianDecoherence.Metrics.FiniteDimensionalOpNorm
import EverettianDecoherence.Approximation.RecordSubsetProjectorCommutator

/-!
**FR.** Blocs croisés continus associés à un sous-ensemble de cellules :
entrée depuis le complément et sortie vers le complément. Cette couche est
purement opératorielle et NON BORN-SENSITIVE.

**EN.** Continuous cross blocks associated with a subset of cells: incoming
from the complement and outgoing to the complement. This layer is purely
operator-theoretic and NON BORN-SENSITIVE.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped Classical

noncomputable section

/-- Continuous linear incoming cross block (P_S U P_{S^c}). -/
noncomputable def recordSubsetIncomingCLM
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    H n →L[ℂ] H n :=
  ((Gleason.projL (recordSubsetSubspace D S)).comp
    (U.toLinearEquiv.toLinearMap.comp
      (Gleason.projL (recordSubsetSubspace D Sᶜ)))).toContinuousLinearMap

@[simp]
theorem recordSubsetIncomingCLM_apply
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    recordSubsetIncomingCLM D U S x = recordSubsetIncoming D U S x := by
  rfl

/-- Continuous linear outgoing cross block (P_{S^c} U P_S). -/
noncomputable def recordSubsetOutgoingCLM
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    H n →L[ℂ] H n :=
  ((Gleason.projL (recordSubsetSubspace D Sᶜ)).comp
    (U.toLinearEquiv.toLinearMap.comp
      (Gleason.projL (recordSubsetSubspace D S)))).toContinuousLinearMap

@[simp]
theorem recordSubsetOutgoingCLM_apply
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    recordSubsetOutgoingCLM D U S x = recordSubsetOutgoing D U S x := by
  rfl

/-- Incoming and outgoing cross blocks are contractions. -/
theorem recordSubsetIncomingCLM_opNorm_le_one
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    ‖recordSubsetIncomingCLM D U S‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm zero_le_one
  intro x hx
  change
    ‖Gleason.projL (recordSubsetSubspace D S)
      (U (Gleason.projL (recordSubsetSubspace D Sᶜ) x))‖ ≤ 1
  calc
    ‖Gleason.projL (recordSubsetSubspace D S)
      (U (Gleason.projL (recordSubsetSubspace D Sᶜ) x))‖ ≤
        ‖U (Gleason.projL (recordSubsetSubspace D Sᶜ) x)‖ := by
      unfold Gleason.projL
      exact Submodule.norm_starProjection_apply_le _ _
    _ = ‖Gleason.projL (recordSubsetSubspace D Sᶜ) x‖ := U.norm_map _
    _ ≤ ‖x‖ := by
      unfold Gleason.projL
      exact Submodule.norm_starProjection_apply_le _ _
    _ = 1 := hx

theorem recordSubsetOutgoingCLM_opNorm_le_one
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    ‖recordSubsetOutgoingCLM D U S‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm zero_le_one
  intro x hx
  change
    ‖Gleason.projL (recordSubsetSubspace D Sᶜ)
      (U (Gleason.projL (recordSubsetSubspace D S) x))‖ ≤ 1
  calc
    ‖Gleason.projL (recordSubsetSubspace D Sᶜ)
      (U (Gleason.projL (recordSubsetSubspace D S) x))‖ ≤
        ‖U (Gleason.projL (recordSubsetSubspace D S) x)‖ := by
      unfold Gleason.projL
      exact Submodule.norm_starProjection_apply_le _ _
    _ = ‖Gleason.projL (recordSubsetSubspace D S) x‖ := U.norm_map _
    _ ≤ ‖x‖ := by
      unfold Gleason.projL
      exact Submodule.norm_starProjection_apply_le _ _
    _ = 1 := hx

end
end EverettianDecoherence.Approximation

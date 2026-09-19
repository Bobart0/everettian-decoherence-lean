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


/-- Continuous linear form of the aggregate subset-projector commutator. -/
noncomputable def recordSubsetProjectorCommutatorCLM
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    H n →L[ℂ] H n :=
  (recordSubsetProjectorCommutator D U S).toContinuousLinearMap

@[simp]
theorem recordSubsetProjectorCommutatorCLM_apply
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    recordSubsetProjectorCommutatorCLM D U S x =
      recordSubsetProjectorCommutator D U S x := by
  rfl

private theorem recordSubsetIncoming_project_compl
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    recordSubsetIncoming D U S
        (Gleason.projL (recordSubsetSubspace D Sᶜ) x) =
      recordSubsetIncoming D U S x := by
  unfold recordSubsetIncoming Gleason.projL
  rw [Submodule.starProjection_eq_self_iff.mpr
    (Submodule.starProjection_apply_mem (recordSubsetSubspace D Sᶜ) x)]

private theorem recordSubsetOutgoing_project
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    recordSubsetOutgoing D U S
        (Gleason.projL (recordSubsetSubspace D S) x) =
      recordSubsetOutgoing D U S x := by
  unfold recordSubsetOutgoing Gleason.projL
  rw [Submodule.starProjection_eq_self_iff.mpr
    (Submodule.starProjection_apply_mem (recordSubsetSubspace D S) x)]

private theorem norm_recordSubsetIncoming_le_commutator
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    ‖recordSubsetIncoming D U S x‖ ≤
      ‖recordSubsetProjectorCommutator D U S x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [norm_sq_recordSubsetProjectorCommutator_eq_cross_sum D U S x]
  exact le_add_of_nonneg_right (sq_nonneg _)

private theorem norm_recordSubsetOutgoing_le_commutator
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    ‖recordSubsetOutgoing D U S x‖ ≤
      ‖recordSubsetProjectorCommutator D U S x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [norm_sq_recordSubsetProjectorCommutator_eq_cross_sum D U S x]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- Each cross block has operator norm at most that of the aggregate
commutator. -/
theorem recordSubsetIncomingCLM_opNorm_le_commutator
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    ‖recordSubsetIncomingCLM D U S‖ ≤
      ‖recordSubsetProjectorCommutatorCLM D U S‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  exact (norm_recordSubsetIncoming_le_commutator D U S x).trans
    (ContinuousLinearMap.le_opNorm _ _)

theorem recordSubsetOutgoingCLM_opNorm_le_commutator
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    ‖recordSubsetOutgoingCLM D U S‖ ≤
      ‖recordSubsetProjectorCommutatorCLM D U S‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  exact (norm_recordSubsetOutgoing_le_commutator D U S x).trans
    (ContinuousLinearMap.le_opNorm _ _)

private theorem recordSubset_projection_norm_sq_add_compl
    {n : ℕ} (D : Perspective n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    ‖Gleason.projL (recordSubsetSubspace D S) x‖ ^ 2 +
        ‖Gleason.projL (recordSubsetSubspace D Sᶜ) x‖ ^ 2 =
      ‖x‖ ^ 2 := by
  rw [norm_sq_recordSubsetProjector_eq_sum D S x,
    norm_sq_recordSubsetProjector_eq_sum D Sᶜ x]
  have hsplit :
      (∑ c ∈ S, ‖Gleason.projL c.val x‖ ^ 2) +
          ∑ c ∈ Sᶜ, ‖Gleason.projL c.val x‖ ^ 2 =
        ∑ c : (Projective.interface n).Cell D,
          ‖Gleason.projL c.val x‖ ^ 2 :=
    S.sum_add_sum_compl (fun c => ‖Gleason.projL c.val x‖ ^ 2)
  have hall := sum_sq_recordCellNormProfile_eq_norm_sq D x
  change
    (∑ c : (Projective.interface n).Cell D,
      ‖Gleason.projL c.val x‖ ^ 2) = ‖x‖ ^ 2 at hall
  exact hsplit.trans hall

private theorem norm_recordSubsetProjectorCommutator_le_max_cross_mul_norm
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    ‖recordSubsetProjectorCommutator D U S x‖ ≤
      max ‖recordSubsetIncomingCLM D U S‖
          ‖recordSubsetOutgoingCLM D U S‖ * ‖x‖ := by
  let M : ℝ := max ‖recordSubsetIncomingCLM D U S‖
    ‖recordSubsetOutgoingCLM D U S‖
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact max_nonneg (norm_nonneg _) (norm_nonneg _)
  have hin :
      ‖recordSubsetIncoming D U S x‖ ≤
        M * ‖Gleason.projL (recordSubsetSubspace D Sᶜ) x‖ := by
    calc
      ‖recordSubsetIncoming D U S x‖ =
          ‖recordSubsetIncomingCLM D U S
            (Gleason.projL (recordSubsetSubspace D Sᶜ) x)‖ := by
        rw [recordSubsetIncomingCLM_apply,
          recordSubsetIncoming_project_compl D U S x]
      _ ≤ ‖recordSubsetIncomingCLM D U S‖ *
          ‖Gleason.projL (recordSubsetSubspace D Sᶜ) x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * ‖Gleason.projL (recordSubsetSubspace D Sᶜ) x‖ := by
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hout :
      ‖recordSubsetOutgoing D U S x‖ ≤
        M * ‖Gleason.projL (recordSubsetSubspace D S) x‖ := by
    calc
      ‖recordSubsetOutgoing D U S x‖ =
          ‖recordSubsetOutgoingCLM D U S
            (Gleason.projL (recordSubsetSubspace D S) x)‖ := by
        rw [recordSubsetOutgoingCLM_apply,
          recordSubsetOutgoing_project D U S x]
      _ ≤ ‖recordSubsetOutgoingCLM D U S‖ *
          ‖Gleason.projL (recordSubsetSubspace D S) x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * ‖Gleason.projL (recordSubsetSubspace D S) x‖ := by
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  have hin_sq :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hM0 (norm_nonneg _))).2 hin
  have hout_sq :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hM0 (norm_nonneg _))).2 hout
  have hsq :
      ‖recordSubsetProjectorCommutator D U S x‖ ^ 2 ≤
        (M * ‖x‖) ^ 2 := by
    rw [norm_sq_recordSubsetProjectorCommutator_eq_cross_sum D U S x]
    calc
      ‖recordSubsetIncoming D U S x‖ ^ 2 +
          ‖recordSubsetOutgoing D U S x‖ ^ 2 ≤
        (M * ‖Gleason.projL (recordSubsetSubspace D Sᶜ) x‖) ^ 2 +
          (M * ‖Gleason.projL (recordSubsetSubspace D S) x‖) ^ 2 :=
        add_le_add hin_sq hout_sq
      _ = M ^ 2 *
          (‖Gleason.projL (recordSubsetSubspace D S) x‖ ^ 2 +
            ‖Gleason.projL (recordSubsetSubspace D Sᶜ) x‖ ^ 2) := by
        ring
      _ = (M * ‖x‖) ^ 2 := by
        rw [recordSubset_projection_norm_sq_add_compl D S x]
        ring
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hM0 (norm_nonneg _))).1 hsq

/-- Exact block formula: the operator norm of the aggregate commutator is the
maximum of the incoming and outgoing cross-block operator norms. -/
theorem recordSubsetProjectorCommutatorCLM_opNorm_eq_max_cross
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    ‖recordSubsetProjectorCommutatorCLM D U S‖ =
      max ‖recordSubsetIncomingCLM D U S‖
          ‖recordSubsetOutgoingCLM D U S‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _
      (max_nonneg (norm_nonneg _) (norm_nonneg _))
    intro x
    exact norm_recordSubsetProjectorCommutator_le_max_cross_mul_norm
      D U S x
  · exact max_le
      (recordSubsetIncomingCLM_opNorm_le_commutator D U S)
      (recordSubsetOutgoingCLM_opNorm_le_commutator D U S)

end
end EverettianDecoherence.Approximation

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


private theorem norm_recordSubsetOutgoing_cell_le
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : (Projective.interface n).Cell D) (hc : c ∈ S) (x : H n) :
    ‖Gleason.projL (recordSubsetSubspace D Sᶜ)
        (U (Gleason.projL c.val x))‖ ≤
      perspectiveProjectorCommutatorOpNormProfile D U c *
        ‖Gleason.projL c.val x‖ := by
  have hzero :
      Gleason.projL (recordSubsetSubspace D Sᶜ)
        (Gleason.projL c.val
          (U (Gleason.projL c.val x))) = 0 :=
    recordSubsetComplementProjector_cell_apply_eq_zero_of_mem
      D S c hc (U (Gleason.projL c.val x))
  have hidem :
      Gleason.projL c.val (Gleason.projL c.val x) =
        Gleason.projL c.val x := by
    unfold Gleason.projL
    change c.val.starProjection (c.val.starProjection x) =
      c.val.starProjection x
    exact Submodule.starProjection_eq_self_iff.mpr
      (Submodule.starProjection_apply_mem c.val x)
  have hcomm :
      Gleason.projL (recordSubsetSubspace D Sᶜ)
          (perspectiveProjectorCommutator D U c
            (Gleason.projL c.val x)) =
        - Gleason.projL (recordSubsetSubspace D Sᶜ)
            (U (Gleason.projL c.val x)) := by
    rw [perspectiveProjectorCommutator_apply, map_sub, hzero, hidem,
      zero_sub]
  calc
    ‖Gleason.projL (recordSubsetSubspace D Sᶜ)
        (U (Gleason.projL c.val x))‖ =
      ‖Gleason.projL (recordSubsetSubspace D Sᶜ)
        (perspectiveProjectorCommutator D U c
          (Gleason.projL c.val x))‖ := by
        rw [hcomm, norm_neg]
    _ ≤ ‖perspectiveProjectorCommutator D U c
          (Gleason.projL c.val x)‖ := by
        change ‖(recordSubsetSubspace D Sᶜ).starProjection
          (perspectiveProjectorCommutator D U c
            (Gleason.projL c.val x))‖ ≤
          ‖perspectiveProjectorCommutator D U c
            (Gleason.projL c.val x)‖
        exact Submodule.norm_starProjection_apply_le _
    _ ≤ perspectiveProjectorCommutatorOpNormProfile D U c *
        ‖Gleason.projL c.val x‖ := by
      simpa [perspectiveProjectorCommutatorNormProfile] using
        (perspectiveProjectorCommutatorNormProfile_le_opNorm_mul_norm
          D U (Gleason.projL c.val x) c)

/-- Input-side estimate for the block leaving `S`, obtained by finite
Cauchy--Schwarz over the cell decomposition of the input. -/
theorem norm_recordSubsetOutgoing_le_sqrt_subsetSq_mul_subset_norm
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    ‖recordSubsetOutgoing D U S x‖ ≤
      Real.sqrt (subsetProjectorCommutatorOpNormSq D U S) *
        ‖Gleason.projL (recordSubsetSubspace D S) x‖ := by
  have hout :
      recordSubsetOutgoing D U S x =
        ∑ c ∈ S,
          Gleason.projL (recordSubsetSubspace D Sᶜ)
            (U (Gleason.projL c.val x)) := by
    unfold recordSubsetOutgoing
    rw [recordSubsetProjector_eq_sum D S]
    simp only [LinearMap.sum_apply, map_sum]
  rw [hout]
  calc
    ‖∑ c ∈ S,
        Gleason.projL (recordSubsetSubspace D Sᶜ)
          (U (Gleason.projL c.val x))‖ ≤
      ∑ c ∈ S,
        ‖Gleason.projL (recordSubsetSubspace D Sᶜ)
          (U (Gleason.projL c.val x))‖ := norm_sum_le _ _
    _ ≤ ∑ c ∈ S,
        perspectiveProjectorCommutatorOpNormProfile D U c *
          ‖Gleason.projL c.val x‖ := by
      exact Finset.sum_le_sum fun c hc =>
        norm_recordSubsetOutgoing_cell_le D U S c hc x
    _ ≤ Real.sqrt
          (∑ c ∈ S,
            (perspectiveProjectorCommutatorOpNormProfile D U c) ^ 2) *
        Real.sqrt (∑ c ∈ S, ‖Gleason.projL c.val x‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt S
        (perspectiveProjectorCommutatorOpNormProfile D U)
        (fun c => ‖Gleason.projL c.val x‖)
    _ = Real.sqrt (subsetProjectorCommutatorOpNormSq D U S) *
        ‖Gleason.projL (recordSubsetSubspace D S) x‖ := by
      rw [← norm_sq_recordSubsetProjector_eq_sum D S x,
        Real.sqrt_sq (norm_nonneg _)]
      rfl

/-- Squared input-side estimate for the block leaving `S`. -/
theorem norm_sq_recordSubsetOutgoing_le_subsetSq_mul_subset_norm_sq
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    ‖recordSubsetOutgoing D U S x‖ ^ 2 ≤
      subsetProjectorCommutatorOpNormSq D U S *
        ‖Gleason.projL (recordSubsetSubspace D S) x‖ ^ 2 := by
  have h := norm_recordSubsetOutgoing_le_sqrt_subsetSq_mul_subset_norm
    D U S x
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).2 h
  rw [mul_pow,
    Real.sq_sqrt (subsetProjectorCommutatorOpNormSq_nonneg D U S)] at hs
  exact hs

/-- The full aggregate commutator is controlled by the squared defect budget
on `S` alone. -/
theorem norm_sq_recordSubsetProjectorCommutator_le_subsetSq_mul_norm_sq
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    ‖recordSubsetProjectorCommutator D U S x‖ ^ 2 ≤
      subsetProjectorCommutatorOpNormSq D U S * ‖x‖ ^ 2 := by
  rw [norm_sq_recordSubsetProjectorCommutator_eq_cross_sum D U S x]
  calc
    ‖recordSubsetIncoming D U S x‖ ^ 2 +
        ‖recordSubsetOutgoing D U S x‖ ^ 2 ≤
      subsetProjectorCommutatorOpNormSq D U S *
          ‖Gleason.projL (recordSubsetSubspace D Sᶜ) x‖ ^ 2 +
        subsetProjectorCommutatorOpNormSq D U S *
          ‖Gleason.projL (recordSubsetSubspace D S) x‖ ^ 2 :=
      add_le_add
        (norm_sq_recordSubsetIncoming_le_subsetSq_mul_compl_norm_sq D U S x)
        (norm_sq_recordSubsetOutgoing_le_subsetSq_mul_subset_norm_sq D U S x)
    _ = subsetProjectorCommutatorOpNormSq D U S *
        (‖Gleason.projL (recordSubsetSubspace D S) x‖ ^ 2 +
          ‖Gleason.projL (recordSubsetSubspace D Sᶜ) x‖ ^ 2) := by ring
    _ = subsetProjectorCommutatorOpNormSq D U S * ‖x‖ ^ 2 := by
      have hsum :=
        sum_sq_recordCellNormProfile_eq_norm_sq D x
      have hpartition :
          ‖Gleason.projL (recordSubsetSubspace D S) x‖ ^ 2 +
              ‖Gleason.projL (recordSubsetSubspace D Sᶜ) x‖ ^ 2 =
            ‖x‖ ^ 2 := by
        rw [norm_sq_recordSubsetProjector_eq_sum D S x,
          norm_sq_recordSubsetProjector_eq_sum D Sᶜ x]
        have hsplit :
            (∑ c ∈ S, ‖Gleason.projL c.val x‖ ^ 2) +
                ∑ c ∈ Sᶜ, ‖Gleason.projL c.val x‖ ^ 2 =
              ∑ c : (Projective.interface n).Cell D,
                ‖Gleason.projL c.val x‖ ^ 2 := by
          exact S.sum_add_sum_compl (fun c => ‖Gleason.projL c.val x‖ ^ 2)
        change
          (∑ c : (Projective.interface n).Cell D,
              ‖Gleason.projL c.val x‖ ^ 2) = ‖x‖ ^ 2 at hsum
        exact hsplit.trans hsum
      rw [hpartition]



/-- The commutator of the finite complement aggregate projector is the
negative of the subset commutator. -/
theorem recordSubsetProjectorCommutator_compl_apply
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    recordSubsetProjectorCommutator D U Sᶜ x =
      - recordSubsetProjectorCommutator D U S x := by
  rw [recordSubsetProjectorCommutator_apply,
    recordSubsetProjectorCommutator_apply,
    recordSubsetProjector_compl_apply_eq_sub D S (U x),
    recordSubsetProjector_compl_apply_eq_sub D S x,
    map_sub]
  module

/-- The same aggregate commutator is also controlled by the squared defect
budget carried by the finite complement. -/
theorem norm_sq_recordSubsetProjectorCommutator_le_complSq_mul_norm_sq
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    ‖recordSubsetProjectorCommutator D U S x‖ ^ 2 ≤
      subsetProjectorCommutatorOpNormSq D U Sᶜ * ‖x‖ ^ 2 := by
  have h :=
    norm_sq_recordSubsetProjectorCommutator_le_subsetSq_mul_norm_sq
      D U Sᶜ x
  rw [recordSubsetProjectorCommutator_compl_apply D U S x,
    norm_neg] at h
  exact h

/-- The aggregate commutator is controlled by the smaller of the subset and
complement squared defect budgets. -/
theorem norm_sq_recordSubsetProjectorCommutator_le_minSq_mul_norm_sq
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    ‖recordSubsetProjectorCommutator D U S x‖ ^ 2 ≤
      min (subsetProjectorCommutatorOpNormSq D U S)
          (subsetProjectorCommutatorOpNormSq D U Sᶜ) * ‖x‖ ^ 2 := by
  rcases le_total
      (subsetProjectorCommutatorOpNormSq D U S)
      (subsetProjectorCommutatorOpNormSq D U Sᶜ) with hle | hle
  · rw [min_eq_left hle]
    exact norm_sq_recordSubsetProjectorCommutator_le_subsetSq_mul_norm_sq
      D U S x
  · rw [min_eq_right hle]
    exact norm_sq_recordSubsetProjectorCommutator_le_complSq_mul_norm_sq
      D U S x

/-- Universal half-square estimate for every aggregated subset commutator. -/
theorem norm_sq_recordSubsetProjectorCommutator_le_half_globalSq_mul_norm_sq
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    ‖recordSubsetProjectorCommutator D U S x‖ ^ 2 ≤
      (operatorNormProjectorCommutatorL2 D U ^ 2 / 2) * ‖x‖ ^ 2 := by
  exact
    (norm_sq_recordSubsetProjectorCommutator_le_minSq_mul_norm_sq D U S x).trans
      (mul_le_mul_of_nonneg_right
        (min_subset_compl_commutatorSq_le_half D U S)
        (sq_nonneg ‖x‖))


end
end EverettianDecoherence.Approximation

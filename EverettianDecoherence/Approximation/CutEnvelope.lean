import EverettianDecoherence.Approximation.NearSaturationTwoCell
import EverettianDecoherence.Approximation.SubsetCommutatorOpNormBounds

/-!
**FR.** Enveloppe finie des normes de commutateurs agrégés sur tous les cuts de
la perspective. Le maximum est réellement atteint, puisque l'ensemble des
sous-ensembles de cellules est fini. Cette couche évite tout supremum sur la
sphère des états.

**EN.** Finite envelope of aggregate commutator norms over all cuts of the
perspective. The maximum is genuinely attained because the family of subsets
of cells is finite. This layer avoids any supremum over the state sphere.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

private noncomputable def subsetCommutatorNormValues
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) : Finset ℝ :=
  (Finset.univ.powerset).image fun S =>
    ‖recordSubsetProjectorCommutatorCLM D U S‖

private theorem subsetCommutatorNormValues_nonempty
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) :
    (subsetCommutatorNormValues D U).Nonempty := by
  unfold subsetCommutatorNormValues
  refine ⟨‖recordSubsetProjectorCommutatorCLM D U ∅‖, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨∅, by simp, rfl⟩

/-- Maximum aggregate commutator norm over all subset cuts. -/
noncomputable def maxSubsetCommutatorOpNorm
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) : ℝ :=
  (subsetCommutatorNormValues D U).max'
    (subsetCommutatorNormValues_nonempty D U)

theorem subsetCommutatorOpNorm_le_max
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    ‖recordSubsetProjectorCommutatorCLM D U S‖ ≤
      maxSubsetCommutatorOpNorm D U := by
  unfold maxSubsetCommutatorOpNorm
  apply Finset.le_max'
  unfold subsetCommutatorNormValues
  apply Finset.mem_image.mpr
  exact ⟨S, by simp, rfl⟩

theorem maxSubsetCommutatorOpNorm_nonneg
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) :
    0 ≤ maxSubsetCommutatorOpNorm D U := by
  exact (norm_nonneg
    (recordSubsetProjectorCommutatorCLM D U ∅)).trans
      (subsetCommutatorOpNorm_le_max D U ∅)

/-- Some subset cut realizes the finite maximum exactly. -/
theorem exists_subsetCommutatorOpNorm_eq_max
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) :
    ∃ S : Finset ((Projective.interface n).Cell D),
      ‖recordSubsetProjectorCommutatorCLM D U S‖ =
        maxSubsetCommutatorOpNorm D U := by
  have hmem :=
    Finset.max'_mem
      (subsetCommutatorNormValues D U)
      (subsetCommutatorNormValues_nonempty D U)
  unfold subsetCommutatorNormValues at hmem
  obtain ⟨S, hS, hEq⟩ := Finset.mem_image.mp hmem
  exact ⟨S, hEq⟩

/-- Every normalized-state record-profile variation is bounded by twice the
finite cut envelope. -/
theorem recordProfileL1_unitary_le_two_mul_maxSubsetCommutatorOpNorm
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (x : H n) (hx : ‖x‖ = 1) :
    recordProfileL1 D (U x) x ≤
      2 * maxSubsetCommutatorOpNorm D U := by
  let S := positiveRecordSubset D (U x) x
  calc
    recordProfileL1 D (U x) x ≤
        2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ := by
      simpa [S] using
        recordProfileL1_unitary_le_two_mul_positiveSubsetCommutatorOpNorm
          D U x hx
    _ ≤ 2 * maxSubsetCommutatorOpNorm D U := by
      gcongr
      exact subsetCommutatorOpNorm_le_max D U S

/-- The squared finite cut envelope is at most half of the full squared L2
commutator budget. -/
theorem maxSubsetCommutatorOpNorm_sq_le_half_globalSq
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) :
    maxSubsetCommutatorOpNorm D U ^ 2 ≤
      operatorNormProjectorCommutatorL2 D U ^ 2 / 2 := by
  obtain ⟨S, hS⟩ := exists_subsetCommutatorOpNorm_eq_max D U
  rw [← hS]
  have hsub :=
    recordSubsetProjectorCommutatorCLM_opNorm_sq_le_subsetSq D U S
  have hcompl :=
    recordSubsetProjectorCommutatorCLM_opNorm_sq_le_complSq D U S
  have hmin :
      ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2 ≤
        min (subsetProjectorCommutatorOpNormSq D U S)
          (subsetProjectorCommutatorOpNormSq D U Sᶜ) :=
    le_min hsub hcompl
  exact hmin.trans (min_subset_compl_commutatorSq_le_half D U S)

end
end EverettianDecoherence.Approximation

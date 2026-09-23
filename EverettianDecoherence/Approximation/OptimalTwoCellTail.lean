import EverettianDecoherence.Approximation.TwoCellCommutatorConcentration
import EverettianDecoherence.Approximation.SubsetCommutatorBudget

/-!
Exact finite top-two tail used by the publication-facing formulation.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

private noncomputable def distinctCellPairs
    {n : ℕ} (D : Perspective n) :
    Finset ((Projective.interface n).Cell D ×
      (Projective.interface n).Cell D) :=
  ((Finset.univ : Finset ((Projective.interface n).Cell D)).product
      (Finset.univ : Finset ((Projective.interface n).Cell D))).filter
    (fun p => p.1 ≠ p.2)

private noncomputable def twoCellCapturedValues
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) : Finset ℝ :=
  insert 0 <|
    (distinctCellPairs D).image fun p =>
      cellCommutatorOpNormSq D U p.1 +
        cellCommutatorOpNormSq D U p.2

private theorem twoCellCapturedValues_nonempty
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) :
    (twoCellCapturedValues D U).Nonempty := by
  exact ⟨0, by simp [twoCellCapturedValues]⟩

/-- Largest quadratic budget captured by two distinct cells.  The inserted
zero makes the definition total even for perspectives with fewer than two
cells. -/
noncomputable def maxTwoCellCapturedBudget
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) : ℝ :=
  (twoCellCapturedValues D U).max'
    (twoCellCapturedValues_nonempty D U)

/-- Absolute budget left after retaining an optimal pair of distinct cells. -/
noncomputable def optimalTwoCellTail
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) : ℝ :=
  operatorNormProjectorCommutatorL2 D U ^ 2 -
    maxTwoCellCapturedBudget D U

/-- Relative optimal two-cell tail.  This is the manuscript's tau whenever
the global squared budget is positive. -/
noncomputable def optimalTwoCellTailFraction
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) : ℝ :=
  optimalTwoCellTail D U /
    operatorNormProjectorCommutatorL2 D U ^ 2

theorem maxTwoCellCapturedBudget_nonneg
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) :
    0 ≤ maxTwoCellCapturedBudget D U := by
  unfold maxTwoCellCapturedBudget
  apply Finset.le_max'
  simp [twoCellCapturedValues]

theorem pair_budget_le_maxTwoCellCapturedBudget
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (i j : (Projective.interface n).Cell D)
    (hij : i ≠ j) :
    cellCommutatorOpNormSq D U i +
        cellCommutatorOpNormSq D U j ≤
      maxTwoCellCapturedBudget D U := by
  unfold maxTwoCellCapturedBudget
  apply Finset.le_max'
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image.mpr
  refine ⟨(i, j), ?_, rfl⟩
  simp [distinctCellPairs, hij]

theorem pair_budget_le_globalSq
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (i j : (Projective.interface n).Cell D)
    (hij : i ≠ j) :
    cellCommutatorOpNormSq D U i +
        cellCommutatorOpNormSq D U j ≤
      operatorNormProjectorCommutatorL2 D U ^ 2 := by
  let S : Finset ((Projective.interface n).Cell D) := {i, j}
  have hS :
      subsetProjectorCommutatorOpNormSq D U S =
        cellCommutatorOpNormSq D U i +
          cellCommutatorOpNormSq D U j := by
    unfold S subsetProjectorCommutatorOpNormSq cellCommutatorOpNormSq
    simp [hij]
  have hpart := subsetProjectorCommutatorOpNormSq_add_compl D U S
  have hcomp0 := subsetProjectorCommutatorOpNormSq_nonneg D U Sᶜ
  rw [hS] at hpart
  linarith

theorem maxTwoCellCapturedBudget_le_globalSq
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) :
    maxTwoCellCapturedBudget D U ≤
      operatorNormProjectorCommutatorL2 D U ^ 2 := by
  unfold maxTwoCellCapturedBudget
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · positivity
  · rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    have hp' := (Finset.mem_filter.mp hp).2
    exact pair_budget_le_globalSq D U p.1 p.2 hp'

theorem optimalTwoCellTail_nonneg
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) :
    0 ≤ optimalTwoCellTail D U := by
  unfold optimalTwoCellTail
  exact sub_nonneg.mpr (maxTwoCellCapturedBudget_le_globalSq D U)

/-- Any concrete two-cell concentration estimate bounds the exact optimal
absolute tail. -/
theorem optimalTwoCellTail_le_of_pair
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (i j : (Projective.interface n).Cell D)
    (hij : i ≠ j) (B : ℝ)
    (hpair :
      operatorNormProjectorCommutatorL2 D U ^ 2 -
          cellCommutatorOpNormSq D U i -
          cellCommutatorOpNormSq D U j ≤ B) :
    optimalTwoCellTail D U ≤ B := by
  have hcap := pair_budget_le_maxTwoCellCapturedBudget D U i j hij
  unfold optimalTwoCellTail
  linarith

/-- Bridge from the existing robust existential predicate to the exact
publication-facing top-two tail. -/
theorem optimalTwoCellTail_le_of_concentratedWithin
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) (eps : ℝ)
    (h : TwoCellCommutatorConcentratedWithin D U eps) :
    optimalTwoCellTail D U ≤
      eps * operatorNormProjectorCommutatorL2 D U ^ 2 := by
  obtain ⟨i, j, hij, hpair⟩ := h
  exact optimalTwoCellTail_le_of_pair D U i j hij _ hpair

/-- Relative version of the preceding bridge at positive global budget. -/
theorem optimalTwoCellTailFraction_le_of_concentratedWithin
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) (eps : ℝ)
    (hdelta : 0 < operatorNormProjectorCommutatorL2 D U)
    (h : TwoCellCommutatorConcentratedWithin D U eps) :
    optimalTwoCellTailFraction D U ≤ eps := by
  have htail := optimalTwoCellTail_le_of_concentratedWithin D U eps h
  unfold optimalTwoCellTailFraction
  exact (div_le_iff₀ (sq_pos_of_pos hdelta)).2 (by
    simpa [mul_comm] using htail)

/-- If the perspective contains a distinct pair, the inserted zero does not
create a spurious optimum: the maximal captured budget is attained by a
pair of distinct cells. -/
theorem exists_pair_eq_maxTwoCellCapturedBudget
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (hpairs : ∃ i j : (Projective.interface n).Cell D, i ≠ j) :
    ∃ i j : (Projective.interface n).Cell D,
      i ≠ j ∧
      maxTwoCellCapturedBudget D U =
        cellCommutatorOpNormSq D U i +
          cellCommutatorOpNormSq D U j := by
  obtain ⟨i0, j0, hij0⟩ := hpairs
  let p0 := cellCommutatorOpNormSq D U i0 +
    cellCommutatorOpNormSq D U j0
  have hp0 : 0 ≤ p0 := by
    dsimp [p0]
    exact add_nonneg (cellCommutatorOpNormSq_nonneg D U i0)
      (cellCommutatorOpNormSq_nonneg D U j0)
  let M := maxTwoCellCapturedBudget D U
  have hmem : M ∈ twoCellCapturedValues D U := by
    dsimp [M, maxTwoCellCapturedBudget]
    exact Finset.max'_mem (twoCellCapturedValues D U)
      (twoCellCapturedValues_nonempty D U)
  rcases Finset.mem_insert.mp hmem with hM0 | himage
  · have hle := pair_budget_le_maxTwoCellCapturedBudget D U i0 j0 hij0
    have hp0zero : p0 = 0 := by
      dsimp [p0, M] at hp0 hle hM0 ⊢
      rw [hM0] at hle
      linarith
    refine ⟨i0, j0, hij0, ?_⟩
    change M =
      cellCommutatorOpNormSq D U i0 +
        cellCommutatorOpNormSq D U j0
    rw [hM0]
    exact hp0zero.symm
  · rcases Finset.mem_image.mp himage with ⟨p, hp, hpval⟩
    have hdistinct : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    refine ⟨p.1, p.2, hdistinct, ?_⟩
    change M =
      cellCommutatorOpNormSq D U p.1 +
        cellCommutatorOpNormSq D U p.2
    exact hpval.symm

end
end EverettianDecoherence.Approximation

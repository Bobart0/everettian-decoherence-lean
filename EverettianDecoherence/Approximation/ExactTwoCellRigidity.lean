import EverettianDecoherence.Approximation.CutEnvelopeStability

/-!
**FR.** Rigidité exacte des cas d'égalité du mécanisme T5 au niveau de
l'enveloppe finie des cuts. Une concentration relative avec erreur nulle
signifie que tout le budget quadratique des commutateurs cellulaires est porté
par deux cellules distinctes. En particulier, une saturation exacte de la
borne universelle de l'enveloppe des cuts force ce support à deux cellules.

**EN.** Exact rigidity of equality cases for the T5 mechanism at the level of
the finite cut envelope. Relative concentration with zero error means that the
full quadratic cellwise commutator budget is supported on two distinct cells.
In particular, exact saturation of the universal cut-envelope bound forces
such two-cell support.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

/-- Exact support of the cellwise squared commutator profile on two distinct
cells. The two selected cells themselves are allowed to carry zero mass; under
positive global defect and exact saturation they will in fact be active. -/
def CellCommutatorSupportedOnTwo
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) : Prop :=
  ∃ i j : (Projective.interface n).Cell D,
    i ≠ j ∧
      ∀ k, k ≠ i → k ≠ j →
        cellCommutatorOpNormSq D U k = 0

/-- The global squared L2 commutator budget is exactly the sum of the squared
cellwise operator-norm commutators. -/
theorem sum_cellCommutatorOpNormSq_eq_globalSq
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) :
    (∑ c, cellCommutatorOpNormSq D U c) =
      operatorNormProjectorCommutatorL2 D U ^ 2 := by
  unfold cellCommutatorOpNormSq
  unfold operatorNormProjectorCommutatorL2
  rw [EverettianDecoherence.Metrics.finiteL2_sq]
  rfl

private theorem sum_except_two_eq_tail
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) {i j : α} (hij : i ≠ j) :
    (∑ k ∈ ((Finset.univ.erase i).erase j), p k) =
      (∑ k, p k) - p i - p j := by
  have hi : i ∈ (Finset.univ : Finset α) := Finset.mem_univ i
  have hj : j ∈ (Finset.univ.erase i : Finset α) := by
    exact Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have h1 :=
    Finset.sum_erase_add (Finset.univ : Finset α) p hi
  have h2 :=
    Finset.sum_erase_add (Finset.univ.erase i) p hj
  nlinarith

/-- Zero relative two-cell tail is literal support on those two cells. -/
theorem cellCommutatorSupportedOnTwo_of_concentrated_zero
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (h : TwoCellCommutatorConcentratedWithin D U 0) :
    CellCommutatorSupportedOnTwo D U := by
  obtain ⟨i, j, hij, htail⟩ := h
  refine ⟨i, j, hij, ?_⟩
  let p : (Projective.interface n).Cell D → ℝ :=
    fun c => cellCommutatorOpNormSq D U c
  have htotal :
      (∑ c, p c) = operatorNormProjectorCommutatorL2 D U ^ 2 := by
    simpa [p] using sum_cellCommutatorOpNormSq_eq_globalSq D U
  have hrest :
      (∑ k ∈ ((Finset.univ.erase i).erase j), p k) =
        operatorNormProjectorCommutatorL2 D U ^ 2 - p i - p j := by
    rw [sum_except_two_eq_tail p hij, htotal]
  have hrest_nonneg :
      0 ≤ ∑ k ∈ ((Finset.univ.erase i).erase j), p k := by
    apply Finset.sum_nonneg
    intro k hk
    exact cellCommutatorOpNormSq_nonneg D U k
  have hrest_le :
      (∑ k ∈ ((Finset.univ.erase i).erase j), p k) ≤ 0 := by
    rw [hrest]
    simpa [TwoCellCommutatorConcentratedWithin, p] using htail
  have hrest_zero :
      (∑ k ∈ ((Finset.univ.erase i).erase j), p k) = 0 :=
    le_antisymm hrest_le hrest_nonneg
  have hpoint :
      ∀ k ∈ ((Finset.univ.erase i).erase j), p k = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun k hk => cellCommutatorOpNormSq_nonneg D U k)).mp hrest_zero
  intro k hki hkj
  have hkrest :
      k ∈ ((Finset.univ.erase i).erase j) := by
    apply Finset.mem_erase.mpr
    refine ⟨hkj, ?_⟩
    exact Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩
  simpa [p] using hpoint k hkrest

/-- Exact saturation of the finite cut-envelope inequality forces exact
two-cell support of the cellwise commutator budget. -/
theorem cellCommutatorSupportedOnTwo_of_maxCut_saturation
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (hdelta : 0 < operatorNormProjectorCommutatorL2 D U)
    (hsat :
      maxSubsetCommutatorOpNorm D U ^ 2 =
        operatorNormProjectorCommutatorL2 D U ^ 2 / 2) :
    CellCommutatorSupportedOnTwo D U := by
  let δ : ℝ := operatorNormProjectorCommutatorL2 D U
  let C : ℝ := maxSubsetCommutatorOpNorm D U
  have hnear :
      2 * (1 - (0 : ℝ)) * δ ^ 2 ≤ (2 * C) ^ 2 := by
    dsimp [δ, C]
    nlinarith [hsat]
  have hconc :
      TwoCellCommutatorConcentratedWithin D U
        (twoCellStabilityModulus
          (operatorNormProjectorCommutatorL2 D U) 0) :=
    twoCellCommutatorConcentratedWithin_of_maxCut_near_saturated
      D U 0 (operatorNormProjectorCommutatorL2 D U)
      (by norm_num)
      (by norm_num)
      hdelta
      le_rfl
      (by simpa [δ, C] using hnear)
  have hzero :
      twoCellStabilityModulus
        (operatorNormProjectorCommutatorL2 D U) 0 = 0 := by
    simp [twoCellStabilityModulus]
  rw [hzero] at hconc
  exact cellCommutatorSupportedOnTwo_of_concentrated_zero D U hconc

end
end EverettianDecoherence.Approximation

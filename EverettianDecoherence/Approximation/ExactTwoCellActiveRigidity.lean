import EverettianDecoherence.Approximation.ExactTwoCellRigidityConverse

/-!
**FR.** Version non triviale de la rigidité exacte. Lorsque le défaut global
est strictement positif, la saturation de l'enveloppe des cuts n'implique pas
seulement un support contenu dans deux cellules : les deux cellules sont
nécessairement actives.

**EN.** Nontrivial exact rigidity. When the global defect is strictly positive,
saturation of the finite cut envelope does not merely imply support contained
in two cells: both cells must be active.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

def ExactlyTwoActiveCellCommutators
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) : Prop :=
  ∃ i j : (Projective.interface n).Cell D,
    i ≠ j ∧
      0 < cellCommutatorOpNormSq D U i ∧
      0 < cellCommutatorOpNormSq D U j ∧
      ∀ k, k ≠ i → k ≠ j →
        cellCommutatorOpNormSq D U k = 0

private theorem sum_except_two_eq_tail_active
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

theorem exactlyTwoActiveCellCommutators_of_maxCut_saturation
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (hdelta : 0 < operatorNormProjectorCommutatorL2 D U)
    (hsat :
      maxSubsetCommutatorOpNorm D U ^ 2 =
        operatorNormProjectorCommutatorL2 D U ^ 2 / 2) :
    ExactlyTwoActiveCellCommutators D U := by
  have hsupp :=
    cellCommutatorSupportedOnTwo_of_maxCut_saturation D U hdelta hsat
  obtain ⟨i, j, hij, hsupport⟩ := hsupp
  let p : (Projective.interface n).Cell D → ℝ :=
    fun c => cellCommutatorOpNormSq D U c
  let A : ℝ := operatorNormProjectorCommutatorL2 D U ^ 2
  let C : ℝ := maxSubsetCommutatorOpNorm D U
  have hApos : 0 < A := by
    dsimp [A]
    exact sq_pos_of_pos hdelta
  have htotal :
      (∑ c, p c) = A := by
    simpa [p, A] using sum_cellCommutatorOpNormSq_eq_globalSq D U
  have hrestzero :
      (∑ k ∈ ((Finset.univ.erase i).erase j), p k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_erase.mp hk
    have hkj : k ≠ j := hk'.1
    have hki : k ≠ i := (Finset.mem_erase.mp hk'.2).1
    exact hsupport k hki hkj
  have hsumtwo : A = p i + p j := by
    have htail :=
      sum_except_two_eq_tail_active p hij
    rw [hrestzero, htotal] at htail
    nlinarith
  have hCi :
      ‖recordSubsetProjectorCommutatorCLM D U {i}‖ ≤ C := by
    simpa [C] using subsetCommutatorOpNorm_le_max D U {i}
  have hCj :
      ‖recordSubsetProjectorCommutatorCLM D U {j}‖ ≤ C := by
    simpa [C] using subsetCommutatorOpNorm_le_max D U {j}
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact maxSubsetCommutatorOpNorm_nonneg D U
  have hiC : p i ≤ C ^ 2 := by
    rw [← singletonSubsetCommutatorOpNormSq_eq_cell D U i]
    exact (sq_le_sq₀ (norm_nonneg _) hC0).2 hCi
  have hjC : p j ≤ C ^ 2 := by
    rw [← singletonSubsetCommutatorOpNormSq_eq_cell D U j]
    exact (sq_le_sq₀ (norm_nonneg _) hC0).2 hCj
  have hCeq : C ^ 2 = A / 2 := by
    simpa [C, A] using hsat
  have hiHalf : p i ≤ A / 2 := by simpa [hCeq] using hiC
  have hjHalf : p j ≤ A / 2 := by simpa [hCeq] using hjC
  have hipos : 0 < p i := by
    nlinarith
  have hjpos : 0 < p j := by
    nlinarith
  refine ⟨i, j, hij, hipos, hjpos, ?_⟩
  intro k hki hkj
  exact hsupport k hki hkj

theorem cellCommutatorSupportedOnTwo_of_exactlyTwoActive
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (h : ExactlyTwoActiveCellCommutators D U) :
    CellCommutatorSupportedOnTwo D U := by
  obtain ⟨i, j, hij, _hi, _hj, hsupport⟩ := h
  exact ⟨i, j, hij, hsupport⟩

/-- For positive global defect, exact cut-envelope saturation is equivalent to
having exactly two active cellwise commutators. -/
theorem maxCut_saturation_iff_exactlyTwoActiveCellCommutators
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (hdelta : 0 < operatorNormProjectorCommutatorL2 D U) :
    maxSubsetCommutatorOpNorm D U ^ 2 =
        operatorNormProjectorCommutatorL2 D U ^ 2 / 2 ↔
      ExactlyTwoActiveCellCommutators D U := by
  constructor
  · exact exactlyTwoActiveCellCommutators_of_maxCut_saturation D U hdelta
  · intro h
    exact maxCut_saturation_of_cellCommutatorSupportedOnTwo D U
      (cellCommutatorSupportedOnTwo_of_exactlyTwoActive D U h)

end
end EverettianDecoherence.Approximation

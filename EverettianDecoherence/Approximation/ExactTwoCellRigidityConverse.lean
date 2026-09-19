import EverettianDecoherence.Approximation.ExactTwoCellRigidity

/-!
**FR.** Réciproque de la rigidité exacte : si le profil quadratique des normes
de commutateurs cellulaires est supporté sur deux cellules distinctes, alors
l'enveloppe des cuts sature exactement sa borne universelle.

**EN.** Converse exact rigidity: if the squared cellwise commutator-norm
profile is supported on two distinct cells, then the finite cut envelope
exactly saturates its universal bound.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

/-- On a singleton cut, the aggregate commutator is exactly the corresponding
cell commutator. -/
theorem recordSubsetProjectorCommutatorCLM_singleton
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (c : (Projective.interface n).Cell D) :
    recordSubsetProjectorCommutatorCLM D U {c} =
      perspectiveProjectorCommutatorCLM D U c := by
  apply ContinuousLinearMap.ext
  intro x
  change recordSubsetProjectorCommutator D U {c} x =
    perspectiveProjectorCommutator D U c x
  rw [recordSubsetProjectorCommutator_apply,
    perspectiveProjectorCommutator_apply]
  have hproj :
      Gleason.projL (recordSubsetSubspace D {c}) =
        Gleason.projL c.val := by
    rw [recordSubsetProjector_eq_sum]
    simp
  rw [hproj]

theorem singletonSubsetCommutatorOpNormSq_eq_cell
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (c : (Projective.interface n).Cell D) :
    ‖recordSubsetProjectorCommutatorCLM D U {c}‖ ^ 2 =
      cellCommutatorOpNormSq D U c := by
  rw [recordSubsetProjectorCommutatorCLM_singleton]
  rfl

private theorem sum_except_two_eq_tail'
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

/-- Exact two-cell support implies exact saturation of the finite cut
envelope. -/
theorem maxCut_saturation_of_cellCommutatorSupportedOnTwo
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (h : CellCommutatorSupportedOnTwo D U) :
    maxSubsetCommutatorOpNorm D U ^ 2 =
      operatorNormProjectorCommutatorL2 D U ^ 2 / 2 := by
  obtain ⟨i, j, hij, hsupport⟩ := h
  let p : (Projective.interface n).Cell D → ℝ :=
    fun c => cellCommutatorOpNormSq D U c
  let C : ℝ := maxSubsetCommutatorOpNorm D U
  let A : ℝ := operatorNormProjectorCommutatorL2 D U ^ 2
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
      sum_except_two_eq_tail' p hij
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
  have hi_le : p i ≤ C ^ 2 := by
    rw [← singletonSubsetCommutatorOpNormSq_eq_cell D U i]
    exact (sq_le_sq₀ (norm_nonneg _) hC0).2 hCi
  have hj_le : p j ≤ C ^ 2 := by
    rw [← singletonSubsetCommutatorOpNormSq_eq_cell D U j]
    exact (sq_le_sq₀ (norm_nonneg _) hC0).2 hCj
  have hlower : A / 2 ≤ C ^ 2 := by
    rw [hsumtwo]
    nlinarith
  have hupper : C ^ 2 ≤ A / 2 := by
    simpa [C, A] using maxSubsetCommutatorOpNorm_sq_le_half_globalSq D U
  exact le_antisymm hupper hlower

/-- For positive global defect, finite cut-envelope saturation is equivalent
to exact support on two distinct cells. -/
theorem maxCut_saturation_iff_cellCommutatorSupportedOnTwo
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (hdelta : 0 < operatorNormProjectorCommutatorL2 D U) :
    maxSubsetCommutatorOpNorm D U ^ 2 =
        operatorNormProjectorCommutatorL2 D U ^ 2 / 2 ↔
      CellCommutatorSupportedOnTwo D U := by
  constructor
  · exact cellCommutatorSupportedOnTwo_of_maxCut_saturation D U hdelta
  · exact maxCut_saturation_of_cellCommutatorSupportedOnTwo D U

end
end EverettianDecoherence.Approximation

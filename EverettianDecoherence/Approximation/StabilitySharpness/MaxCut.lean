import EverettianDecoherence.Approximation.StabilitySharpness.GlobalBudget

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped Classical BigOperators

noncomputable section

theorem iterationSharpnessC_le_one_for_stability (m : ℕ) :
    iterationSharpnessC m ≤ 1 := by
  have hC0 := iterationSharpnessC_nonneg m
  have hCS := iterationSharpnessC_sq_add_S_sq m
  nlinarith [sq_nonneg (iterationSharpnessS m)]

theorem stabilitySharpnessD_nonneg (m : ℕ) :
    0 ≤ stabilitySharpnessD m := by
  unfold stabilitySharpnessD
  linarith [iterationSharpnessC_le_one_for_stability m]

theorem stabilitySharpnessD_le_one (m : ℕ) :
    stabilitySharpnessD m ≤ 1 := by
  unfold stabilitySharpnessD
  linarith [iterationSharpnessC_nonneg m]

private theorem stabilitySharpnessCell0_budget_le_s_sq (n m : ℕ) :
    cellCommutatorOpNormSq stabilitySharpnessPerspective3
      (stabilitySharpnessRotation n m)
      (stabilitySharpnessCell3 (0 : Fin 3)) ≤
      iterationSharpnessS m ^ 2 := by
  rw [stabilitySharpnessCell0_budget_sq]
  have hAB := stabilitySharpnessA_sq_add_B_sq n
  have hCS := iterationSharpnessC_sq_add_S_sq m
  have hD0 := stabilitySharpnessD_nonneg m
  have hC0 := iterationSharpnessC_nonneg m
  have hdiag :
      iterationSharpnessC m ≤
        1 - stabilitySharpnessD m * stabilitySharpnessA n ^ 2 := by
    have hrewrite :
        1 - stabilitySharpnessD m * stabilitySharpnessA n ^ 2 =
          iterationSharpnessC m +
            stabilitySharpnessD m * stabilitySharpnessB n ^ 2 := by
      unfold stabilitySharpnessD
      nlinarith
    rw [hrewrite]
    exact le_add_of_nonneg_right
      (mul_nonneg hD0 (sq_nonneg _))
  have hdiag0 :
      0 ≤ 1 - stabilitySharpnessD m * stabilitySharpnessA n ^ 2 :=
    hC0.trans hdiag
  have hsq :
      iterationSharpnessC m ^ 2 ≤
        (1 - stabilitySharpnessD m * stabilitySharpnessA n ^ 2) ^ 2 :=
    (sq_le_sq₀ hC0 hdiag0).2 hdiag
  have hform :
      2 * stabilitySharpnessD m * stabilitySharpnessA n ^ 2 -
          stabilitySharpnessD m ^ 2 * stabilitySharpnessA n ^ 4 =
        1 -
          (1 - stabilitySharpnessD m * stabilitySharpnessA n ^ 2) ^ 2 := by
    unfold stabilitySharpnessD
    ring
  rw [hform]
  nlinarith

private theorem stabilitySharpnessCell1_budget_le_s_sq (n m : ℕ) :
    cellCommutatorOpNormSq stabilitySharpnessPerspective3
      (stabilitySharpnessRotation n m)
      (stabilitySharpnessCell3 (1 : Fin 3)) ≤
      iterationSharpnessS m ^ 2 := by
  rw [stabilitySharpnessCell1_budget_sq]
  have hAB := stabilitySharpnessA_sq_add_B_sq n
  have hCS := iterationSharpnessC_sq_add_S_sq m
  have hD0 := stabilitySharpnessD_nonneg m
  have hC0 := iterationSharpnessC_nonneg m
  have hdiag :
      iterationSharpnessC m ≤
        1 - stabilitySharpnessD m * stabilitySharpnessB n ^ 2 := by
    have hrewrite :
        1 - stabilitySharpnessD m * stabilitySharpnessB n ^ 2 =
          iterationSharpnessC m +
            stabilitySharpnessD m * stabilitySharpnessA n ^ 2 := by
      unfold stabilitySharpnessD
      nlinarith
    rw [hrewrite]
    positivity
  have hdiag0 :
      0 ≤ 1 - stabilitySharpnessD m * stabilitySharpnessB n ^ 2 :=
    hC0.trans hdiag
  have hsq :
      iterationSharpnessC m ^ 2 ≤
        (1 - stabilitySharpnessD m * stabilitySharpnessB n ^ 2) ^ 2 :=
    (sq_le_sq₀ hC0 hdiag0).2 hdiag
  have hform :
      2 * stabilitySharpnessD m * stabilitySharpnessB n ^ 2 -
          stabilitySharpnessD m ^ 2 * stabilitySharpnessB n ^ 4 =
        1 -
          (1 - stabilitySharpnessD m * stabilitySharpnessB n ^ 2) ^ 2 := by
    unfold stabilitySharpnessD
    ring
  rw [hform]
  nlinarith

theorem stabilitySharpness_cell_budget_le_s_sq
    (n m : ℕ)
    (c :
      (Projective.interface 3).Cell stabilitySharpnessPerspective3) :
    cellCommutatorOpNormSq stabilitySharpnessPerspective3
      (stabilitySharpnessRotation n m) c ≤
      iterationSharpnessS m ^ 2 := by
  obtain ⟨i, hi⟩ := stabilitySharpnessCell3_bijective.2 c
  rw [← hi]
  fin_cases i
  · exact stabilitySharpnessCell0_budget_le_s_sq n m
  · exact stabilitySharpnessCell1_budget_le_s_sq n m
  · rw [stabilitySharpnessCell2_budget_sq]

private theorem stabilitySharpness_subset_opNorm_le_s_of_card_le_one
    (n m : ℕ)
    (S :
      Finset ((Projective.interface 3).Cell stabilitySharpnessPerspective3))
    (hcard : S.card ≤ 1) :
    ‖recordSubsetProjectorCommutatorCLM stabilitySharpnessPerspective3
        (stabilitySharpnessRotation n m) S‖ ≤
      iterationSharpnessS m := by
  have hs0 : 0 ≤ iterationSharpnessS m :=
    (iterationSharpnessS_pos m).le
  by_cases hzero : S.card = 0
  · have hS : S = ∅ := Finset.card_eq_zero.mp hzero
    subst S
    have hsq :=
      recordSubsetProjectorCommutatorCLM_opNorm_sq_le_subsetSq
        stabilitySharpnessPerspective3
        (stabilitySharpnessRotation n m) ∅
    have hnorm0 :
        ‖recordSubsetProjectorCommutatorCLM stabilitySharpnessPerspective3
          (stabilitySharpnessRotation n m) ∅‖ = 0 := by
      unfold subsetProjectorCommutatorOpNormSq at hsq
      simp at hsq
      simpa [hsq]
    rw [hnorm0]
    exact hs0
  · have hone : S.card = 1 := by omega
    obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp hone
    have hsq :
        ‖recordSubsetProjectorCommutatorCLM stabilitySharpnessPerspective3
            (stabilitySharpnessRotation n m) {c}‖ ^ 2 ≤
          iterationSharpnessS m ^ 2 := by
      rw [singletonSubsetCommutatorOpNormSq_eq_cell]
      exact stabilitySharpness_cell_budget_le_s_sq n m c
    exact
      (sq_le_sq₀
        (norm_nonneg
          (recordSubsetProjectorCommutatorCLM stabilitySharpnessPerspective3
            (stabilitySharpnessRotation n m) {c}))
        hs0).1 hsq

theorem stabilitySharpness_subset_opNorm_le_s
    (n m : ℕ)
    (S :
      Finset ((Projective.interface 3).Cell stabilitySharpnessPerspective3)) :
    ‖recordSubsetProjectorCommutatorCLM stabilitySharpnessPerspective3
        (stabilitySharpnessRotation n m) S‖ ≤
      iterationSharpnessS m := by
  by_cases hsmall : S.card ≤ 1
  · exact stabilitySharpness_subset_opNorm_le_s_of_card_le_one
      n m S hsmall
  · have htype :
        Fintype.card
          ((Projective.interface 3).Cell stabilitySharpnessPerspective3) = 3 := by
      calc
        Fintype.card
            ((Projective.interface 3).Cell stabilitySharpnessPerspective3) =
          Fintype.card (Fin 3) :=
            Fintype.card_congr stabilitySharpnessCellEquiv3.symm
        _ = 3 := Fintype.card_fin 3
    have hcompl : Sᶜ.card ≤ 1 := by
      rw [Finset.card_compl, htype]
      have hle : S.card ≤ 3 := by
        have := S.card_le_univ
        rwa [htype] at this
      omega
    have h :=
      stabilitySharpness_subset_opNorm_le_s_of_card_le_one
        n m Sᶜ hcompl
    rw [recordSubsetProjectorCommutatorCLM_opNorm_compl
      stabilitySharpnessPerspective3 (stabilitySharpnessRotation n m) S] at h
    exact h

/-- The finite cut envelope of the C3 sharpness family is exactly s_m. -/
theorem stabilitySharpness_maxCut_eq_s (n m : ℕ) :
    maxSubsetCommutatorOpNorm stabilitySharpnessPerspective3
        (stabilitySharpnessRotation n m) =
      iterationSharpnessS m := by
  apply le_antisymm
  · obtain ⟨S, hS⟩ :=
      exists_subsetCommutatorOpNorm_eq_max
        stabilitySharpnessPerspective3 (stabilitySharpnessRotation n m)
    rw [← hS]
    exact stabilitySharpness_subset_opNorm_le_s n m S
  · have hsq :
        ‖recordSubsetProjectorCommutatorCLM stabilitySharpnessPerspective3
            (stabilitySharpnessRotation n m)
            {stabilitySharpnessCell3 (2 : Fin 3)}‖ ^ 2 =
          iterationSharpnessS m ^ 2 := by
      rw [singletonSubsetCommutatorOpNormSq_eq_cell,
        stabilitySharpnessCell2_budget_sq]
    have heq :
        ‖recordSubsetProjectorCommutatorCLM stabilitySharpnessPerspective3
            (stabilitySharpnessRotation n m)
            {stabilitySharpnessCell3 (2 : Fin 3)}‖ =
          iterationSharpnessS m := by
      nlinarith [
        norm_nonneg
          (recordSubsetProjectorCommutatorCLM stabilitySharpnessPerspective3
            (stabilitySharpnessRotation n m)
            {stabilitySharpnessCell3 (2 : Fin 3)}),
        iterationSharpnessS_pos m]
    rw [← heq]
    exact subsetCommutatorOpNorm_le_max
      stabilitySharpnessPerspective3 (stabilitySharpnessRotation n m)
      {stabilitySharpnessCell3 (2 : Fin 3)}

end
end EverettianDecoherence.Approximation

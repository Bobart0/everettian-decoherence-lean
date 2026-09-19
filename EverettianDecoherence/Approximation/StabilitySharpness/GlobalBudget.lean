import EverettianDecoherence.Approximation.StabilitySharpness.CellBudgets

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped Classical BigOperators

noncomputable section

theorem stabilitySharpnessCell3_bijective :
    Function.Bijective
      (stabilitySharpnessCell3 :
        Fin 3 →
          (Projective.interface 3).Cell stabilitySharpnessPerspective3) := by
  constructor
  · intro i j hij
    by_contra hne
    exact stabilitySharpnessCell3_ne hne hij
  · intro c
    rcases c with ⟨V, hV⟩
    change
      V ∈
        (Perspective.basisPerspective stabilitySharpnessBasis3).cells
      at hV
    change
      V ∈
        Finset.univ.image
          (fun i : Fin 3 =>
            ℂ ∙ (stabilitySharpnessBasis3 i : H 3))
      at hV
    obtain ⟨i, _hi, hVi⟩ := Finset.mem_image.mp hV
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hVi.symm

noncomputable def stabilitySharpnessCellEquiv3 :
    Fin 3 ≃
      (Projective.interface 3).Cell stabilitySharpnessPerspective3 :=
  Equiv.ofBijective stabilitySharpnessCell3
    stabilitySharpnessCell3_bijective

@[simp]
theorem stabilitySharpnessCellEquiv3_apply (i : Fin 3) :
    stabilitySharpnessCellEquiv3 i = stabilitySharpnessCell3 i := by
  rfl

theorem sum_stabilitySharpnessCells
    (f :
      (Projective.interface 3).Cell stabilitySharpnessPerspective3 → ℝ) :
    (∑ c, f c) =
      ∑ i : Fin 3, f (stabilitySharpnessCell3 i) := by
  symm
  exact Fintype.sum_equiv stabilitySharpnessCellEquiv3
    (fun i => f (stabilitySharpnessCell3 i)) f (fun i => rfl)

/-- Closed global squared L2 commutator budget for the C3 sharpness family. -/
theorem stabilitySharpness_globalSq (n m : ℕ) :
    operatorNormProjectorCommutatorL2 stabilitySharpnessPerspective3
        (stabilitySharpnessRotation n m) ^ 2 =
      2 * iterationSharpnessS m ^ 2 +
        2 * stabilitySharpnessD m ^ 2 *
          stabilitySharpnessA n ^ 2 * stabilitySharpnessB n ^ 2 := by
  rw [← sum_cellCommutatorOpNormSq_eq_globalSq]
  rw [sum_stabilitySharpnessCells]
  rw [Fin.sum_univ_three]
  rw [stabilitySharpnessCell0_budget_sq,
    stabilitySharpnessCell1_budget_sq,
    stabilitySharpnessCell2_budget_sq]
  have hAB := stabilitySharpnessA_sq_add_B_sq n
  have hCS := iterationSharpnessC_sq_add_S_sq m
  have hsD :
      iterationSharpnessS m ^ 2 =
        2 * stabilitySharpnessD m - stabilitySharpnessD m ^ 2 := by
    unfold stabilitySharpnessD
    nlinarith
  have hfour :
      stabilitySharpnessA n ^ 4 + stabilitySharpnessB n ^ 4 =
        1 -
          2 * stabilitySharpnessA n ^ 2 *
            stabilitySharpnessB n ^ 2 := by
    calc
      stabilitySharpnessA n ^ 4 + stabilitySharpnessB n ^ 4 =
          (stabilitySharpnessA n ^ 2 + stabilitySharpnessB n ^ 2) ^ 2 -
            2 * stabilitySharpnessA n ^ 2 *
              stabilitySharpnessB n ^ 2 := by ring
      _ = 1 -
            2 * stabilitySharpnessA n ^ 2 *
              stabilitySharpnessB n ^ 2 := by rw [hAB]; ring
  rw [hsD]
  nlinarith

end
end EverettianDecoherence.Approximation

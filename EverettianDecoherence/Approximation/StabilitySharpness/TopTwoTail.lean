import EverettianDecoherence.Approximation.StabilitySharpness.EtaTail

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped Classical BigOperators

noncomputable section

theorem stabilitySharpnessB_le_A (n : ℕ) :
    stabilitySharpnessB n ≤ stabilitySharpnessA n := by
  unfold stabilitySharpnessA stabilitySharpnessB
  have hs : 0 < Real.sqrt (2 : ℝ) := stabilitySharpness_sqrt_two_pos
  apply (div_le_div_iff_of_pos_right hs).2
  nlinarith [sharpnessB_nonneg n]

theorem stabilitySharpnessB_sq_le_A_sq (n : ℕ) :
    stabilitySharpnessB n ^ 2 ≤ stabilitySharpnessA n ^ 2 := by
  exact (sq_le_sq₀ (stabilitySharpnessB_nonneg n)
    (stabilitySharpnessA_nonneg n)).2 (stabilitySharpnessB_le_A n)

theorem stabilitySharpnessCell1_budget_le_cell0 (n m : ℕ) :
    cellCommutatorOpNormSq stabilitySharpnessPerspective3
        (stabilitySharpnessRotation n m)
        (stabilitySharpnessCell3 (1 : Fin 3)) ≤
      cellCommutatorOpNormSq stabilitySharpnessPerspective3
        (stabilitySharpnessRotation n m)
        (stabilitySharpnessCell3 (0 : Fin 3)) := by
  rw [stabilitySharpnessCell0_budget_sq,
    stabilitySharpnessCell1_budget_sq]
  have hAB := stabilitySharpnessA_sq_add_B_sq n
  have hCS := iterationSharpnessC_sq_add_S_sq m
  have hsD :
      iterationSharpnessS m ^ 2 =
        2 * stabilitySharpnessD m - stabilitySharpnessD m ^ 2 := by
    unfold stabilitySharpnessD
    nlinarith
  have hdiff :
      (2 * stabilitySharpnessD m * stabilitySharpnessA n ^ 2 -
          stabilitySharpnessD m ^ 2 * stabilitySharpnessA n ^ 4) -
        (2 * stabilitySharpnessD m * stabilitySharpnessB n ^ 2 -
          stabilitySharpnessD m ^ 2 * stabilitySharpnessB n ^ 4) =
        (stabilitySharpnessA n ^ 2 - stabilitySharpnessB n ^ 2) *
          iterationSharpnessS m ^ 2 := by
    calc
      _ =
          (stabilitySharpnessA n ^ 2 - stabilitySharpnessB n ^ 2) *
            (2 * stabilitySharpnessD m -
              stabilitySharpnessD m ^ 2 *
                (stabilitySharpnessA n ^ 2 + stabilitySharpnessB n ^ 2)) := by
          ring
      _ =
          (stabilitySharpnessA n ^ 2 - stabilitySharpnessB n ^ 2) *
            iterationSharpnessS m ^ 2 := by
          rw [hAB, hsD]
          ring
  have hnonneg :
      0 ≤
        (stabilitySharpnessA n ^ 2 - stabilitySharpnessB n ^ 2) *
          iterationSharpnessS m ^ 2 := by
    positivity
  nlinarith

theorem stabilitySharpnessCell1_budget_le_cell2 (n m : ℕ) :
    cellCommutatorOpNormSq stabilitySharpnessPerspective3
        (stabilitySharpnessRotation n m)
        (stabilitySharpnessCell3 (1 : Fin 3)) ≤
      cellCommutatorOpNormSq stabilitySharpnessPerspective3
        (stabilitySharpnessRotation n m)
        (stabilitySharpnessCell3 (2 : Fin 3)) := by
  rw [stabilitySharpnessCell2_budget_sq]
  exact stabilitySharpness_cell_budget_le_s_sq n m
    (stabilitySharpnessCell3 (1 : Fin 3))

/-- Canonical top-two tail fraction for the three-cell family: omit the
smallest of the three cellwise quadratic budgets. -/
noncomputable def stabilitySharpnessTopTwoTail (n m : ℕ) : ℝ :=
  let a0 :=
    cellCommutatorOpNormSq stabilitySharpnessPerspective3
      (stabilitySharpnessRotation n m)
      (stabilitySharpnessCell3 (0 : Fin 3))
  let a1 :=
    cellCommutatorOpNormSq stabilitySharpnessPerspective3
      (stabilitySharpnessRotation n m)
      (stabilitySharpnessCell3 (1 : Fin 3))
  let a2 :=
    cellCommutatorOpNormSq stabilitySharpnessPerspective3
      (stabilitySharpnessRotation n m)
      (stabilitySharpnessCell3 (2 : Fin 3))
  min a0 (min a1 a2) /
    operatorNormProjectorCommutatorL2 stabilitySharpnessPerspective3
      (stabilitySharpnessRotation n m) ^ 2

theorem stabilitySharpnessTopTwoTail_eq_Tau (n m : ℕ) :
    stabilitySharpnessTopTwoTail n m = stabilitySharpnessTau n m := by
  unfold stabilitySharpnessTopTwoTail stabilitySharpnessTau
  dsimp
  rw [min_eq_left (stabilitySharpnessCell1_budget_le_cell2 n m)]
  rw [min_eq_right (stabilitySharpnessCell1_budget_le_cell0 n m)]

end
end EverettianDecoherence.Approximation

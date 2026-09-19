import EverettianDecoherence.Approximation.StabilitySharpness.MaxCut

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open Filter
open scoped Classical BigOperators Topology

noncomputable section

/-- Relative quadratic deficit of finite-cut saturation for the C3 family. -/
noncomputable def stabilitySharpnessEta (n m : ℕ) : ℝ :=
  let δ := operatorNormProjectorCommutatorL2 stabilitySharpnessPerspective3
    (stabilitySharpnessRotation n m)
  let C := maxSubsetCommutatorOpNorm stabilitySharpnessPerspective3
    (stabilitySharpnessRotation n m)
  (δ ^ 2 - 2 * C ^ 2) / δ ^ 2

/-- Tail fraction obtained by retaining cells 0 and 2, hence leaving cell 1. -/
noncomputable def stabilitySharpnessTau (n m : ℕ) : ℝ :=
  cellCommutatorOpNormSq stabilitySharpnessPerspective3
      (stabilitySharpnessRotation n m)
      (stabilitySharpnessCell3 (1 : Fin 3)) /
    operatorNormProjectorCommutatorL2 stabilitySharpnessPerspective3
      (stabilitySharpnessRotation n m) ^ 2

theorem stabilitySharpnessA_pos (n : ℕ) :
    0 < stabilitySharpnessA n := by
  rw [stabilitySharpnessA_eq_P_div]
  positivity

theorem stabilitySharpnessD_pos (m : ℕ) :
    0 < stabilitySharpnessD m := by
  unfold stabilitySharpnessD
  have hS := iterationSharpnessS_pos m
  have hCS := iterationSharpnessC_sq_add_S_sq m
  have hC0 := iterationSharpnessC_nonneg m
  nlinarith

theorem stabilitySharpness_delta_pos (n m : ℕ) :
    0 <
      operatorNormProjectorCommutatorL2 stabilitySharpnessPerspective3
        (stabilitySharpnessRotation n m) := by
  have hsq := stabilitySharpness_globalSq n m
  have hs := iterationSharpnessS_pos m
  have hextra :
      0 ≤
        2 * stabilitySharpnessD m ^ 2 *
          stabilitySharpnessA n ^ 2 * stabilitySharpnessB n ^ 2 := by
    positivity
  have hδ0 :=
    operatorNormProjectorCommutatorL2_nonneg
      stabilitySharpnessPerspective3 (stabilitySharpnessRotation n m)
  nlinarith

theorem stabilitySharpnessEta_exact (n m : ℕ) :
    stabilitySharpnessEta n m =
      (2 * stabilitySharpnessD m ^ 2 *
          stabilitySharpnessA n ^ 2 * stabilitySharpnessB n ^ 2) /
        (2 * iterationSharpnessS m ^ 2 +
          2 * stabilitySharpnessD m ^ 2 *
            stabilitySharpnessA n ^ 2 * stabilitySharpnessB n ^ 2) := by
  unfold stabilitySharpnessEta
  dsimp
  rw [stabilitySharpness_maxCut_eq_s, stabilitySharpness_globalSq]
  ring

theorem stabilitySharpnessTau_exact (n m : ℕ) :
    stabilitySharpnessTau n m =
      (2 * stabilitySharpnessD m * stabilitySharpnessB n ^ 2 -
          stabilitySharpnessD m ^ 2 * stabilitySharpnessB n ^ 4) /
        (2 * iterationSharpnessS m ^ 2 +
          2 * stabilitySharpnessD m ^ 2 *
            stabilitySharpnessA n ^ 2 * stabilitySharpnessB n ^ 2) := by
  unfold stabilitySharpnessTau
  rw [stabilitySharpnessCell1_budget_sq, stabilitySharpness_globalSq]

theorem stabilitySharpnessEta_pos (n m : ℕ) :
    0 < stabilitySharpnessEta n m := by
  rw [stabilitySharpnessEta_exact]
  have hD := stabilitySharpnessD_pos m
  have hA := stabilitySharpnessA_pos n
  have hB := stabilitySharpnessB_pos n
  have hs := iterationSharpnessS_pos m
  positivity

/-- Exact ratio between the retained-pair tail and the saturation deficit. -/
theorem stabilitySharpnessTau_div_Eta_exact (n m : ℕ) :
    stabilitySharpnessTau n m / stabilitySharpnessEta n m =
      (2 - stabilitySharpnessD m * stabilitySharpnessB n ^ 2) /
        (2 * stabilitySharpnessD m * stabilitySharpnessA n ^ 2) := by
  rw [stabilitySharpnessTau_exact, stabilitySharpnessEta_exact]
  have hD : stabilitySharpnessD m ≠ 0 :=
    ne_of_gt (stabilitySharpnessD_pos m)
  have hA : stabilitySharpnessA n ≠ 0 :=
    ne_of_gt (stabilitySharpnessA_pos n)
  have hB : stabilitySharpnessB n ≠ 0 :=
    ne_of_gt (stabilitySharpnessB_pos n)
  have hs : iterationSharpnessS m ≠ 0 :=
    ne_of_gt (iterationSharpnessS_pos m)
  field_simp [hD, hA, hB, hs]
  ring

end
end EverettianDecoherence.Approximation

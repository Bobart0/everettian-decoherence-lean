import EverettianDecoherence.Approximation.OptimalTwoCellTail
import EverettianDecoherence.Approximation.CutEnvelopeStabilitySharp
import EverettianDecoherence.Approximation.V12AsymptoticEight
import EverettianDecoherence.Approximation.V12UltraNearFour

/-!
Publication-facing exact-tail corollaries.

The historical stability API states two-cell concentration existentially.
This file translates those theorems to the exact optimal relative tail
`optimalTwoCellTailFraction`, which is the manuscript quantity tau.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open Filter
open scoped BigOperators Classical Topology

noncomputable section

theorem optimalTwoCellTail_eq_globalSq_mul_fraction
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (hdelta : 0 < operatorNormProjectorCommutatorL2 D U) :
    optimalTwoCellTail D U =
      operatorNormProjectorCommutatorL2 D U ^ 2 *
        optimalTwoCellTailFraction D U := by
  unfold optimalTwoCellTailFraction
  have hA :
      operatorNormProjectorCommutatorL2 D U ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_pos hdelta)
  field_simp [hA]

/-- Exact publication-facing finite stability theorem with coefficient 18. -/
theorem optimalTwoCellTailFraction_le_modulus18_of_maxCut_near_saturated
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (η : ℝ)
    (hη0 : 0 ≤ η)
    (hηfive : η ≤ 1 / 5)
    (hdelta : 0 < operatorNormProjectorCommutatorL2 D U)
    (hnear :
      2 * (1 - η) * operatorNormProjectorCommutatorL2 D U ^ 2 ≤
        (2 * maxSubsetCommutatorOpNorm D U) ^ 2) :
    optimalTwoCellTailFraction D U ≤
      twoCellStabilityModulus18
        (operatorNormProjectorCommutatorL2 D U) η := by
  have hconc :=
    twoCellCommutatorConcentratedWithin18_of_maxCut_near_saturated
      D U η (operatorNormProjectorCommutatorL2 D U)
      hη0 hηfive hdelta le_rfl hnear
  exact optimalTwoCellTailFraction_le_of_concentratedWithin
    D U _ hdelta hconc

/-- Expanded manuscript form:
tau <= 2 eta + 18 eta / ((1-3 eta) delta^2). -/
theorem optimalTwoCellTailFraction_le_18_expanded
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (η : ℝ)
    (hη0 : 0 ≤ η)
    (hηfive : η ≤ 1 / 5)
    (hdelta : 0 < operatorNormProjectorCommutatorL2 D U)
    (hnear :
      2 * (1 - η) * operatorNormProjectorCommutatorL2 D U ^ 2 ≤
        (2 * maxSubsetCommutatorOpNorm D U) ^ 2) :
    optimalTwoCellTailFraction D U ≤
      2 * η +
        18 * η /
          ((1 - 3 * η) *
            operatorNormProjectorCommutatorL2 D U ^ 2) := by
  have h :=
    optimalTwoCellTailFraction_le_modulus18_of_maxCut_near_saturated
      D U η hη0 hηfive hdelta hnear
  unfold twoCellStabilityModulus18 at h
  have hA :
      operatorNormProjectorCommutatorL2 D U ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_pos hdelta)
  have hq : 1 - 3 * η ≠ 0 := by
    nlinarith
  calc
    optimalTwoCellTailFraction D U
        ≤ 2 * η +
          (18 * η / (1 - 3 * η)) /
            operatorNormProjectorCommutatorL2 D U ^ 2 := h
    _ = 2 * η +
        18 * η /
          ((1 - 3 * η) *
            operatorNormProjectorCommutatorL2 D U ^ 2) := by
      field_simp [hA, hq]
      <;> ring

/-- Publication-facing coefficient 8: the exact optimal absolute tail,
equivalently delta^2 tau, is eventually at most c eta for every c>8. -/
theorem eventually_optimalTail_le_of_small_defect
    (dim : ℕ → ℕ)
    (D : (k : ℕ) → Perspective (dim k))
    (U : (k : ℕ) → H (dim k) ≃ₗᵢ[ℂ] H (dim k))
    (eta : ℕ → ℝ)
    (hdelta : ∀ k, 0 < operatorNormProjectorCommutatorL2 (D k) (U k))
    (hetaPos : ∀ k, 0 < eta k)
    (hexact : ∀ k,
      maxCutEnvelopeDefect (D k) (U k) =
        eta k * operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2)
    (hA :
      Tendsto
        (fun k =>
          operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2)
        atTop (𝓝 0))
    (heta : Tendsto eta atTop (𝓝 0))
    (c : ℝ) (hc : 8 < c) :
    ∀ᶠ k in atTop,
      optimalTwoCellTail (D k) (U k) ≤ c * eta k := by
  have h :=
    eventually_two_cell_tail_le_of_small_defect
      dim D U eta hdelta hetaPos hexact hA heta c hc
  filter_upwards [h] with k hk
  obtain ⟨i, j, hij, htail⟩ := hk
  exact optimalTwoCellTail_le_of_pair
    (D k) (U k) i j hij (c * eta k) htail

/-- Same coefficient-8 theorem written literally as delta^2 tau <= c eta. -/
theorem eventually_globalSq_mul_optimalTau_le_of_small_defect
    (dim : ℕ → ℕ)
    (D : (k : ℕ) → Perspective (dim k))
    (U : (k : ℕ) → H (dim k) ≃ₗᵢ[ℂ] H (dim k))
    (eta : ℕ → ℝ)
    (hdelta : ∀ k, 0 < operatorNormProjectorCommutatorL2 (D k) (U k))
    (hetaPos : ∀ k, 0 < eta k)
    (hexact : ∀ k,
      maxCutEnvelopeDefect (D k) (U k) =
        eta k * operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2)
    (hA :
      Tendsto
        (fun k =>
          operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2)
        atTop (𝓝 0))
    (heta : Tendsto eta atTop (𝓝 0))
    (c : ℝ) (hc : 8 < c) :
    ∀ᶠ k in atTop,
      operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2 *
          optimalTwoCellTailFraction (D k) (U k) ≤
        c * eta k := by
  have h :=
    eventually_optimalTail_le_of_small_defect
      dim D U eta hdelta hetaPos hexact hA heta c hc
  filter_upwards [h] with k hk
  rw [← optimalTwoCellTail_eq_globalSq_mul_fraction
    (D k) (U k) (hdelta k)]
  exact hk

/-- Publication-facing ultra-near coefficient 4 for the exact optimal tail. -/
theorem eventually_optimalTail_le_of_ultra_near
    (dim : ℕ → ℕ)
    (D : (k : ℕ) → Perspective (dim k))
    (U : (k : ℕ) → H (dim k) ≃ₗᵢ[ℂ] H (dim k))
    (eta : ℕ → ℝ)
    (hdelta : ∀ k, 0 < operatorNormProjectorCommutatorL2 (D k) (U k))
    (hetaPos : ∀ k, 0 < eta k)
    (hexact : ∀ k,
      maxCutEnvelopeDefect (D k) (U k) =
        eta k * operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2)
    (hA :
      Tendsto
        (fun k =>
          operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2)
        atTop (𝓝 0))
    (heta : Tendsto eta atTop (𝓝 0))
    (hultra :
      Tendsto
        (fun k =>
          eta k /
            operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2)
        atTop (𝓝 0))
    (c : ℝ) (hc : 4 < c) :
    ∀ᶠ k in atTop,
      optimalTwoCellTail (D k) (U k) ≤ c * eta k := by
  have h :=
    eventually_two_cell_tail_le_of_ultra_near
      dim D U eta hdelta hetaPos hexact hA heta hultra c hc
  filter_upwards [h] with k hk
  obtain ⟨i, j, hij, htail⟩ := hk
  exact optimalTwoCellTail_le_of_pair
    (D k) (U k) i j hij (c * eta k) htail

/-- Same coefficient-4 theorem written literally as delta^2 tau <= c eta. -/
theorem eventually_globalSq_mul_optimalTau_le_of_ultra_near
    (dim : ℕ → ℕ)
    (D : (k : ℕ) → Perspective (dim k))
    (U : (k : ℕ) → H (dim k) ≃ₗᵢ[ℂ] H (dim k))
    (eta : ℕ → ℝ)
    (hdelta : ∀ k, 0 < operatorNormProjectorCommutatorL2 (D k) (U k))
    (hetaPos : ∀ k, 0 < eta k)
    (hexact : ∀ k,
      maxCutEnvelopeDefect (D k) (U k) =
        eta k * operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2)
    (hA :
      Tendsto
        (fun k =>
          operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2)
        atTop (𝓝 0))
    (heta : Tendsto eta atTop (𝓝 0))
    (hultra :
      Tendsto
        (fun k =>
          eta k /
            operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2)
        atTop (𝓝 0))
    (c : ℝ) (hc : 4 < c) :
    ∀ᶠ k in atTop,
      operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2 *
          optimalTwoCellTailFraction (D k) (U k) ≤
        c * eta k := by
  have h :=
    eventually_optimalTail_le_of_ultra_near
      dim D U eta hdelta hetaPos hexact hA heta hultra c hc
  filter_upwards [h] with k hk
  rw [← optimalTwoCellTail_eq_globalSq_mul_fraction
    (D k) (U k) (hdelta k)]
  exact hk

end
end EverettianDecoherence.Approximation

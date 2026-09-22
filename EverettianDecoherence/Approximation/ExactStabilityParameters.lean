import EverettianDecoherence.Approximation.OptimalTwoCellTail
import EverettianDecoherence.Approximation.CutEnvelopeStabilitySharp
import EverettianDecoherence.Approximation.MaxCutThresholdStability

/-!
Publication-facing exact relative parameters eta and tau, plus the exact
finite coefficient-18 slope bound.  This bridges the robust division-free
Lean stability predicate with the manuscript's normalized quantities.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped Classical

noncomputable section

noncomputable def exactMaxCutEta
    {n : ℕ} (D : Perspective n) (U : H n ≃ₗᵢ[ℂ] H n) : ℝ :=
  maxCutEnvelopeDefect D U /
    operatorNormProjectorCommutatorL2 D U ^ 2

noncomputable def exactTwoCellTau
    {n : ℕ} (D : Perspective n) (U : H n ≃ₗᵢ[ℂ] H n) : ℝ :=
  optimalTwoCellTailFraction D U

theorem exactMaxCutEta_mul_globalSq
    {n : ℕ} (D : Perspective n) (U : H n ≃ₗᵢ[ℂ] H n)
    (hdelta : 0 < operatorNormProjectorCommutatorL2 D U) :
    exactMaxCutEta D U * operatorNormProjectorCommutatorL2 D U ^ 2 =
      maxCutEnvelopeDefect D U := by
  unfold exactMaxCutEta
  field_simp [ne_of_gt (sq_pos_of_pos hdelta)]

theorem exactTwoCellTau_mul_globalSq
    {n : ℕ} (D : Perspective n) (U : H n ≃ₗᵢ[ℂ] H n)
    (hdelta : 0 < operatorNormProjectorCommutatorL2 D U) :
    exactTwoCellTau D U * operatorNormProjectorCommutatorL2 D U ^ 2 =
      optimalTwoCellTail D U := by
  unfold exactTwoCellTau optimalTwoCellTailFraction
  field_simp [ne_of_gt (sq_pos_of_pos hdelta)]

theorem exactMaxCutEta_nonneg
    {n : ℕ} (D : Perspective n) (U : H n ≃ₗᵢ[ℂ] H n) :
    0 ≤ exactMaxCutEta D U := by
  unfold exactMaxCutEta
  exact div_nonneg (maxCutEnvelopeDefect_nonneg D U) (sq_nonneg _)

theorem exactTwoCellTau_nonneg
    {n : ℕ} (D : Perspective n) (U : H n ≃ₗᵢ[ℂ] H n) :
    0 ≤ exactTwoCellTau D U := by
  unfold exactTwoCellTau optimalTwoCellTailFraction
  exact div_nonneg (optimalTwoCellTail_nonneg D U) (sq_nonneg _)

theorem exactMaxCut_near_saturated
    {n : ℕ} (D : Perspective n) (U : H n ≃ₗᵢ[ℂ] H n)
    (hdelta : 0 < operatorNormProjectorCommutatorL2 D U) :
    2 * (1 - exactMaxCutEta D U) *
        operatorNormProjectorCommutatorL2 D U ^ 2 ≤
      (2 * maxSubsetCommutatorOpNorm D U) ^ 2 := by
  have heta := exactMaxCutEta_mul_globalSq D U hdelta
  unfold maxCutEnvelopeDefect at heta
  nlinarith

/-- Exact normalized finite slope version of the coefficient-18 theorem. -/
theorem exactTwoCellSlope_le_18
    {n : ℕ} (D : Perspective n) (U : H n ≃ₗᵢ[ℂ] H n)
    (hdelta : 0 < operatorNormProjectorCommutatorL2 D U)
    (hetaPos : 0 < exactMaxCutEta D U)
    (hetaFive : exactMaxCutEta D U ≤ 1 / 5) :
    exactTwoCellTau D U / exactMaxCutEta D U ≤
      2 + 18 /
        ((1 - 3 * exactMaxCutEta D U) *
          operatorNormProjectorCommutatorL2 D U ^ 2) := by
  let delta : ℝ := operatorNormProjectorCommutatorL2 D U
  let eta : ℝ := exactMaxCutEta D U
  have hconc :=
    twoCellCommutatorConcentratedWithin18_of_maxCut_near_saturated
      D U eta delta
      (by simpa [eta] using hetaPos.le)
      (by simpa [eta] using hetaFive)
      (by simpa [delta] using hdelta)
      (by simp [delta])
      (by simpa [eta, delta] using exactMaxCut_near_saturated D U hdelta)
  have htau :=
    optimalTwoCellTailFraction_le_of_concentratedWithin
      D U (twoCellStabilityModulus18 delta eta)
      (by simpa [delta] using hdelta) hconc
  change exactTwoCellTau D U ≤ twoCellStabilityModulus18 delta eta at htau
  have hq : 1 - 3 * eta ≠ 0 := by
    have : 0 < 1 - 3 * eta := by
      dsimp [eta] at hetaFive ⊢
      nlinarith
    exact ne_of_gt this
  have hdeltaSq : delta ^ 2 ≠ 0 := by
    exact ne_of_gt (sq_pos_of_pos (by simpa [delta] using hdelta))
  have hmod :
      twoCellStabilityModulus18 delta eta =
        eta * (2 + 18 / ((1 - 3 * eta) * delta ^ 2)) := by
    unfold twoCellStabilityModulus18
    field_simp [hq, hdeltaSq]
    ring
  rw [hmod] at htau
  have hdiv := (div_le_iff₀ (by simpa [eta] using hetaPos)).2 htau
  simpa [eta, delta, mul_comm, mul_left_comm, mul_assoc] using hdiv

end
end EverettianDecoherence.Approximation

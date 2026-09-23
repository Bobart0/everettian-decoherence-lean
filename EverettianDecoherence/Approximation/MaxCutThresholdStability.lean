import EverettianDecoherence.Approximation.TwoCellConcentrationThreshold
import EverettianDecoherence.Approximation.CutEnvelope
import EverettianDecoherence.Approximation.TwoCellCommutatorConcentration

/-!
**FR.** Remontée du lemme à seuil variable au cut qui réalise l'enveloppe
maximale. La conclusion est exprimée sans choisir publiquement le cut.

**EN.** Lift of the variable-threshold lemma to a cut attaining the maximal
envelope. The conclusion is stated without exposing the maximizing cut.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

/-- Exact nonnegative defect of the maximal cut envelope. -/
noncomputable def maxCutEnvelopeDefect
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) : ℝ :=
  operatorNormProjectorCommutatorL2 D U ^ 2 -
    2 * maxSubsetCommutatorOpNorm D U ^ 2

theorem maxCutEnvelopeDefect_nonneg
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) :
    0 ≤ maxCutEnvelopeDefect D U := by
  unfold maxCutEnvelopeDefect
  have h := maxSubsetCommutatorOpNorm_sq_le_half_globalSq D U
  linarith

theorem exists_two_cell_concentration_of_maxCut_threshold
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (β t : ℝ)
    (hβ0 : 0 < β) (hβone : β < 1) (ht : 0 < t)
    (hgpos : 0 < maxSubsetCommutatorOpNorm D U)
    (hLpos :
      0 <
        maxSubsetCommutatorOpNorm D U ^ 2 -
          maxCutEnvelopeDefect D U / β) :
    ∃ i j : (Projective.interface n).Cell D,
      i ≠ j ∧
      operatorNormProjectorCommutatorL2 D U ^ 2 -
          cellCommutatorOpNormSq D U i -
          cellCommutatorOpNormSq D U j ≤
        maxCutEnvelopeDefect D U / β +
        (4 * (1 + t) *
            (maxCutEnvelopeDefect D U / (1 - β)) +
          (1 + 1 / t) *
            (maxCutEnvelopeDefect D U / (1 - β)) ^ 2) /
          (maxSubsetCommutatorOpNorm D U ^ 2 -
            maxCutEnvelopeDefect D U / β) := by
  obtain ⟨S, hSmax⟩ := exists_subsetCommutatorOpNorm_eq_max D U
  have hcpos :
      0 < ‖recordSubsetProjectorCommutatorCLM D U S‖ := by
    rw [hSmax]
    exact hgpos
  have hLpos' :
      0 <
        ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2 -
          (operatorNormProjectorCommutatorL2 D U ^ 2 -
            2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) / β := by
    simpa [maxCutEnvelopeDefect, hSmax] using hLpos
  obtain ⟨i, hi, j, hj, htail⟩ :=
    exists_two_cell_concentration_of_cut_threshold
      D U S β t hβ0 hβone ht hcpos hLpos'
  have hjnot : j ∉ S := by
    simpa using hj
  have hij : i ≠ j := by
    intro hij
    apply hjnot
    simpa [hij] using hi
  refine ⟨i, j, hij, ?_⟩
  simpa [cellCommutatorOpNormSq, incomingWitnessP,
    maxCutEnvelopeDefect, hSmax] using htail

end
end EverettianDecoherence.Approximation

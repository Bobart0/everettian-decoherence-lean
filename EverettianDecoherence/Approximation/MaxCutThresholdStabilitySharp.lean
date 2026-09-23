import EverettianDecoherence.Approximation.TwoCellConcentrationThresholdSharp
import EverettianDecoherence.Approximation.MaxCutThresholdStability

/-!
**FR.** Remontée sharp du lemme à seuil variable au cut maximisant
l'enveloppe. Cette forme est la brique de l'upper bound asymptotique 4 dans
le régime ultra-near.

**EN.** Sharp lift of the variable-threshold lemma to a maximizing cut. This
is the main finite ingredient for the asymptotic upper coefficient 4 in the
ultra-near regime.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

theorem exists_two_cell_concentration_of_maxCut_threshold_sharp
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (β t : ℝ)
    (hβ0 : 0 < β) (hβone : β < 1) (ht : 0 < t)
    (hgpos : 0 < maxSubsetCommutatorOpNorm D U)
    (hLpos :
      0 <
        maxSubsetCommutatorOpNorm D U ^ 2 -
          maxCutEnvelopeDefect D U / β)
    (hKlt :
      4 * (1 + t) *
          (maxCutEnvelopeDefect D U / (1 - β)) +
        (1 + 1 / t) *
          (maxCutEnvelopeDefect D U / (1 - β)) ^ 2 <
        (maxSubsetCommutatorOpNorm D U ^ 2 -
          maxCutEnvelopeDefect D U / β) ^ 2) :
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
          (2 *
            ((maxSubsetCommutatorOpNorm D U ^ 2 -
              maxCutEnvelopeDefect D U / β) -
              (4 * (1 + t) *
                  (maxCutEnvelopeDefect D U / (1 - β)) +
                (1 + 1 / t) *
                  (maxCutEnvelopeDefect D U / (1 - β)) ^ 2) /
                (maxSubsetCommutatorOpNorm D U ^ 2 -
                  maxCutEnvelopeDefect D U / β))) := by
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
  have hKlt' :
      4 * (1 + t) *
          ((operatorNormProjectorCommutatorL2 D U ^ 2 -
            2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) /
            (1 - β)) +
        (1 + 1 / t) *
          ((operatorNormProjectorCommutatorL2 D U ^ 2 -
            2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) /
            (1 - β)) ^ 2 <
        (‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2 -
          (operatorNormProjectorCommutatorL2 D U ^ 2 -
            2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) / β) ^ 2 := by
    simpa [maxCutEnvelopeDefect, hSmax] using hKlt
  obtain ⟨i, hi, j, hj, htail⟩ :=
    exists_two_cell_concentration_of_cut_threshold_sharp
      D U S β t hβ0 hβone ht hcpos hLpos' hKlt'
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

import EverettianDecoherence.Approximation.IncomingCutConcentrationThresholdSharp
import EverettianDecoherence.Approximation.OutgoingCutConcentrationThresholdSharp

/-!
**FR.** Version sans orientation du lemme de cut sharp à seuil variable.

**EN.** Orientation-free sharp variable-threshold cut lemma.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

theorem exists_cell_concentration_of_cut_threshold_sharp
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (β t L Kbar : ℝ)
    (hβ0 : 0 < β) (hβone : β < 1) (ht : 0 < t)
    (hcpos : 0 < ‖recordSubsetProjectorCommutatorCLM D U S‖)
    (hLpos : 0 < L)
    (hL :
      L ≤ subsetProjectorCommutatorOpNormSq D U S -
        (subsetProjectorCommutatorOpNormSq D U S -
          ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) / β)
    (hKbar0 : 0 ≤ Kbar)
    (hKbarlt : Kbar < L ^ 2)
    (hKcap :
      4 * (1 + t) *
          ((subsetProjectorCommutatorOpNormSq D U S -
            ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) /
            (1 - β)) +
        (1 + 1 / t) *
          ((subsetProjectorCommutatorOpNormSq D U S -
            ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) /
            (1 - β)) ^ 2 ≤
        Kbar) :
    ∃ c ∈ S,
      subsetProjectorCommutatorOpNormSq D U S -
          incomingWitnessP D U c ≤
        (subsetProjectorCommutatorOpNormSq D U S -
          ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) / β +
        (4 * (1 + t) *
            ((subsetProjectorCommutatorOpNormSq D U S -
              ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) /
              (1 - β)) +
          (1 + 1 / t) *
            ((subsetProjectorCommutatorOpNormSq D U S -
              ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) /
              (1 - β)) ^ 2) /
          (2 * (L - Kbar / L)) := by
  have hblock :=
    recordSubsetProjectorCommutatorCLM_opNorm_eq_max_cross D U S
  rcases le_total
      ‖recordSubsetOutgoingCLM D U S‖
      ‖recordSubsetIncomingCLM D U S‖ with hout_in | hin_out
  · have hmax :
        ‖recordSubsetIncomingCLM D U S‖ =
          ‖recordSubsetProjectorCommutatorCLM D U S‖ := by
      rw [hblock, max_eq_left hout_in]
    exact exists_cell_concentration_of_incoming_max_threshold_sharp
      D U S β t L Kbar hβ0 hβone ht hmax hcpos
      hLpos hL hKbar0 hKbarlt hKcap
  · have hmax :
        ‖recordSubsetOutgoingCLM D U S‖ =
          ‖recordSubsetProjectorCommutatorCLM D U S‖ := by
      rw [hblock, max_eq_right hin_out]
    exact exists_cell_concentration_of_outgoing_max_threshold_sharp
      D U S β t L Kbar hβ0 hβone ht hmax hcpos
      hLpos hL hKbar0 hKbarlt hKcap

end
end EverettianDecoherence.Approximation

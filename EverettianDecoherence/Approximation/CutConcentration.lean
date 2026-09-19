import EverettianDecoherence.Approximation.IncomingCutConcentration
import EverettianDecoherence.Approximation.OutgoingCutConcentration

/-!
**FR.** Concentration unilatérale sans choix d'orientation. L'identité exacte
de blocs montre que la norme du commutateur agrégé est le maximum des blocs
entrant et sortant; le lemme approprié s'applique donc dans tous les cas.

**EN.** Orientation-free one-sided concentration. The exact block identity
shows that the aggregate commutator norm is the maximum of the incoming and
outgoing blocks, so the appropriate one-sided lemma applies in every case.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

/-- Orientation-free one-sided concentration for any subset cut. -/
theorem exists_cell_concentration_of_cut
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (hcpos : 0 < ‖recordSubsetProjectorCommutatorCLM D U S‖)
    (hehalf :
      subsetProjectorCommutatorOpNormSq D U S -
          ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2 ≤
        ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2 / 2) :
    ∃ c ∈ S,
      subsetProjectorCommutatorOpNormSq D U S -
          incomingWitnessP D U c ≤
        2 * (subsetProjectorCommutatorOpNormSq D U S -
          ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) +
        18 * (subsetProjectorCommutatorOpNormSq D U S -
          ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) /
          (‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2 -
            (subsetProjectorCommutatorOpNormSq D U S -
              ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2)) := by
  have hblock :=
    recordSubsetProjectorCommutatorCLM_opNorm_eq_max_cross D U S
  rcases le_total
      ‖recordSubsetOutgoingCLM D U S‖
      ‖recordSubsetIncomingCLM D U S‖ with hout_in | hin_out
  · have hmax :
        ‖recordSubsetIncomingCLM D U S‖ =
          ‖recordSubsetProjectorCommutatorCLM D U S‖ := by
      rw [hblock, max_eq_left hout_in]
    exact exists_cell_concentration_of_incoming_max
      D U S hmax hcpos hehalf
  · have hmax :
        ‖recordSubsetOutgoingCLM D U S‖ =
          ‖recordSubsetProjectorCommutatorCLM D U S‖ := by
      rw [hblock, max_eq_right hin_out]
    exact exists_cell_concentration_of_outgoing_max
      D U S hmax hcpos hehalf

end
end EverettianDecoherence.Approximation

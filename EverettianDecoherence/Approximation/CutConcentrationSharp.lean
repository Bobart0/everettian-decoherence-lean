import EverettianDecoherence.Approximation.IncomingCutConcentrationSharp
import EverettianDecoherence.Approximation.OutgoingCutConcentrationSharp

/-!
**FR.** Concentration unilatérale v12 sans choix d'orientation. La norme du
commutateur agrégé est réalisée par l'un des deux blocs croisés et la constante
9 s'applique dans les deux cas.

**EN.** Orientation-free v12 one-sided concentration. The aggregate
commutator norm is attained by one of the two cross blocks, and the constant 9
applies in either case.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

theorem exists_cell_concentration_of_cut_9
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
        9 * (subsetProjectorCommutatorOpNormSq D U S -
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
    exact exists_cell_concentration_of_incoming_max_9
      D U S hmax hcpos hehalf
  · have hmax :
        ‖recordSubsetOutgoingCLM D U S‖ =
          ‖recordSubsetProjectorCommutatorCLM D U S‖ := by
      rw [hblock, max_eq_right hin_out]
    exact exists_cell_concentration_of_outgoing_max_9
      D U S hmax hcpos hehalf

end
end EverettianDecoherence.Approximation

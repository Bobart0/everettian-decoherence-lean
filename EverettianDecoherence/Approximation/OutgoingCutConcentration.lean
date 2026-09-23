import EverettianDecoherence.Approximation.IncomingCutConcentration
import EverettianDecoherence.Approximation.UnitaryInverseSymmetry

/-!
**FR.** Version sortante du lemme de concentration unilatérale. Elle est
obtenue sans dupliquer la preuve analytique : on applique le lemme entrant à
U⁻¹ et on transporte toutes les normes par la symétrie d'adjoint.

**EN.** Outgoing version of the one-sided concentration lemma. No analytic
proof is duplicated: the incoming lemma is applied to U⁻¹ and all norms are
transported by adjoint symmetry.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

theorem exists_cell_concentration_of_outgoing_max
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (hmax :
      ‖recordSubsetOutgoingCLM D U S‖ =
        ‖recordSubsetProjectorCommutatorCLM D U S‖)
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
  have hmax' :
      ‖recordSubsetIncomingCLM D U.symm S‖ =
        ‖recordSubsetProjectorCommutatorCLM D U.symm S‖ := by
    calc
      ‖recordSubsetIncomingCLM D U.symm S‖ =
          ‖recordSubsetOutgoingCLM D U S‖ :=
        (recordSubsetOutgoingCLM_opNorm_eq_incoming_symm D U S).symm
      _ = ‖recordSubsetProjectorCommutatorCLM D U S‖ := hmax
      _ = ‖recordSubsetProjectorCommutatorCLM D U.symm S‖ :=
        (recordSubsetProjectorCommutatorCLM_opNorm_symm D U S).symm
  have hcpos' :
      0 < ‖recordSubsetProjectorCommutatorCLM D U.symm S‖ := by
    rw [recordSubsetProjectorCommutatorCLM_opNorm_symm D U S]
    exact hcpos
  have hehalf' :
      subsetProjectorCommutatorOpNormSq D U.symm S -
          ‖recordSubsetProjectorCommutatorCLM D U.symm S‖ ^ 2 ≤
        ‖recordSubsetProjectorCommutatorCLM D U.symm S‖ ^ 2 / 2 := by
    rw [subsetProjectorCommutatorOpNormSq_symm D U S,
      recordSubsetProjectorCommutatorCLM_opNorm_symm D U S]
    exact hehalf
  obtain ⟨c, hc, hbound⟩ :=
    exists_cell_concentration_of_incoming_max
      D U.symm S hmax' hcpos' hehalf'
  refine ⟨c, hc, ?_⟩
  simpa [incomingWitnessP,
    perspectiveProjectorCommutatorOpNormProfile_symm D U c,
    subsetProjectorCommutatorOpNormSq_symm D U S,
    recordSubsetProjectorCommutatorCLM_opNorm_symm D U S] using hbound

end
end EverettianDecoherence.Approximation

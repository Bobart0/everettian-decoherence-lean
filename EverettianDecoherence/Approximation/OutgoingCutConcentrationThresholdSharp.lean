import EverettianDecoherence.Approximation.IncomingCutConcentrationThresholdSharp
import EverettianDecoherence.Approximation.UnitaryInverseSymmetry

/-!
**FR.** Version sortante sharp du lemme de cut à seuil variable, obtenue par
symétrie unitaire.

**EN.** Sharp outgoing version of the variable-threshold cut lemma, obtained
by unitary symmetry.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

theorem exists_cell_concentration_of_outgoing_max_threshold_sharp
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (β t L Kbar : ℝ)
    (hβ0 : 0 < β) (hβone : β < 1) (ht : 0 < t)
    (hmax :
      ‖recordSubsetOutgoingCLM D U S‖ =
        ‖recordSubsetProjectorCommutatorCLM D U S‖)
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
            (1 - β)) ^ 2 ≤ Kbar) :
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
  have hL' :
      L ≤ subsetProjectorCommutatorOpNormSq D U.symm S -
        (subsetProjectorCommutatorOpNormSq D U.symm S -
          ‖recordSubsetProjectorCommutatorCLM D U.symm S‖ ^ 2) / β := by
    rw [subsetProjectorCommutatorOpNormSq_symm D U S,
      recordSubsetProjectorCommutatorCLM_opNorm_symm D U S]
    exact hL
  have hKcap' :
      4 * (1 + t) *
          ((subsetProjectorCommutatorOpNormSq D U.symm S -
            ‖recordSubsetProjectorCommutatorCLM D U.symm S‖ ^ 2) /
            (1 - β)) +
        (1 + 1 / t) *
          ((subsetProjectorCommutatorOpNormSq D U.symm S -
            ‖recordSubsetProjectorCommutatorCLM D U.symm S‖ ^ 2) /
            (1 - β)) ^ 2 ≤ Kbar := by
    rw [subsetProjectorCommutatorOpNormSq_symm D U S,
      recordSubsetProjectorCommutatorCLM_opNorm_symm D U S]
    exact hKcap
  obtain ⟨c, hc, hbound⟩ :=
    exists_cell_concentration_of_incoming_max_threshold_sharp
      D U.symm S β t L Kbar hβ0 hβone ht hmax' hcpos'
      hLpos hL' hKbar0 hKbarlt hKcap'
  refine ⟨c, hc, ?_⟩
  simpa [incomingWitnessP,
    perspectiveProjectorCommutatorOpNormProfile_symm D U c,
    subsetProjectorCommutatorOpNormSq_symm D U S,
    recordSubsetProjectorCommutatorCLM_opNorm_symm D U S] using hbound

end
end EverettianDecoherence.Approximation

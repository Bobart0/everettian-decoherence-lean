import EverettianDecoherence.Approximation.CutConcentrationSharp
import EverettianDecoherence.Approximation.SubsetCommutatorOpNormBounds

/-!
**FR.** Concentration bilatérale v12. Pour
E = delta^2 - 2 C^2, deux cellules situées de part et d'autre du cut capturent
le budget avec
  tail <= 2 E + 9 E / (C^2 - E).

**EN.** v12 bilateral cut concentration. For
E = delta^2 - 2 C^2, two cells on opposite sides of the cut capture the
budget with
  tail <= 2 E + 9 E / (C^2 - E).
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

theorem exists_two_cell_concentration_of_cut_9
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (hcpos : 0 < ‖recordSubsetProjectorCommutatorCLM D U S‖)
    (hEhalf :
      operatorNormProjectorCommutatorL2 D U ^ 2 -
          2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2 ≤
        ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2 / 2) :
    ∃ i ∈ S, ∃ j ∈ Sᶜ,
      operatorNormProjectorCommutatorL2 D U ^ 2 -
          incomingWitnessP D U i - incomingWitnessP D U j ≤
        2 * (operatorNormProjectorCommutatorL2 D U ^ 2 -
          2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) +
        9 * (operatorNormProjectorCommutatorL2 D U ^ 2 -
          2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) /
          (‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2 -
            (operatorNormProjectorCommutatorL2 D U ^ 2 -
              2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2)) := by
  let C : ℝ := ‖recordSubsetProjectorCommutatorCLM D U S‖
  let A : ℝ := operatorNormProjectorCommutatorL2 D U ^ 2
  let AS : ℝ := subsetProjectorCommutatorOpNormSq D U S
  let AT : ℝ := subsetProjectorCommutatorOpNormSq D U Sᶜ
  let eS : ℝ := AS - C ^ 2
  let eT : ℝ := AT - C ^ 2
  let E : ℝ := A - 2 * C ^ 2
  let d : ℝ := C ^ 2 - E
  have hpart : AS + AT = A := by
    simpa [AS, AT, A] using
      subsetProjectorCommutatorOpNormSq_add_compl D U S
  have hcS : C ^ 2 ≤ AS := by
    simpa [C, AS] using
      recordSubsetProjectorCommutatorCLM_opNorm_sq_le_subsetSq D U S
  have hcT : C ^ 2 ≤ AT := by
    simpa [C, AT] using
      recordSubsetProjectorCommutatorCLM_opNorm_sq_le_complSq D U S
  have heS0 : 0 ≤ eS := by
    dsimp [eS]
    linarith
  have heT0 : 0 ≤ eT := by
    dsimp [eT]
    linarith
  have hsumE : eS + eT = E := by
    dsimp [eS, eT, E]
    linarith
  have hE0 : 0 ≤ E := by
    rw [← hsumE]
    positivity
  have heS_E : eS ≤ E := by
    rw [← hsumE]
    linarith
  have heT_E : eT ≤ E := by
    rw [← hsumE]
    linarith
  have hEhalf' : E ≤ C ^ 2 / 2 := by
    simpa [E, A, C] using hEhalf
  have heShalf : eS ≤ C ^ 2 / 2 := heS_E.trans hEhalf'
  have heThalf : eT ≤ C ^ 2 / 2 := heT_E.trans hEhalf'
  have hcpos' : 0 < C := by simpa [C] using hcpos
  have hdpos : 0 < d := by
    dsimp [d]
    nlinarith [sq_pos_of_pos hcpos']
  have hScut :
      AS - C ^ 2 ≤ C ^ 2 / 2 := by
    simpa [eS] using heShalf
  obtain ⟨i, hiS, hi⟩ :=
    exists_cell_concentration_of_cut_9 D U S hcpos
      (by simpa [AS, C] using hScut)
  have hcposT :
      0 < ‖recordSubsetProjectorCommutatorCLM D U Sᶜ‖ := by
    rw [recordSubsetProjectorCommutatorCLM_opNorm_compl D U S]
    exact hcpos
  have hTcut :
      subsetProjectorCommutatorOpNormSq D U Sᶜ -
          ‖recordSubsetProjectorCommutatorCLM D U Sᶜ‖ ^ 2 ≤
        ‖recordSubsetProjectorCommutatorCLM D U Sᶜ‖ ^ 2 / 2 := by
    rw [recordSubsetProjectorCommutatorCLM_opNorm_compl D U S]
    simpa [AT, C, eT] using heThalf
  obtain ⟨j, hjT, hj⟩ :=
    exists_cell_concentration_of_cut_9 D U Sᶜ hcposT hTcut
  have hi' :
      AS - incomingWitnessP D U i ≤
        2 * eS + 9 * eS / (C ^ 2 - eS) := by
    simpa [AS, C, eS] using hi
  have hj' :
      AT - incomingWitnessP D U j ≤
        2 * eT + 9 * eT / (C ^ 2 - eT) := by
    simpa [AT, C, eT,
      recordSubsetProjectorCommutatorCLM_opNorm_compl D U S] using hj
  have hd_le_S : d ≤ C ^ 2 - eS := by
    dsimp [d]
    linarith
  have hd_le_T : d ≤ C ^ 2 - eT := by
    dsimp [d]
    linarith
  have hfracS :
      eS / (C ^ 2 - eS) ≤ eS / d :=
    div_le_div_of_nonneg_left heS0 hdpos hd_le_S
  have hfracT :
      eT / (C ^ 2 - eT) ≤ eT / d :=
    div_le_div_of_nonneg_left heT0 hdpos hd_le_T
  have hfrac :
      eS / (C ^ 2 - eS) + eT / (C ^ 2 - eT) ≤ E / d := by
    calc
      eS / (C ^ 2 - eS) + eT / (C ^ 2 - eT) ≤
          eS / d + eT / d := add_le_add hfracS hfracT
      _ = (eS + eT) / d := by ring
      _ = E / d := by rw [hsumE]
  have hsum :
      (AS - incomingWitnessP D U i) +
          (AT - incomingWitnessP D U j) ≤
        2 * E + 9 * E / d := by
    calc
      (AS - incomingWitnessP D U i) +
          (AT - incomingWitnessP D U j) ≤
        (2 * eS + 9 * eS / (C ^ 2 - eS)) +
          (2 * eT + 9 * eT / (C ^ 2 - eT)) :=
        add_le_add hi' hj'
      _ = 2 * (eS + eT) +
          9 * (eS / (C ^ 2 - eS) + eT / (C ^ 2 - eT)) := by ring
      _ ≤ 2 * E + 9 * (E / d) := by
        rw [hsumE]
        gcongr
      _ = 2 * E + 9 * E / d := by ring
  refine ⟨i, hiS, j, hjT, ?_⟩
  have hbudget :
      A - incomingWitnessP D U i - incomingWitnessP D U j =
        (AS - incomingWitnessP D U i) +
          (AT - incomingWitnessP D U j) := by
    linarith
  rw [show operatorNormProjectorCommutatorL2 D U ^ 2 = A by rfl]
  rw [hbudget]
  simpa [E, d, A, C] using hsum

end
end EverettianDecoherence.Approximation

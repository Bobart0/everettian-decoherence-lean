import EverettianDecoherence.Approximation.IncomingCutConcentration
import EverettianDecoherence.Approximation.IncomingWitnessConcentrationSharp

/-!
**FR.** Version v12 du lemme de concentration unilatérale pour le bloc
entrant. Le terme de Gram est réduit de 18 à 9 :
  A_S - p_i <= 2 e + 9 e / (C^2 - e).

**EN.** v12 one-sided concentration lemma for the incoming block. The Gram
term is reduced from 18 to 9:
  A_S - p_i <= 2 e + 9 e / (C^2 - e).
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

theorem exists_cell_concentration_of_incoming_max_9
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (hmax :
      ‖recordSubsetIncomingCLM D U S‖ =
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
        9 * (subsetProjectorCommutatorOpNormSq D U S -
          ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) /
          (‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2 -
            (subsetProjectorCommutatorOpNormSq D U S -
              ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2)) := by
  let C : ℝ := ‖recordSubsetProjectorCommutatorCLM D U S‖
  let A : ℝ := subsetProjectorCommutatorOpNormSq D U S
  let e : ℝ := A - C ^ 2
  let L : ℝ := C ^ 2 - e
  have hinpos : 0 < ‖recordSubsetIncomingCLM D U S‖ := by
    rw [hmax]
    exact hcpos
  obtain ⟨v, hv, hvcompl, hvnorm⟩ :=
    exists_unit_complWitness_norm_incoming D U S hinpos
  have heq :
      (∑ c ∈ S, incomingWitnessAlpha D U c v) = e := by
    rw [sum_incomingWitnessAlpha_eq_budget_sub_incoming
      D U S v hvcompl]
    dsimp [e, A, C]
    rw [hvnorm, hmax]
  have he0 : 0 ≤ e := by
    rw [← heq]
    exact Finset.sum_nonneg fun c hc =>
      incomingWitnessAlpha_nonneg_of_mem D U S c hc v hv hvcompl
  have hCle : C ≤ 1 := by
    dsimp [C]
    rw [← hmax]
    exact recordSubsetIncomingCLM_opNorm_le_one D U S
  have hC0 : 0 ≤ C := norm_nonneg _
  have hehalf' : e ≤ C ^ 2 / 2 := by
    simpa [e, A, C] using hehalf
  have ehalf : e ≤ 1 / 2 := by
    nlinarith
  have hLpos : 0 < L := by
    dsimp [L]
    nlinarith
  have hmass0 :=
    activeGood_incomingWitnessP_mass_lower
      D U S v hv hvcompl
  have hmass :
      L ≤ ∑ c ∈ incomingWitnessActiveGoodCells D U S v,
        incomingWitnessP D U c := by
    dsimp [L, e, A, C]
    rw [heq] at hmass0
    nlinarith
  obtain ⟨i, hitail⟩ :=
    exists_dominant_activeGood_incomingWitness_9
      D U S v hv hvcompl L
      (by simpa [heq] using ehalf)
      hmass hLpos
  have hiActive : i.1 ∈ incomingWitnessActiveGoodCells D U S v := i.2
  have hiS :
      i.1 ∈ S :=
    ((mem_incomingWitnessActiveGoodCells D U S v i.1).mp hiActive).1
  have hbad :=
    sum_bad_incomingWitnessP_le_two_mul_alpha_sum
      D U S v hv hvcompl
  have hbad' :
      (∑ c ∈ incomingWitnessBadCells D U S v,
        incomingWitnessP D U c) ≤ 2 * e := by
    simpa [heq] using hbad
  have hsplit :=
    good_add_bad_incomingWitnessP_eq_budget D U S v
  have hactiveGood :=
    sum_activeGood_incomingWitnessP_eq_good D U S v
  have hidecomp :
      (∑ j : ↥(incomingWitnessActiveGoodCells D U S v),
          incomingWitnessP D U j.1) =
        incomingWitnessP D U i.1 +
          ∑ j ∈ Finset.univ.erase i, incomingWitnessP D U j.1 := by
    have hiuniv :
        i ∈ (Finset.univ :
          Finset ↥(incomingWitnessActiveGoodCells D U S v)) :=
      Finset.mem_univ i
    have hsum :=
      Finset.sum_erase_add (Finset.univ :
        Finset ↥(incomingWitnessActiveGoodCells D U S v))
        (fun j => incomingWitnessP D U j.1) hiuniv
    simpa [add_comm] using hsum.symm
  have hactiveGood' :
      (∑ c ∈ incomingWitnessGoodCells D U S v,
          incomingWitnessP D U c) =
        incomingWitnessP D U i.1 +
          ∑ j ∈ Finset.univ.erase i, incomingWitnessP D U j.1 := by
    rw [← hactiveGood]
    rw [← Finset.sum_attach, Finset.attach_eq_univ]
    exact hidecomp
  have hbudgetDecomp :
      A - incomingWitnessP D U i.1 =
        (∑ c ∈ incomingWitnessBadCells D U S v,
            incomingWitnessP D U c) +
          (∑ j ∈ Finset.univ.erase i,
            incomingWitnessP D U j.1) := by
    dsimp [A]
    rw [← hsplit, hactiveGood']
    simp only [Finset.attach_eq_univ]
    abel
  refine ⟨i.1, hiS, ?_⟩
  rw [show subsetProjectorCommutatorOpNormSq D U S = A by rfl]
  rw [hbudgetDecomp]
  have htail :
      (∑ j ∈ Finset.univ.erase i,
        incomingWitnessP D U j.1) ≤ 9 * e / L := by
    simpa [heq] using hitail
  have hsumBound :
      (∑ c ∈ incomingWitnessBadCells D U S v,
          incomingWitnessP D U c) +
        (∑ j ∈ Finset.univ.erase i,
          incomingWitnessP D U j.1) ≤
        2 * e + 9 * e / L :=
    add_le_add hbad' htail
  simpa [e, L, A, C] using hsumBound

end
end EverettianDecoherence.Approximation

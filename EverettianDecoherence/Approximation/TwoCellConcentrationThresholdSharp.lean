import EverettianDecoherence.Approximation.CutConcentrationThresholdSharp
import EverettianDecoherence.Approximation.SubsetCommutatorOpNormBounds

/-!
**FR.** Concentration bilatérale sharp à seuil variable. Avec
E = A - 2 C^2, L = C^2 - E/beta et
K = 4(1+t) E/(1-beta) + (1+1/t)(E/(1-beta))^2,
l'hypothèse K < L^2 permet de préserver le facteur deux de la concentration
à petit spread sur les deux côtés du cut.

**EN.** Sharp bilateral variable-threshold concentration. With
E = A - 2 C^2, L = C^2 - E/beta and
K = 4(1+t) E/(1-beta) + (1+1/t)(E/(1-beta))^2,
the condition K < L^2 preserves the small-spread factor two on both sides of
the cut.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

theorem exists_two_cell_concentration_of_cut_threshold_sharp
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (β t : ℝ)
    (hβ0 : 0 < β) (hβone : β < 1) (ht : 0 < t)
    (hcpos : 0 < ‖recordSubsetProjectorCommutatorCLM D U S‖)
    (hLpos :
      0 <
        ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2 -
          (operatorNormProjectorCommutatorL2 D U ^ 2 -
            2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) / β)
    (hKlt :
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
            2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) / β) ^ 2) :
    ∃ i ∈ S, ∃ j ∈ Sᶜ,
      operatorNormProjectorCommutatorL2 D U ^ 2 -
          incomingWitnessP D U i - incomingWitnessP D U j ≤
        (operatorNormProjectorCommutatorL2 D U ^ 2 -
          2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) / β +
        (4 * (1 + t) *
            ((operatorNormProjectorCommutatorL2 D U ^ 2 -
              2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) /
              (1 - β)) +
          (1 + 1 / t) *
            ((operatorNormProjectorCommutatorL2 D U ^ 2 -
              2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) /
              (1 - β)) ^ 2) /
          (2 *
            ((‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2 -
              (operatorNormProjectorCommutatorL2 D U ^ 2 -
                2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) / β) -
              (4 * (1 + t) *
                  ((operatorNormProjectorCommutatorL2 D U ^ 2 -
                    2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) /
                    (1 - β)) +
                (1 + 1 / t) *
                  ((operatorNormProjectorCommutatorL2 D U ^ 2 -
                    2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) /
                    (1 - β)) ^ 2) /
                (‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2 -
                  (operatorNormProjectorCommutatorL2 D U ^ 2 -
                    2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) /
                    β))) := by
  let C : ℝ := ‖recordSubsetProjectorCommutatorCLM D U S‖
  let A : ℝ := operatorNormProjectorCommutatorL2 D U ^ 2
  let AS : ℝ := subsetProjectorCommutatorOpNormSq D U S
  let AT : ℝ := subsetProjectorCommutatorOpNormSq D U Sᶜ
  let eS : ℝ := AS - C ^ 2
  let eT : ℝ := AT - C ^ 2
  let E : ℝ := A - 2 * C ^ 2
  let L : ℝ := C ^ 2 - E / β
  let qS : ℝ := eS / (1 - β)
  let qT : ℝ := eT / (1 - β)
  let qE : ℝ := E / (1 - β)
  let kS : ℝ := 4 * (1 + t) * qS + (1 + 1 / t) * qS ^ 2
  let kT : ℝ := 4 * (1 + t) * qT + (1 + 1 / t) * qT ^ 2
  let kE : ℝ := 4 * (1 + t) * qE + (1 + 1 / t) * qE ^ 2
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
  have hden : 0 < 1 - β := sub_pos.mpr hβone
  have hqS0 : 0 ≤ qS := by
    dsimp [qS]
    positivity
  have hqT0 : 0 ≤ qT := by
    dsimp [qT]
    positivity
  have hqE0 : 0 ≤ qE := by
    dsimp [qE]
    positivity
  have hqS_E : qS ≤ qE :=
    div_le_div_of_nonneg_right heS_E hden.le
  have hqT_E : qT ≤ qE :=
    div_le_div_of_nonneg_right heT_E hden.le
  have hqSsq : qS ^ 2 ≤ qE ^ 2 :=
    (sq_le_sq₀ hqS0 hqE0).2 hqS_E
  have hqTsq : qT ^ 2 ≤ qE ^ 2 :=
    (sq_le_sq₀ hqT0 hqE0).2 hqT_E
  have hqsum : qS + qT = qE := by
    dsimp [qS, qT, qE]
    rw [← add_div, hsumE]
  have hsqsum : qS ^ 2 + qT ^ 2 ≤ qE ^ 2 := by
    rw [← hqsum]
    nlinarith [mul_nonneg hqS0 hqT0]
  have hcoef1 : 0 ≤ 4 * (1 + t) := by positivity
  have hcoef2 : 0 ≤ 1 + 1 / t := by
    have : 0 < 1 / t := one_div_pos.mpr ht
    linarith
  have hkS0 : 0 ≤ kS := by
    dsimp [kS]
    positivity
  have hkT0 : 0 ≤ kT := by
    dsimp [kT]
    positivity
  have hkE0 : 0 ≤ kE := by
    dsimp [kE]
    positivity
  have hkS_E : kS ≤ kE := by
    dsimp [kS, kE]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hqS_E hcoef1)
      (mul_le_mul_of_nonneg_left hqSsq hcoef2)
  have hkT_E : kT ≤ kE := by
    dsimp [kT, kE]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hqT_E hcoef1)
      (mul_le_mul_of_nonneg_left hqTsq hcoef2)
  have hkSum : kS + kT ≤ kE := by
    dsimp [kS, kT, kE]
    calc
      4 * (1 + t) * qS + (1 + 1 / t) * qS ^ 2 +
          (4 * (1 + t) * qT + (1 + 1 / t) * qT ^ 2) =
        4 * (1 + t) * (qS + qT) +
          (1 + 1 / t) * (qS ^ 2 + qT ^ 2) := by ring
      _ ≤ 4 * (1 + t) * qE +
          (1 + 1 / t) * qE ^ 2 := by
        rw [hqsum]
        gcongr
  have hLpos' : 0 < L := by
    simpa [L, E, A, C] using hLpos
  have hKlt' : kE < L ^ 2 := by
    simpa [kE, qE, L, E, A, C] using hKlt
  have hL_S : L ≤ AS - eS / β := by
    have hrest : 0 ≤ (E - eS) / β :=
      div_nonneg (sub_nonneg.mpr heS_E) hβ0.le
    dsimp [L, eS]
    nlinarith
  have hL_T : L ≤ AT - eT / β := by
    have hrest : 0 ≤ (E - eT) / β :=
      div_nonneg (sub_nonneg.mpr heT_E) hβ0.le
    dsimp [L, eT]
    nlinarith
  obtain ⟨i, hiS, hi⟩ :=
    exists_cell_concentration_of_cut_threshold_sharp
      D U S β t L kE hβ0 hβone ht hcpos hLpos'
      (by simpa [AS, C, eS] using hL_S)
      hkE0 hKlt'
      (by simpa [eS, qS, kS, AS, C] using hkS_E)
  have hcposT :
      0 < ‖recordSubsetProjectorCommutatorCLM D U Sᶜ‖ := by
    rw [recordSubsetProjectorCommutatorCLM_opNorm_compl D U S]
    exact hcpos
  obtain ⟨j, hjT, hj⟩ :=
    exists_cell_concentration_of_cut_threshold_sharp
      D U Sᶜ β t L kE hβ0 hβone ht hcposT hLpos'
      (by
        rw [recordSubsetProjectorCommutatorCLM_opNorm_compl D U S]
        simpa [AT, C, eT] using hL_T)
      hkE0 hKlt'
      (by
        rw [recordSubsetProjectorCommutatorCLM_opNorm_compl D U S]
        simpa [eT, qT, kT, AT, C] using hkT_E)
  have hbasepos : 0 < L - kE / L := by
    apply (sub_pos_iff_lt).2
    apply (div_lt_iff₀ hLpos').2
    simpa [pow_two, mul_comm] using hKlt'
  have hdenSharp : 0 < 2 * (L - kE / L) := by positivity
  have hi' :
      AS - incomingWitnessP D U i ≤
        eS / β + kS / (2 * (L - kE / L)) := by
    simpa [AS, C, eS, qS, kS] using hi
  have hj' :
      AT - incomingWitnessP D U j ≤
        eT / β + kT / (2 * (L - kE / L)) := by
    simpa [AT, C, eT, qT, kT,
      recordSubsetProjectorCommutatorCLM_opNorm_compl D U S] using hj
  have hkdiv :
      kS / (2 * (L - kE / L)) +
          kT / (2 * (L - kE / L)) ≤
        kE / (2 * (L - kE / L)) := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right hkSum hdenSharp.le
  have hsum :
      (AS - incomingWitnessP D U i) +
          (AT - incomingWitnessP D U j) ≤
        E / β + kE / (2 * (L - kE / L)) := by
    calc
      (AS - incomingWitnessP D U i) +
          (AT - incomingWitnessP D U j) ≤
        (eS / β + kS / (2 * (L - kE / L))) +
          (eT / β + kT / (2 * (L - kE / L))) :=
        add_le_add hi' hj'
      _ = (eS + eT) / β +
          (kS / (2 * (L - kE / L)) +
            kT / (2 * (L - kE / L))) := by ring
      _ ≤ E / β + kE / (2 * (L - kE / L)) := by
        rw [hsumE]
        exact add_le_add_left hkdiv _
  refine ⟨i, hiS, j, hjT, ?_⟩
  have hbudget :
      A - incomingWitnessP D U i - incomingWitnessP D U j =
        (AS - incomingWitnessP D U i) +
          (AT - incomingWitnessP D U j) := by
    linarith
  rw [show operatorNormProjectorCommutatorL2 D U ^ 2 = A by rfl]
  rw [hbudget]
  simpa [E, L, qE, kE, A, C] using hsum

end
end EverettianDecoherence.Approximation

import EverettianDecoherence.Approximation.CutConcentrationThreshold
import EverettianDecoherence.Approximation.SubsetCommutatorOpNormBounds

/-!
**FR.** Concentration bilatérale à seuil variable avec dénominateur commun.
Si E = A - 2 g et L = g - E/beta est positif, deux cellules de part et
d'autre du cut laissent une queue contrôlée explicitement par E, beta et t.

**EN.** Variable-threshold bilateral concentration with a common denominator.
If E = A - 2 g and L = g - E/beta is positive, two cells on opposite sides
of the cut leave a tail explicitly controlled by E, beta, and t.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

theorem exists_two_cell_concentration_of_cut_threshold
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
            2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) / β) :
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
          (‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2 -
            (operatorNormProjectorCommutatorL2 D U ^ 2 -
              2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) / β) := by
  let C : ℝ := ‖recordSubsetProjectorCommutatorCLM D U S‖
  let A : ℝ := operatorNormProjectorCommutatorL2 D U ^ 2
  let AS : ℝ := subsetProjectorCommutatorOpNormSq D U S
  let AT : ℝ := subsetProjectorCommutatorOpNormSq D U Sᶜ
  let eS : ℝ := AS - C ^ 2
  let eT : ℝ := AT - C ^ 2
  let E : ℝ := A - 2 * C ^ 2
  let L : ℝ := C ^ 2 - E / β
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
  have hLpos' : 0 < L := by
    simpa [L, E, A, C] using hLpos
  have hL_S : L ≤ AS - eS / β := by
    have hrest : 0 ≤ (E - eS) / β :=
      div_nonneg (sub_nonneg.mpr heS_E) hβ0.le
    have hdiff :
        AS - eS / β - L = eS + (E - eS) / β := by
      dsimp [L, eS]
      ring
    have hnon : 0 ≤ AS - eS / β - L := by
      rw [hdiff]
      exact add_nonneg heS0 hrest
    linarith
  have hL_T : L ≤ AT - eT / β := by
    have hrest : 0 ≤ (E - eT) / β :=
      div_nonneg (sub_nonneg.mpr heT_E) hβ0.le
    have hdiff :
        AT - eT / β - L = eT + (E - eT) / β := by
      dsimp [L, eT]
      ring
    have hnon : 0 ≤ AT - eT / β - L := by
      rw [hdiff]
      exact add_nonneg heT0 hrest
    linarith
  obtain ⟨i, hiS, hi⟩ :=
    exists_cell_concentration_of_cut_threshold
      D U S β t L hβ0 hβone ht hcpos hLpos'
      (by simpa [AS, C, eS] using hL_S)
  have hcposT :
      0 < ‖recordSubsetProjectorCommutatorCLM D U Sᶜ‖ := by
    rw [recordSubsetProjectorCommutatorCLM_opNorm_compl D U S]
    exact hcpos
  obtain ⟨j, hjT, hj⟩ :=
    exists_cell_concentration_of_cut_threshold
      D U Sᶜ β t L hβ0 hβone ht hcposT hLpos'
      (by
        rw [recordSubsetProjectorCommutatorCLM_opNorm_compl D U S]
        simpa [AT, C, eT] using hL_T)
  let qS : ℝ := eS / (1 - β)
  let qT : ℝ := eT / (1 - β)
  let qE : ℝ := E / (1 - β)
  let kS : ℝ := 4 * (1 + t) * qS + (1 + 1 / t) * qS ^ 2
  let kT : ℝ := 4 * (1 + t) * qT + (1 + 1 / t) * qT ^ 2
  let kE : ℝ := 4 * (1 + t) * qE + (1 + 1 / t) * qE ^ 2
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
  have hqsum : qS + qT = qE := by
    dsimp [qS, qT, qE]
    rw [← add_div]
    rw [hsumE]
  have hsqsum : qS ^ 2 + qT ^ 2 ≤ qE ^ 2 := by
    rw [← hqsum]
    nlinarith [mul_nonneg hqS0 hqT0]
  have hcoef1 : 0 ≤ 4 * (1 + t) := by positivity
  have hcoef2 : 0 ≤ 1 + 1 / t := by
    have : 0 < 1 / t := one_div_pos.mpr ht
    linarith
  have hk : kS + kT ≤ kE := by
    dsimp [kS, kT, kE]
    calc
      4 * (1 + t) * qS + (1 + 1 / t) * qS ^ 2 +
          (4 * (1 + t) * qT + (1 + 1 / t) * qT ^ 2)
          =
        4 * (1 + t) * (qS + qT) +
          (1 + 1 / t) * (qS ^ 2 + qT ^ 2) := by ring
      _ ≤
        4 * (1 + t) * qE +
          (1 + 1 / t) * qE ^ 2 := by
        rw [hqsum]
        gcongr
  have hi' :
      AS - incomingWitnessP D U i ≤ eS / β + kS / L := by
    simpa [AS, C, eS, qS, kS] using hi
  have hj' :
      AT - incomingWitnessP D U j ≤ eT / β + kT / L := by
    simpa [AT, C, eT, qT, kT,
      recordSubsetProjectorCommutatorCLM_opNorm_compl D U S] using hj
  have hL0 : 0 ≤ L := hLpos'.le
  have hkdiv : kS / L + kT / L ≤ kE / L := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right hk hL0
  have hsum :
      (AS - incomingWitnessP D U i) +
          (AT - incomingWitnessP D U j) ≤
        E / β + kE / L := by
    calc
      (AS - incomingWitnessP D U i) +
          (AT - incomingWitnessP D U j) ≤
        (eS / β + kS / L) + (eT / β + kT / L) :=
          add_le_add hi' hj'
      _ = (eS + eT) / β + (kS / L + kT / L) := by ring
      _ ≤ E / β + kE / L := by
        rw [hsumE]
        exact add_le_add (le_refl _) hkdiv
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

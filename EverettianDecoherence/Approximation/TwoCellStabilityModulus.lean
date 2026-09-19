import EverettianDecoherence.Approximation.TwoCellConcentration

/-!
**FR.** Modulus quantitatif explicite extrait du théorème bilatéral sur un cut.
Si le déficit quadratique du cut
  E = delta^2 - 2 C^2
est au plus eta * delta^2, avec eta <= 1/5, alors deux cellules distinctes
capturent presque tout le budget global. La première forme ne fait pas encore
intervenir de seuil d'échelle rho.

**EN.** Explicit quantitative modulus extracted from the bilateral cut theorem.
If the quadratic cut deficit
  E = delta^2 - 2 C^2
is at most eta * delta^2, with eta <= 1/5, then two distinct cells capture
almost all of the global budget. The first form does not yet use a scale
threshold rho.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

/-- Eta-form of bilateral two-cell concentration for a fixed cut. -/
theorem exists_two_cell_concentration_of_cut_eta
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (η : ℝ)
    (hη0 : 0 ≤ η)
    (hηfive : η ≤ 1 / 5)
    (hdelta : 0 < operatorNormProjectorCommutatorL2 D U)
    (hEη :
      operatorNormProjectorCommutatorL2 D U ^ 2 -
          2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2 ≤
        η * operatorNormProjectorCommutatorL2 D U ^ 2) :
    ∃ i ∈ S, ∃ j ∈ Sᶜ,
      operatorNormProjectorCommutatorL2 D U ^ 2 -
          incomingWitnessP D U i - incomingWitnessP D U j ≤
        2 * η * operatorNormProjectorCommutatorL2 D U ^ 2 +
          36 * η / (1 - 3 * η) := by
  let A : ℝ := operatorNormProjectorCommutatorL2 D U ^ 2
  let C : ℝ := ‖recordSubsetProjectorCommutatorCLM D U S‖
  let AS : ℝ := subsetProjectorCommutatorOpNormSq D U S
  let AT : ℝ := subsetProjectorCommutatorOpNormSq D U Sᶜ
  let E : ℝ := A - 2 * C ^ 2
  let d : ℝ := C ^ 2 - E
  have hApos : 0 < A := by
    dsimp [A]
    exact sq_pos_of_pos hdelta
  have hA0 : 0 ≤ A := hApos.le
  have hpart : AS + AT = A := by
    simpa [AS, AT, A] using
      subsetProjectorCommutatorOpNormSq_add_compl D U S
  have hcS : C ^ 2 ≤ AS := by
    simpa [C, AS] using
      recordSubsetProjectorCommutatorCLM_opNorm_sq_le_subsetSq D U S
  have hcT : C ^ 2 ≤ AT := by
    simpa [C, AT] using
      recordSubsetProjectorCommutatorCLM_opNorm_sq_le_complSq D U S
  have hE0 : 0 ≤ E := by
    dsimp [E]
    linarith
  have hEtaA5 : η * A ≤ A / 5 := by
    calc
      η * A ≤ (1 / 5 : ℝ) * A :=
        mul_le_mul_of_nonneg_right hηfive hA0
      _ = A / 5 := by ring
  have hE_A5 : E ≤ A / 5 := by
    apply (show E ≤ η * A by simpa [E, A, C] using hEη).trans
    exact hEtaA5
  have hC2pos : 0 < C ^ 2 := by
    dsimp [E] at hE_A5
    nlinarith
  have hCpos : 0 < C := by
    have hC0 : 0 ≤ C := by
      dsimp [C]
      exact norm_nonneg _
    nlinarith
  have hEhalf : E ≤ C ^ 2 / 2 := by
    dsimp [E] at hE_A5
    nlinarith
  obtain ⟨i, hi, j, hj, htail⟩ :=
    exists_two_cell_concentration_of_cut D U S
      (by simpa [C] using hCpos)
      (by simpa [E, A, C] using hEhalf)
  have hqpos : 0 < 1 - 3 * η := by
    nlinarith
  have hdeneq : d = (A - 3 * E) / 2 := by
    dsimp [d, E]
    ring
  have hElimit : E ≤ η * A := by
    simpa [E, A, C] using hEη
  have hdenlower : ((1 - 3 * η) * A) / 2 ≤ d := by
    rw [hdeneq]
    nlinarith
  have hdenpos : 0 < d := by
    have hprodpos : 0 < (1 - 3 * η) * A :=
      mul_pos hqpos hApos
    nlinarith
  have hnum0 : 0 ≤ η * A := mul_nonneg hη0 hA0
  have hfrac1 : E / d ≤ (η * A) / d :=
    div_le_div_of_nonneg_right hElimit hdenpos.le
  have hlowerpos : 0 < ((1 - 3 * η) * A) / 2 := by
    positivity
  have hfrac2 :
      (η * A) / d ≤
        (η * A) / (((1 - 3 * η) * A) / 2) :=
    div_le_div_of_nonneg_left hnum0 hlowerpos hdenlower
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hqne : 1 - 3 * η ≠ 0 := ne_of_gt hqpos
  have hsimplify :
      (η * A) / (((1 - 3 * η) * A) / 2) =
        2 * η / (1 - 3 * η) := by
    field_simp [hAne, hqne]
    ring
  have hfrac :
      E / d ≤ 2 * η / (1 - 3 * η) := by
    calc
      E / d ≤ (η * A) / d := hfrac1
      _ ≤ (η * A) / (((1 - 3 * η) * A) / 2) := hfrac2
      _ = 2 * η / (1 - 3 * η) := hsimplify
  have hbase :
      A - incomingWitnessP D U i - incomingWitnessP D U j ≤
        2 * E + 18 * E / d := by
    simpa [A, C, E, d] using htail
  have htwoE : 2 * E ≤ 2 * η * A := by
    linarith
  have h18frac :
      18 * E / d ≤ 36 * η / (1 - 3 * η) := by
    have hmul := mul_le_mul_of_nonneg_left hfrac (by norm_num : (0 : ℝ) ≤ 18)
    simpa [mul_div_assoc] using hmul
  refine ⟨i, hi, j, hj, ?_⟩
  change A - incomingWitnessP D U i - incomingWitnessP D U j ≤
    2 * η * A + 36 * η / (1 - 3 * η)
  exact hbase.trans (add_le_add htwoE h18frac)


/-- Scale-sensitive eta-rho form. If the global defect is at least rho > 0,
then the two-cell tail is controlled by a fraction of the global squared
defect. -/
theorem exists_two_cell_concentration_of_cut_eta_rho
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (η ρ : ℝ)
    (hη0 : 0 ≤ η)
    (hηfive : η ≤ 1 / 5)
    (hρpos : 0 < ρ)
    (hρdelta : ρ ≤ operatorNormProjectorCommutatorL2 D U)
    (hEη :
      operatorNormProjectorCommutatorL2 D U ^ 2 -
          2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2 ≤
        η * operatorNormProjectorCommutatorL2 D U ^ 2) :
    ∃ i ∈ S, ∃ j ∈ Sᶜ,
      operatorNormProjectorCommutatorL2 D U ^ 2 -
          incomingWitnessP D U i - incomingWitnessP D U j ≤
        operatorNormProjectorCommutatorL2 D U ^ 2 *
          (2 * η +
            (36 * η / (1 - 3 * η)) / ρ ^ 2) := by
  have hdelta :
      0 < operatorNormProjectorCommutatorL2 D U :=
    lt_of_lt_of_le hρpos hρdelta
  obtain ⟨i, hi, j, hj, htail⟩ :=
    exists_two_cell_concentration_of_cut_eta
      D U S η hη0 hηfive hdelta hEη
  let A : ℝ := operatorNormProjectorCommutatorL2 D U ^ 2
  let K : ℝ := 36 * η / (1 - 3 * η)
  have hδ0 : 0 ≤ operatorNormProjectorCommutatorL2 D U :=
    operatorNormProjectorCommutatorL2_nonneg D U
  have hρ0 : 0 ≤ ρ := hρpos.le
  have hρsq : ρ ^ 2 ≤ A := by
    dsimp [A]
    exact (sq_le_sq₀ hρ0 hδ0).2 hρdelta
  have hρsqpos : 0 < ρ ^ 2 := sq_pos_of_pos hρpos
  have hqpos : 0 < 1 - 3 * η := by
    nlinarith
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact div_nonneg
      (mul_nonneg (by norm_num) hη0) hqpos.le
  have hKrho :
      K ≤ A * (K / ρ ^ 2) := by
    have hcoef0 : 0 ≤ K / ρ ^ 2 :=
      div_nonneg hK0 hρsqpos.le
    calc
      K = ρ ^ 2 * (K / ρ ^ 2) := by
        field_simp [ne_of_gt hρsqpos]
      _ ≤ A * (K / ρ ^ 2) :=
        mul_le_mul_of_nonneg_right hρsq hcoef0
  refine ⟨i, hi, j, hj, ?_⟩
  have hscaled :
      2 * η * A + K ≤
        A * (2 * η + K / ρ ^ 2) := by
    calc
      2 * η * A + K ≤
          2 * η * A + A * (K / ρ ^ 2) :=
        add_le_add_left hKrho _
      _ = A * (2 * η + K / ρ ^ 2) := by ring
  have htail' :
      A - incomingWitnessP D U i - incomingWitnessP D U j ≤
        2 * η * A + K := by
    simpa [A, K] using htail
  exact htail'.trans (by simpa [A, K] using hscaled)


/-- Explicit relative two-cell stability modulus. -/
noncomputable def twoCellStabilityModulus (ρ η : ℝ) : ℝ :=
  2 * η + (36 * η / (1 - 3 * η)) / ρ ^ 2

theorem twoCellStabilityModulus_nonneg
    {ρ η : ℝ} (hρ : 0 < ρ) (hη0 : 0 ≤ η) (hηthird : η < 1 / 3) :
    0 ≤ twoCellStabilityModulus ρ η := by
  unfold twoCellStabilityModulus
  have hq : 0 < 1 - 3 * η := by nlinarith
  positivity

/-- For eta <= 1/6 the exact modulus admits the transparent linear bound
eta * (2 + 72 / rho^2). This exhibits the dimension-free O(eta / rho^2)
scale dependence. -/
theorem twoCellStabilityModulus_le_linear
    {ρ η : ℝ} (hρ : 0 < ρ) (hη0 : 0 ≤ η) (hηsix : η ≤ 1 / 6) :
    twoCellStabilityModulus ρ η ≤
      η * (2 + 72 / ρ ^ 2) := by
  have hq : (1 / 2 : ℝ) ≤ 1 - 3 * η := by
    nlinarith
  have hqpos : 0 < 1 - 3 * η := lt_of_lt_of_le (by norm_num) hq
  have hnum :
      36 * η ≤ 72 * η * (1 - 3 * η) := by
    calc
      36 * η = (72 * η) * (1 / 2 : ℝ) := by ring
      _ ≤ (72 * η) * (1 - 3 * η) :=
        mul_le_mul_of_nonneg_left hq
          (mul_nonneg (by norm_num) hη0)
  have hfrac :
      36 * η / (1 - 3 * η) ≤ 72 * η :=
    (div_le_iff₀ hqpos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hnum)
  have hρsqpos : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hscaled :
      (36 * η / (1 - 3 * η)) / ρ ^ 2 ≤
        (72 * η) / ρ ^ 2 :=
    div_le_div_of_nonneg_right hfrac hρsqpos.le
  unfold twoCellStabilityModulus
  calc
    2 * η + (36 * η / (1 - 3 * η)) / ρ ^ 2 ≤
        2 * η + (72 * η) / ρ ^ 2 :=
      add_le_add_left hscaled _
    _ = η * (2 + 72 / ρ ^ 2) := by ring

end
end EverettianDecoherence.Approximation

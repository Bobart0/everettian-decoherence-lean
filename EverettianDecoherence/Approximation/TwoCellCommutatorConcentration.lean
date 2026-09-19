import EverettianDecoherence.Approximation.NearSaturationTwoCell

/-!
**FR.** Interface structurelle pour la stabilité T5. On encode la conclusion
"deux cellules capturent tout sauf une fraction eps du budget quadratique
global" sans choisir d'ordre sur les cellules et sans diviser par delta^2.
Ce prédicat est l'analogue robuste de la borne sur la queue top-two tau.

**EN.** Structural interface for T5 stability. We encode the conclusion that
two cells capture all but an eps fraction of the global quadratic budget,
without ordering the cells and without dividing by delta squared. This is the
robust analogue of a top-two tail bound tau.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

/-- Squared cellwise operator-norm commutator. -/
noncomputable def cellCommutatorOpNormSq
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (c : (Projective.interface n).Cell D) : ℝ :=
  perspectiveProjectorCommutatorOpNormProfile D U c ^ 2

@[simp]
theorem cellCommutatorOpNormSq_eq_incomingWitnessP
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (c : (Projective.interface n).Cell D) :
    cellCommutatorOpNormSq D U c = incomingWitnessP D U c := by
  rfl

theorem cellCommutatorOpNormSq_nonneg
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (c : (Projective.interface n).Cell D) :
    0 ≤ cellCommutatorOpNormSq D U c := by
  unfold cellCommutatorOpNormSq
  positivity

/-- Two-cell concentration within a relative fraction eps of the global
squared L2 commutator budget. The formulation avoids division, hence remains
well-defined also at zero defect. -/
def TwoCellCommutatorConcentratedWithin
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) (ε : ℝ) : Prop :=
  ∃ i j : (Projective.interface n).Cell D,
    i ≠ j ∧
      operatorNormProjectorCommutatorL2 D U ^ 2 -
          cellCommutatorOpNormSq D U i -
          cellCommutatorOpNormSq D U j ≤
        ε * operatorNormProjectorCommutatorL2 D U ^ 2

theorem TwoCellCommutatorConcentratedWithin.mono
    {n : ℕ} {D : Perspective n}
    {U : H n ≃ₗᵢ[ℂ] H n} {ε ε' : ℝ}
    (h : TwoCellCommutatorConcentratedWithin D U ε)
    (hε : ε ≤ ε') :
    TwoCellCommutatorConcentratedWithin D U ε' := by
  obtain ⟨i, j, hij, htail⟩ := h
  refine ⟨i, j, hij, htail.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hε
    (sq_nonneg (operatorNormProjectorCommutatorL2 D U))

/-- A concrete normalized near-saturating state forces relative two-cell
concentration with the exact eta-rho modulus. -/
theorem twoCellCommutatorConcentratedWithin_of_near_saturated_state
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (x : H n) (hx : ‖x‖ = 1)
    (η ρ : ℝ)
    (hη0 : 0 ≤ η)
    (hηfive : η ≤ 1 / 5)
    (hρpos : 0 < ρ)
    (hρdelta : ρ ≤ operatorNormProjectorCommutatorL2 D U)
    (hnear :
      2 * (1 - η) * operatorNormProjectorCommutatorL2 D U ^ 2 ≤
        recordProfileL1 D (U x) x ^ 2) :
    TwoCellCommutatorConcentratedWithin D U
      (twoCellStabilityModulus ρ η) := by
  obtain ⟨i, hi, j, hj, htail⟩ :=
    exists_two_cell_concentration_of_near_saturated_state
      D U x hx η ρ hη0 hηfive hρpos hρdelta hnear
  have hjnot :
      j ∉ positiveRecordSubset D (U x) x := by
    simpa using hj
  have hij : i ≠ j := by
    intro hij
    apply hjnot
    simpa [hij] using hi
  refine ⟨i, j, hij, ?_⟩
  simpa [TwoCellCommutatorConcentratedWithin,
    cellCommutatorOpNormSq, incomingWitnessP,
    twoCellStabilityModulus] using htail

/-- Transparent linear form: for eta <= 1/6, near saturation at scale at least
rho forces a two-cell tail fraction at most eta * (2 + 72 / rho^2). -/
theorem twoCellCommutatorConcentratedWithin_linear_of_near_saturated_state
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (x : H n) (hx : ‖x‖ = 1)
    (η ρ : ℝ)
    (hη0 : 0 ≤ η)
    (hηsix : η ≤ 1 / 6)
    (hρpos : 0 < ρ)
    (hρdelta : ρ ≤ operatorNormProjectorCommutatorL2 D U)
    (hnear :
      2 * (1 - η) * operatorNormProjectorCommutatorL2 D U ^ 2 ≤
        recordProfileL1 D (U x) x ^ 2) :
    TwoCellCommutatorConcentratedWithin D U
      (η * (2 + 72 / ρ ^ 2)) := by
  have hηfive : η ≤ 1 / 5 := by
    linarith
  have hbase :=
    twoCellCommutatorConcentratedWithin_of_near_saturated_state
      D U x hx η ρ hη0 hηfive hρpos hρdelta hnear
  exact hbase.mono
    (twoCellStabilityModulus_le_linear hρpos hη0 hηsix)

end
end EverettianDecoherence.Approximation

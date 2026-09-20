import EverettianDecoherence.Approximation.CutEnvelope
import EverettianDecoherence.Approximation.TwoCellCommutatorConcentration

/-!
**FR.** Stabilité inverse exprimée par l'enveloppe finie des cuts. Si le
maximum Cmax des normes de commutateurs agrégés quasi-sature sa borne
universelle Cmax^2 <= delta^2 / 2, alors le budget cellulaire est concentré
sur deux cellules.

**EN.** Inverse stability expressed through the finite cut envelope. If the
maximum Cmax of aggregate commutator norms nearly saturates its universal
bound Cmax^2 <= delta^2 / 2, then the cellwise budget concentrates on two
cells.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

/-- Near saturation of the finite cut envelope forces relative two-cell
concentration with the exact eta-rho modulus. -/
theorem twoCellCommutatorConcentratedWithin_of_maxCut_near_saturated
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (η ρ : ℝ)
    (hη0 : 0 ≤ η)
    (hηfive : η ≤ 1 / 5)
    (hρpos : 0 < ρ)
    (hρdelta : ρ ≤ operatorNormProjectorCommutatorL2 D U)
    (hnear :
      2 * (1 - η) * operatorNormProjectorCommutatorL2 D U ^ 2 ≤
        (2 * maxSubsetCommutatorOpNorm D U) ^ 2) :
    TwoCellCommutatorConcentratedWithin D U
      (twoCellStabilityModulus ρ η) := by
  obtain ⟨S, hSmax⟩ := exists_subsetCommutatorOpNorm_eq_max D U
  let δ : ℝ := operatorNormProjectorCommutatorL2 D U
  let C : ℝ := ‖recordSubsetProjectorCommutatorCLM D U S‖
  have hEη :
      δ ^ 2 - 2 * C ^ 2 ≤ η * δ ^ 2 := by
    have hnear' :
        2 * (1 - η) * δ ^ 2 ≤ (2 * C) ^ 2 := by
      simpa [δ, C, hSmax] using hnear
    nlinarith
  obtain ⟨i, hi, j, hj, htail⟩ :=
    exists_two_cell_concentration_of_cut_eta_rho
      D U S η ρ hη0 hηfive hρpos hρdelta
      (by simpa [δ, C] using hEη)
  have hjnot : j ∉ S := by
    simpa using hj
  have hij : i ≠ j := by
    intro hij
    apply hjnot
    simpa [hij] using hi
  refine ⟨i, j, hij, ?_⟩
  have htail' :
      operatorNormProjectorCommutatorL2 D U ^ 2 -
          incomingWitnessP D U i - incomingWitnessP D U j ≤
        twoCellStabilityModulus ρ η *
          operatorNormProjectorCommutatorL2 D U ^ 2 := by
    calc
      operatorNormProjectorCommutatorL2 D U ^ 2 -
            incomingWitnessP D U i - incomingWitnessP D U j ≤
          operatorNormProjectorCommutatorL2 D U ^ 2 *
            twoCellStabilityModulus ρ η := by
        simpa [twoCellStabilityModulus] using htail
      _ = twoCellStabilityModulus ρ η *
            operatorNormProjectorCommutatorL2 D U ^ 2 := by
        ac_rfl
  simpa [TwoCellCommutatorConcentratedWithin,
    cellCommutatorOpNormSq, incomingWitnessP] using htail'

/-- Linear transparent form of finite-envelope stability. -/
theorem twoCellCommutatorConcentratedWithin_linear_of_maxCut_near_saturated
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (η ρ : ℝ)
    (hη0 : 0 ≤ η)
    (hηsix : η ≤ 1 / 6)
    (hρpos : 0 < ρ)
    (hρdelta : ρ ≤ operatorNormProjectorCommutatorL2 D U)
    (hnear :
      2 * (1 - η) * operatorNormProjectorCommutatorL2 D U ^ 2 ≤
        (2 * maxSubsetCommutatorOpNorm D U) ^ 2) :
    TwoCellCommutatorConcentratedWithin D U
      (η * (2 + 72 / ρ ^ 2)) := by
  have hηfive : η ≤ 1 / 5 := by
    linarith
  have hbase :=
    twoCellCommutatorConcentratedWithin_of_maxCut_near_saturated
      D U η ρ hη0 hηfive hρpos hρdelta hnear
  exact hbase.mono
    (twoCellStabilityModulus_le_linear hρpos hη0 hηsix)

end
end EverettianDecoherence.Approximation

import EverettianDecoherence.Approximation.CutEnvelope
import EverettianDecoherence.Approximation.TwoCellCommutatorConcentration
import EverettianDecoherence.Approximation.TwoCellStabilityModulusSharp

/-!
**FR.** Théorèmes de stabilité v12 au niveau de l'enveloppe maximale des cuts.
Le modulus relatif porte la constante 18, et sa forme linéaire sur
eta <= 1/6 porte la constante 36.

**EN.** v12 stability theorems at the maximal-cut-envelope level. The relative
modulus has constant 18, and its linear eta <= 1/6 form has constant 36.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

theorem twoCellCommutatorConcentratedWithin18_of_maxCut_near_saturated
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
      (twoCellStabilityModulus18 ρ η) := by
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
    exists_two_cell_concentration_of_cut_eta_rho_18
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
        twoCellStabilityModulus18 ρ η *
          operatorNormProjectorCommutatorL2 D U ^ 2 := by
    calc
      operatorNormProjectorCommutatorL2 D U ^ 2 -
            incomingWitnessP D U i - incomingWitnessP D U j ≤
          operatorNormProjectorCommutatorL2 D U ^ 2 *
            twoCellStabilityModulus18 ρ η := by
        simpa [twoCellStabilityModulus18] using htail
      _ = twoCellStabilityModulus18 ρ η *
            operatorNormProjectorCommutatorL2 D U ^ 2 := by
        ac_rfl
  simpa [TwoCellCommutatorConcentratedWithin,
    cellCommutatorOpNormSq, incomingWitnessP] using htail'

theorem twoCellCommutatorConcentratedWithin18_linear_of_maxCut_near_saturated
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
      (η * (2 + 36 / ρ ^ 2)) := by
  have hηfive : η ≤ 1 / 5 := by
    linarith
  have hbase :=
    twoCellCommutatorConcentratedWithin18_of_maxCut_near_saturated
      D U η ρ hη0 hηfive hρpos hρdelta hnear
  exact hbase.mono
    (twoCellStabilityModulus18_le_linear hρpos hη0 hηsix)

end
end EverettianDecoherence.Approximation

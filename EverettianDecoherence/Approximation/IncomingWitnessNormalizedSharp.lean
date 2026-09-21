import EverettianDecoherence.Approximation.IncomingWitnessNormalized
import EverettianDecoherence.Metrics.FiniteGramStabilitySharp

/-!
**FR.** Raffinement v12 des familles normalisées pour les cellules bonnes.
La condition alpha <= p/2 implique r >= p/2 et permet de remplacer le
contrôle quadratique 2 alpha par (47/40) alpha.

**EN.** v12 refinement of the normalized good-cell families. The condition
alpha <= p/2 implies r >= p/2 and improves the squared-error control from
2 alpha to (47/40) alpha.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical InnerProductSpace

noncomputable section

theorem incomingWitnessXi_sub_Zeta_norm_sq_le_47_40
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (hv : ‖v‖ = 1)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v)
    (i : ↥(incomingWitnessActiveGoodCells D U S v)) :
    ‖incomingWitnessXi D U S v i -
        incomingWitnessZeta D U S v i‖ ^ 2 ≤
      (47 / 40 : ℝ) * incomingWitnessAlpha D U i.1 v := by
  have hi :=
    (mem_incomingWitnessActiveGoodCells D U S v i.1).mp i.2
  have hrpos :=
    incomingWitnessR_pos_of_activeGood D U S v i.1 i.2
  have halpha0 :=
    incomingWitnessAlpha_nonneg_of_mem
      D U S i.1 hi.1 v hv hvcompl
  have hrp :
      incomingWitnessR D U i.1 v ≤ incomingWitnessP D U i.1 := by
    unfold incomingWitnessAlpha at halpha0
    linarith
  have hhalf :
      incomingWitnessP D U i.1 / 2 ≤ incomingWitnessR D U i.1 v := by
    have hgood := hi.2.1
    unfold incomingWitnessAlpha at hgood
    linarith
  have hq :=
    incomingWitnessCellResidual_norm_sq_le D U i.1 v
  have hinner :=
    re_inner_incomingWitnessCellResidual_eq_norm_sq
      D U S i.1 hi.1 v hvcompl
  have hbase :=
    normalized_residual_close_good_47_40
      v (incomingWitnessCellResidual D U i.1 v)
      (incomingWitnessP D U i.1)
      (incomingWitnessR D U i.1 v)
      hv hrpos hrp hhalf hq hinner
  have hdiff :
      incomingWitnessXi D U S v i -
          incomingWitnessZeta D U S v i =
        (((Real.sqrt (incomingWitnessR D U i.1 v) : ℝ) : ℂ)⁻¹) •
            incomingWitnessCellResidual D U i.1 v -
          (((Real.sqrt (incomingWitnessP D U i.1) : ℝ) : ℂ)) • v := by
    unfold incomingWitnessXi incomingWitnessZeta
    unfold incomingWitnessCellResidual
    module
  rw [hdiff]
  simpa [incomingWitnessAlpha] using hbase

theorem sum_incomingWitnessXi_sub_Zeta_norm_sq_le_47_40
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (hv : ‖v‖ = 1)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v) :
    (∑ i : ↥(incomingWitnessActiveGoodCells D U S v),
        ‖incomingWitnessXi D U S v i -
          incomingWitnessZeta D U S v i‖ ^ 2) ≤
      (47 / 40 : ℝ) *
        (∑ c ∈ S, incomingWitnessAlpha D U c v) := by
  calc
    (∑ i : ↥(incomingWitnessActiveGoodCells D U S v),
        ‖incomingWitnessXi D U S v i -
          incomingWitnessZeta D U S v i‖ ^ 2) ≤
      ∑ i : ↥(incomingWitnessActiveGoodCells D U S v),
        (47 / 40 : ℝ) * incomingWitnessAlpha D U i.1 v := by
      apply Finset.sum_le_sum
      intro i _
      exact incomingWitnessXi_sub_Zeta_norm_sq_le_47_40
        D U S v hv hvcompl i
    _ = (47 / 40 : ℝ) *
        ∑ i : ↥(incomingWitnessActiveGoodCells D U S v),
          incomingWitnessAlpha D U i.1 v := by
      rw [Finset.mul_sum]
    _ ≤ (47 / 40 : ℝ) *
        (∑ c ∈ S, incomingWitnessAlpha D U c v) := by
      have hactive :
          (∑ i : ↥(incomingWitnessActiveGoodCells D U S v),
              incomingWitnessAlpha D U i.1 v) ≤
            ∑ c ∈ S, incomingWitnessAlpha D U c v := by
        calc
          (∑ i : ↥(incomingWitnessActiveGoodCells D U S v),
              incomingWitnessAlpha D U i.1 v) =
              ∑ c ∈ incomingWitnessActiveGoodCells D U S v,
                incomingWitnessAlpha D U c v := by
            exact Finset.sum_coe_sort
              (incomingWitnessActiveGoodCells D U S v)
              (fun c => incomingWitnessAlpha D U c v)
          _ ≤ ∑ c ∈ S, incomingWitnessAlpha D U c v := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro c hc
              exact
                ((mem_incomingWitnessActiveGoodCells D U S v c).mp hc).1
            · intro c hcS _hcnot
              exact incomingWitnessAlpha_nonneg_of_mem
                D U S c hcS v hv hvcompl
      exact mul_le_mul_of_nonneg_left hactive (by norm_num)

end
end EverettianDecoherence.Approximation

import Mathlib.Analysis.SpecificLimits.Basic
import EverettianDecoherence.Metrics.DimensionFreeSharpness.Profile

/-!
**FR.** # Optimalité de la constante 2 dans la borne ED2B

Ce module reste **BORN-SENSITIVE** : il utilise `recordProfileL1`, donc
`bornRecord`. La famille rationnelle explicite en dimension `2` conduit au
quotient `recordProfileL1 D x y / ‖x-y‖`; son carré vaut
`4 - 4 / (p^2 + 1)`, d'où la convergence vers `2` et le corollaire de
sharpness excluant toute constante universelle strictement inférieure à `2`.

**EN.** # Sharpness of the constant 2 in the ED2B bound

This module remains **BORN-SENSITIVE** because it uses `recordProfileL1`, hence
`bornRecord`. The explicit rational family in dimension `2` yields the ratio
`recordProfileL1 D x y / ‖x-y‖`; its square is
`4 - 4 / (p^2 + 1)`, giving convergence to `2` and the sharpness corollary
excluding every universal constant strictly below `2`.
-/

namespace EverettianDecoherence.Metrics

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open Filter
open scoped BigOperators Classical InnerProductSpace Topology

noncomputable section

/-- Ratio whose limiting value measures sharpness of the constant `2`. -/
noncomputable def dimensionFreeSharpnessRatio (n : ℕ) : ℝ :=
  recordProfileL1 sharpnessPerspective (sharpnessX n) (sharpnessY n) /
    ‖sharpnessX n - sharpnessY n‖

/-- The sharpness ratio is nonnegative. -/
theorem dimensionFreeSharpnessRatio_nonneg (n : ℕ) :
    0 ≤ dimensionFreeSharpnessRatio n := by
  exact div_nonneg (recordProfileL1_nonneg _ _ _) (norm_nonneg _)

/-- The already-proved ED2B estimate supplies the matching universal upper bound. -/
theorem dimensionFreeSharpnessRatio_le_two (n : ℕ) :
    dimensionFreeSharpnessRatio n ≤ 2 := by
  unfold dimensionFreeSharpnessRatio
  have h := recordProfileL1_le_two_mul_norm_sub sharpnessPerspective
    (sharpnessX n) (sharpnessY n) (sharpnessX_norm n) (sharpnessY_norm n)
  exact (div_le_iff₀ (sharpness_state_distance_pos n)).2 (by nlinarith)

/-- Exact squared quotient; its defect from `4` is rational and tends to zero. -/
theorem dimensionFreeSharpnessRatio_sq (n : ℕ) :
    dimensionFreeSharpnessRatio n ^ 2 =
      4 - 4 / ((sharpnessP n : ℝ) ^ 2 + 1) := by
  have hq : (sharpnessQ n : ℝ) ≠ 0 := ne_of_gt (sharpnessQ_real_pos n)
  have hdist : ‖sharpnessX n - sharpnessY n‖ ≠ 0 :=
    ne_of_gt (sharpness_state_distance_pos n)
  have hpell :
      (sharpnessP n : ℝ) ^ 2 + 1 = 2 * (sharpnessQ n : ℝ) ^ 2 := by
    exact_mod_cast sharpnessP_sq_add_one_eq_two_mul_Q_sq n
  unfold dimensionFreeSharpnessRatio
  rw [div_pow, sharpness_recordProfileL1_rational, sharpness_state_difference_sq]
  have hpden : 0 < (sharpnessP n : ℝ) ^ 2 + 1 := by positivity
  field_simp [hq, ne_of_gt hpden]
  nlinarith [hpell]

private theorem sharpness_denominator_tendsto_atTop :
    Filter.Tendsto (fun n : ℕ => (sharpnessP n : ℝ) ^ 2 + 1)
      Filter.atTop Filter.atTop := by
  have hsquare :
      Filter.Tendsto (fun x : ℝ => x ^ 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_pow_atTop (by norm_num)
  exact tendsto_atTop_add_const_right _ _ (hsquare.comp sharpnessP_tendsto_atTop)

private theorem sharpness_defect_tendsto_zero :
    Filter.Tendsto
      (fun n : ℕ => 4 / ((sharpnessP n : ℝ) ^ 2 + 1))
      Filter.atTop (𝓝 0) := by
  simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using
    (tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero.comp sharpness_denominator_tendsto_atTop))

private theorem dimensionFreeSharpnessRatio_sq_tendsto_four :
    Filter.Tendsto (fun n => dimensionFreeSharpnessRatio n ^ 2)
      Filter.atTop (𝓝 4) := by
  have hconst :
      Filter.Tendsto (fun _ : ℕ => (4 : ℝ)) Filter.atTop (𝓝 4) :=
    tendsto_const_nhds
  have h := hconst.sub sharpness_defect_tendsto_zero
  simpa [dimensionFreeSharpnessRatio_sq] using h

/-- Main sharpness theorem: the explicit rational-state ratio tends to `2`. -/
theorem dimensionFreeSharpnessRatio_tendsto_two :
    Filter.Tendsto dimensionFreeSharpnessRatio Filter.atTop (𝓝 2) := by
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp
    dimensionFreeSharpnessRatio_sq_tendsto_four
  change Filter.Tendsto
    (fun n => Real.sqrt (dimensionFreeSharpnessRatio n ^ 2))
    Filter.atTop (𝓝 (Real.sqrt 4)) at hsqrt
  have hrewrite :
      (fun n => Real.sqrt (dimensionFreeSharpnessRatio n ^ 2)) =
        dimensionFreeSharpnessRatio := by
    funext n
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (dimensionFreeSharpnessRatio_nonneg n)]
  rw [hrewrite] at hsqrt
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by norm_num
  simpa [hsqrt4] using hsqrt

/-- Operational sharpness consequence: every proposed universal constant below
`2` is violated by some member of the explicit rational family. -/
theorem exists_recordProfileL1_gt_const_mul_norm_sub_of_lt_two
    {K : ℝ} (hK : K < 2) :
    ∃ n : ℕ,
      K * ‖sharpnessX n - sharpnessY n‖ <
        recordProfileL1 sharpnessPerspective (sharpnessX n) (sharpnessY n) := by
  have hev : ∀ᶠ n in Filter.atTop, K < dimensionFreeSharpnessRatio n :=
    (dimensionFreeSharpnessRatio_tendsto_two.eventually
      (eventually_gt_nhds hK))
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨n, ?_⟩
  unfold dimensionFreeSharpnessRatio at hn
  exact (lt_div_iff₀ (sharpness_state_distance_pos n)).mp hn

end
end EverettianDecoherence.Metrics

import EverettianDecoherence.Approximation.ExactStabilityParameters
import EverettianDecoherence.Approximation.StabilitySharpness.PublicationFacingTail
import EverettianDecoherence.Approximation.StabilitySharpness.DiffuseFamilyMaxCut
import EverettianDecoherence.Approximation.StabilitySharpness.DiffuseFamilyTail
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Sharp complete-diffusion threshold 1/8.

This file gives a publication-facing eventual formulation of the universal
lower threshold and the exact scalar diffuse identity that attains it.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open Filter
open scoped BigOperators Classical Topology

noncomputable section

noncomputable def v19DiffuseEtaOverGlobal (m : ℕ) (d : ℝ) : ℝ :=
  v18DiffuseEnvelopeDefect m d / v18DiffuseGlobal m d ^ 2

theorem v19DiffuseEtaOverGlobal_eq
    (m : ℕ) (hm2 : 2 ≤ m) (d : ℝ) (hd : d ≠ 0)
    (hA : v18DiffuseGlobal m d ≠ 0) :
    v19DiffuseEtaOverGlobal m d =
      v18DiffuseTau m /
        (8 * (1 - d / (2 * (m : ℝ))) ^ 2) := by
  have hratio := v18Diffuse_scaledRatio_exact m hm2 d hd
  unfold v19DiffuseEtaOverGlobal
  have hE :
      v18DiffuseEnvelopeDefect m d ≠ 0 := by
    rw [v18DiffuseEnvelopeDefect_exact m (by omega) d]
    have hm1 : (1 : ℝ) < (m : ℝ) := by
      exact_mod_cast (show 1 < m by omega)
    have htail : 0 < 1 - 1 / (m : ℝ) := by
      have hmpos : 0 < (m : ℝ) := by positivity
      rw [sub_pos, div_lt_one hmpos]
      linarith
    positivity
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have hq :
      1 - d / (2 * (m : ℝ)) ≠ 0 := by
    intro hq0
    apply hA
    rw [v18DiffuseGlobal_exact m (by omega) d]
    have hden : (2 * (m : ℝ)) ≠ 0 := by positivity
    have hdEq : d = 2 * (m : ℝ) := by
      have hdiv : d / (2 * (m : ℝ)) = 1 := by linarith
      exact (div_eq_one_iff_eq hden).mp hdiv
    rw [hdEq]
    field_simp [hmR]
    ring
  field_simp [hE, hA, hq]
  nlinarith [hratio]

theorem v19DiffuseTau_tendsto_one
    {α : Type*} {l : Filter α}
    (m : α → ℕ)
    (hminv :
      Tendsto (fun k => 1 / (m k : ℝ)) l (𝓝 0)) :
    Tendsto (fun k => v18DiffuseTau (m k)) l (𝓝 1) := by
  unfold v18DiffuseTau
  simpa using
    (tendsto_const_nhds :
      Tendsto (fun _ : α => (1 : ℝ)) l (𝓝 1)).sub hminv

theorem v19DiffuseEtaOverGlobal_tendsto_eighth
    {α : Type*} {l : Filter α}
    (m : α → ℕ) (d : α → ℝ)
    (hm2 : ∀ k, 2 ≤ m k)
    (hdne : ∀ k, d k ≠ 0)
    (hAne : ∀ k, v18DiffuseGlobal (m k) (d k) ≠ 0)
    (hminv :
      Tendsto (fun k => 1 / (m k : ℝ)) l (𝓝 0))
    (hdOverM :
      Tendsto (fun k => d k / (2 * (m k : ℝ))) l (𝓝 0)) :
    Tendsto
      (fun k => v19DiffuseEtaOverGlobal (m k) (d k))
      l (𝓝 (1 / 8 : ℝ)) := by
  have htau := v19DiffuseTau_tendsto_one m hminv
  have hone :
      Tendsto
        (fun k => 1 - d k / (2 * (m k : ℝ)))
        l (𝓝 1) := by
    simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : α => (1 : ℝ)) l (𝓝 1)).sub hdOverM
  have hsq :
      Tendsto
        (fun k => (1 - d k / (2 * (m k : ℝ))) ^ 2)
        l (𝓝 1) := by
    simpa [pow_two] using hone.mul hone
  have hden :
      Tendsto
        (fun k => 8 * (1 - d k / (2 * (m k : ℝ))) ^ 2)
        l (𝓝 8) := by
    simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : α => (8 : ℝ)) l (𝓝 8)).mul hsq
  have hdiv := htau.div hden (by norm_num : (8 : ℝ) ≠ 0)
  have hfun :
      (fun k => v19DiffuseEtaOverGlobal (m k) (d k)) =
        (fun k =>
          v18DiffuseTau (m k) /
            (8 * (1 - d k / (2 * (m k : ℝ))) ^ 2)) := by
    funext k
    exact v19DiffuseEtaOverGlobal_eq
      (m k) (hm2 k) (d k) (hdne k) (hAne k)
  rw [hfun]
  convert hdiv using 1 <;> norm_num

/-- Exact geometric diffuse ratio eta/A equals the scalar E/A^2. -/
theorem diffuse_exactEta_over_globalSq_eq
    {m : ℕ} (hm2 : 2 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi2 : θ < Real.pi / 2) :
    exactMaxCutEta
        (coordinatePerspective (m + m)) (diffuseRotation m θ) /
        operatorNormProjectorCommutatorL2
          (coordinatePerspective (m + m)) (diffuseRotation m θ) ^ 2 =
      v19DiffuseEtaOverGlobal m (diffuseAngularDefect θ) := by
  have hm : 0 < m := by omega
  have hApos :
      0 <
        operatorNormProjectorCommutatorL2
          (coordinatePerspective (m + m)) (diffuseRotation m θ) ^ 2 := by
    rw [diffuseGlobal_budget_sq hm θ]
    unfold v18DiffuseGlobal
    have hp := diffuseCellBudget_pos hm2 hθ0 hθpi2
    positivity
  have hglobal :
      0 < v18DiffuseGlobal m (diffuseAngularDefect θ) := by
    rw [← diffuseGlobal_budget_sq hm θ]
    exact hApos
  have hglobal_ne :
      v18DiffuseGlobal m (diffuseAngularDefect θ) ≠ 0 :=
    ne_of_gt hglobal
  unfold exactMaxCutEta v19DiffuseEtaOverGlobal maxCutEnvelopeDefect
    v18DiffuseEnvelopeDefect
  rw [diffuseGlobal_budget_sq hm θ,
    diffuseMaxCut_sq_eq hm hθ0 hθpi2]
  field_simp [hglobal_ne]
  ring

/-- Geometric envelope defect of the diffuse family, in the exact scalar
form used by the manuscript. -/
theorem diffuseEnvelopeDefect_eq
    {m : ℕ} (hm2 : 2 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi2 : θ < Real.pi / 2) :
    maxCutEnvelopeDefect
        (coordinatePerspective (m + m)) (diffuseRotation m θ) =
      v18DiffuseEnvelopeDefect m (diffuseAngularDefect θ) := by
  have hm : 0 < m := by omega
  unfold maxCutEnvelopeDefect v18DiffuseEnvelopeDefect
  rw [diffuseGlobal_budget_sq hm θ,
    diffuseMaxCut_sq_eq hm hθ0 hθpi2]

theorem diffuseEnvelopeDefect_exact
    {m : ℕ} (hm2 : 2 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi2 : θ < Real.pi / 2) :
    maxCutEnvelopeDefect
        (coordinatePerspective (m + m)) (diffuseRotation m θ) =
      2 * diffuseAngularDefect θ ^ 2 *
        (1 - 1 / (m : ℝ)) := by
  rw [diffuseEnvelopeDefect_eq hm2 hθ0 hθpi2]
  exact v18DiffuseEnvelopeDefect_exact m (by omega)
    (diffuseAngularDefect θ)

/-- Exact geometric sharp-ratio identity
A * tau / eta = A^2 * tau / E = 8 (1 - d/(2m))^2. -/
theorem diffuseScaledRatio_exact
    {m : ℕ} (hm2 : 2 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi2 : θ < Real.pi / 2) :
    (operatorNormProjectorCommutatorL2
        (coordinatePerspective (m + m)) (diffuseRotation m θ) ^ 2) ^ 2 *
        optimalTwoCellTailFraction
          (coordinatePerspective (m + m)) (diffuseRotation m θ) /
        maxCutEnvelopeDefect
          (coordinatePerspective (m + m)) (diffuseRotation m θ) =
      8 * (1 - diffuseAngularDefect θ / (2 * (m : ℝ))) ^ 2 := by
  have hm : 0 < m := by omega
  have hd : diffuseAngularDefect θ ≠ 0 :=
    ne_of_gt (diffuseAngularDefect_pos hθ0 hθpi2)
  rw [diffuseGlobal_budget_sq hm θ,
    diffuseOptimalTwoCellTailFraction_eq_tau hm2 hθ0 hθpi2,
    diffuseEnvelopeDefect_eq hm2 hθ0 hθpi2]
  exact v18Diffuse_scaledRatio_exact m hm2
    (diffuseAngularDefect θ) hd

/-- Universal threshold in an eventual form equivalent to
liminf eta/delta^2 >= 1/8 when tau -> 1. -/
theorem eventually_lt_exactEta_over_globalSq_of_tau_tendsto_one
    (dim : ℕ → ℕ)
    (D : (k : ℕ) → Perspective (dim k))
    (U : (k : ℕ) → H (dim k) ≃ₗᵢ[ℂ] H (dim k))
    (hdelta : ∀ k, 0 < operatorNormProjectorCommutatorL2 (D k) (U k))
    (hetaPos : ∀ k, 0 < exactMaxCutEta (D k) (U k))
    (hA :
      Tendsto
        (fun k => operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2)
        atTop (𝓝 0))
    (heta :
      Tendsto (fun k => exactMaxCutEta (D k) (U k))
        atTop (𝓝 0))
    (htau :
      Tendsto (fun k => exactTwoCellTau (D k) (U k))
        atTop (𝓝 1))
    (r : ℝ) (hr : r < 1 / 8) :
    ∀ᶠ k in atTop,
      r <
        exactMaxCutEta (D k) (U k) /
          operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2 := by
  by_cases hr0 : r ≤ 0
  · filter_upwards with k
    have hApos :=
      sq_pos_of_pos (hdelta k)
    have hratio :
        0 <
          exactMaxCutEta (D k) (U k) /
            operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2 :=
      div_pos (hetaPos k) hApos
    exact lt_of_le_of_lt hr0 hratio
  · have hrpos : 0 < r := lt_of_not_ge hr0
    let c : ℝ := (8 + 1 / r) / 2
    have h8r : 8 * r < 1 := by
      nlinarith
    have hc8 : 8 < c := by
      dsimp [c]
      have hrne : r ≠ 0 := ne_of_gt hrpos
      apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      apply (lt_div_iff₀ hrpos).2
      nlinarith
    have hcpos : 0 < c := lt_trans (by norm_num : (0 : ℝ) < 8) hc8
    have hcr : c * r < 1 := by
      dsimp [c]
      have hrne : r ≠ 0 := ne_of_gt hrpos
      field_simp [hrne]
      nlinarith
    have hexact :
        ∀ k,
          maxCutEnvelopeDefect (D k) (U k) =
            exactMaxCutEta (D k) (U k) *
              operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2 := by
      intro k
      exact (exactMaxCutEta_mul_globalSq (D k) (U k) (hdelta k)).symm
    have htail :=
      eventually_globalSq_mul_optimalTau_le_of_small_defect
        dim D U
        (fun k => exactMaxCutEta (D k) (U k))
        hdelta hetaPos hexact hA heta c hc8
    have htauLower :
        ∀ᶠ k in atTop,
          c * r < exactTwoCellTau (D k) (U k) :=
      htau.eventually (Ioi_mem_nhds hcr)
    filter_upwards [htail, htauLower] with k hk hklow
    have hApos :
        0 < operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2 :=
      sq_pos_of_pos (hdelta k)
    have htauEq :
        exactTwoCellTau (D k) (U k) =
          optimalTwoCellTailFraction (D k) (U k) := rfl
    rw [htauEq] at hklow
    have hlowA :
        c * r *
            operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2 <
          operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2 *
            optimalTwoCellTailFraction (D k) (U k) := by
      exact mul_lt_mul_of_pos_right hklow hApos
    have hchain :
        c * r *
            operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2 <
          c * exactMaxCutEta (D k) (U k) :=
      lt_of_lt_of_le hlowA hk
    have hbetter :
        r * operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2 <
          exactMaxCutEta (D k) (U k) := by
      apply (mul_lt_mul_left hcpos).mp
      simpa [mul_assoc] using hchain
    exact (lt_div_iff₀ hApos).2 hbetter

end
end EverettianDecoherence.Approximation

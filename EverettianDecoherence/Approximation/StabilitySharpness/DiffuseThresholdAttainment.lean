import EverettianDecoherence.Approximation.StabilitySharpness.DiffuseThreshold

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open Filter
open scoped BigOperators Classical Topology

noncomputable section

theorem diffuseExactTau_eq
    {m : ℕ} (hm2 : 2 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi2 : θ < Real.pi / 2) :
    exactTwoCellTau
        (coordinatePerspective (m + m)) (diffuseRotation m θ) =
      v18DiffuseTau m := by
  unfold exactTwoCellTau
  exact diffuseOptimalTwoCellTailFraction_eq_tau hm2 hθ0 hθpi2

theorem diffuseAngularDefect_tendsto_zero
    {α : Type*} {l : Filter α}
    (θ : α → ℝ) (hθ : Tendsto θ l (𝓝 0)) :
    Tendsto (fun k => diffuseAngularDefect (θ k)) l (𝓝 0) := by
  have hcos : Tendsto (fun k => Real.cos (θ k)) l (𝓝 1) := by
    have hc := (Real.continuous_cos.tendsto 0).comp hθ
    simpa [Function.comp_def] using hc
  unfold diffuseAngularDefect
  simpa using
    (tendsto_const_nhds :
      Tendsto (fun _ : α => (1 : ℝ)) l (𝓝 1)).sub hcos

theorem diffuseExactTau_tendsto_one
    (m : ℕ → ℕ) (θ : ℕ → ℝ)
    (hm2 : ∀ k, 2 ≤ m k)
    (hθ0 : ∀ k, 0 < θ k)
    (hθpi2 : ∀ k, θ k < Real.pi / 2)
    (hminv : Tendsto (fun k => 1 / (m k : ℝ)) atTop (𝓝 0)) :
    Tendsto
      (fun k => exactTwoCellTau
        (coordinatePerspective (m k + m k)) (diffuseRotation (m k) (θ k)))
      atTop (𝓝 1) := by
  have htau := v19DiffuseTau_tendsto_one m hminv
  have hfun :
      (fun k => exactTwoCellTau
        (coordinatePerspective (m k + m k)) (diffuseRotation (m k) (θ k))) =
      (fun k => v18DiffuseTau (m k)) := by
    funext k
    exact diffuseExactTau_eq (hm2 k) (hθ0 k) (hθpi2 k)
  rw [hfun]
  exact htau

theorem diffuseExactEtaOverGlobal_tendsto_eighth
    (m : ℕ → ℕ) (θ : ℕ → ℝ)
    (hm2 : ∀ k, 2 ≤ m k)
    (hθ0 : ∀ k, 0 < θ k)
    (hθpi2 : ∀ k, θ k < Real.pi / 2)
    (hminv : Tendsto (fun k => 1 / (m k : ℝ)) atTop (𝓝 0))
    (hθ : Tendsto θ atTop (𝓝 0)) :
    Tendsto
      (fun k =>
        exactMaxCutEta
            (coordinatePerspective (m k + m k)) (diffuseRotation (m k) (θ k)) /
          operatorNormProjectorCommutatorL2
            (coordinatePerspective (m k + m k)) (diffuseRotation (m k) (θ k)) ^ 2)
      atTop (𝓝 (1 / 8 : ℝ)) := by
  let d : ℕ → ℝ := fun k => diffuseAngularDefect (θ k)
  have hd : Tendsto d atTop (𝓝 0) :=
    diffuseAngularDefect_tendsto_zero θ hθ
  have hdne : ∀ k, d k ≠ 0 := by
    intro k
    exact ne_of_gt (diffuseAngularDefect_pos (hθ0 k) (hθpi2 k))
  have hAne : ∀ k, v18DiffuseGlobal (m k) (d k) ≠ 0 := by
    intro k
    have hp := diffuseCellBudget_pos (hm2 k) (hθ0 k) (hθpi2 k)
    have hmposNat : 0 < m k :=
      lt_of_lt_of_le (by decide : 0 < 2) (hm2 k)
    have hmpos : 0 < (m k : ℝ) := by exact_mod_cast hmposNat
    unfold v18DiffuseGlobal
    exact ne_of_gt (mul_pos (mul_pos (by norm_num) hmpos) hp)
  have hdOverM :
      Tendsto (fun k => d k / (2 * (m k : ℝ))) atTop (𝓝 0) := by
    have hhalf : Tendsto (fun k => d k / 2) atTop (𝓝 0) := by
      simpa using hd.div_const 2
    have hprod := hhalf.mul hminv
    have hfun :
        (fun k => d k / (2 * (m k : ℝ))) =
          (fun k => (d k / 2) * (1 / (m k : ℝ))) := by
      funext k
      have hmposNat : 0 < m k :=
        lt_of_lt_of_le (by decide : 0 < 2) (hm2 k)
      have hm0 : (m k : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hmposNat)
      field_simp [hm0]
    rw [hfun]
    simpa using hprod
  have hscalar :=
    v19DiffuseEtaOverGlobal_tendsto_eighth
      m d hm2 hdne hAne hminv hdOverM
  have hfun :
      (fun k =>
        exactMaxCutEta
            (coordinatePerspective (m k + m k)) (diffuseRotation (m k) (θ k)) /
          operatorNormProjectorCommutatorL2
            (coordinatePerspective (m k + m k)) (diffuseRotation (m k) (θ k)) ^ 2) =
      (fun k => v19DiffuseEtaOverGlobal (m k) (d k)) := by
    funext k
    exact diffuse_exactEta_over_globalSq_eq
      (hm2 k) (hθ0 k) (hθpi2 k)
  rw [hfun]
  exact hscalar

theorem diffuseGlobalSq_tendsto_zero
    (m : ℕ → ℕ) (θ : ℕ → ℝ)
    (hm2 : ∀ k, 2 ≤ m k)
    (hminv : Tendsto (fun k => 1 / (m k : ℝ)) atTop (𝓝 0))
    (hθ : Tendsto θ atTop (𝓝 0)) :
    Tendsto
      (fun k =>
        operatorNormProjectorCommutatorL2
          (coordinatePerspective (m k + m k)) (diffuseRotation (m k) (θ k)) ^ 2)
      atTop (𝓝 0) := by
  let d : ℕ → ℝ := fun k => diffuseAngularDefect (θ k)
  have hd : Tendsto d atTop (𝓝 0) :=
    diffuseAngularDefect_tendsto_zero θ hθ
  have hd2 : Tendsto (fun k => d k ^ 2) atTop (𝓝 0) := by
    simpa [pow_two] using hd.mul hd
  have hcorr :
      Tendsto (fun k => 2 * d k ^ 2 * (1 / (m k : ℝ)))
        atTop (𝓝 0) := by
    have htwo :
        Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) :=
      tendsto_const_nhds
    simpa [mul_assoc] using (htwo.mul hd2).mul hminv
  have hmain : Tendsto (fun k => 4 * d k) atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (𝓝 4)).mul hd
  have hformula :
      (fun k =>
        operatorNormProjectorCommutatorL2
          (coordinatePerspective (m k + m k)) (diffuseRotation (m k) (θ k)) ^ 2) =
      (fun k => 4 * d k - 2 * d k ^ 2 * (1 / (m k : ℝ))) := by
    funext k
    have hm : 0 < m k :=
      lt_of_lt_of_le (by decide : 0 < 2) (hm2 k)
    rw [diffuseGlobal_budget_sq_exact hm (θ k)]
    dsimp [d]
    ring
  rw [hformula]
  simpa using hmain.sub hcorr

theorem diffuseExactEta_tendsto_zero
    (m : ℕ → ℕ) (θ : ℕ → ℝ)
    (hm2 : ∀ k, 2 ≤ m k)
    (hθ0 : ∀ k, 0 < θ k)
    (hθpi2 : ∀ k, θ k < Real.pi / 2)
    (hminv : Tendsto (fun k => 1 / (m k : ℝ)) atTop (𝓝 0))
    (hθ : Tendsto θ atTop (𝓝 0)) :
    Tendsto
      (fun k => exactMaxCutEta
        (coordinatePerspective (m k + m k)) (diffuseRotation (m k) (θ k)))
      atTop (𝓝 0) := by
  have hA := diffuseGlobalSq_tendsto_zero m θ hm2 hminv hθ
  have hratio :=
    diffuseExactEtaOverGlobal_tendsto_eighth
      m θ hm2 hθ0 hθpi2 hminv hθ
  have hprod := hratio.mul hA
  have hfun :
      (fun k => exactMaxCutEta
        (coordinatePerspective (m k + m k)) (diffuseRotation (m k) (θ k))) =
      (fun k =>
        (exactMaxCutEta
            (coordinatePerspective (m k + m k)) (diffuseRotation (m k) (θ k)) /
          operatorNormProjectorCommutatorL2
            (coordinatePerspective (m k + m k)) (diffuseRotation (m k) (θ k)) ^ 2) *
        operatorNormProjectorCommutatorL2
          (coordinatePerspective (m k + m k)) (diffuseRotation (m k) (θ k)) ^ 2) := by
    funext k
    have hm : 0 < m k :=
      lt_of_lt_of_le (by decide : 0 < 2) (hm2 k)
    have hApos :
        0 < operatorNormProjectorCommutatorL2
          (coordinatePerspective (m k + m k)) (diffuseRotation (m k) (θ k)) ^ 2 := by
      rw [diffuseGlobal_budget_sq hm (θ k)]
      unfold v18DiffuseGlobal
      have hp := diffuseCellBudget_pos (hm2 k) (hθ0 k) (hθpi2 k)
      positivity
    let A : ℝ :=
      operatorNormProjectorCommutatorL2
        (coordinatePerspective (m k + m k)) (diffuseRotation (m k) (θ k)) ^ 2
    have hAne : A ≠ 0 := by
      dsimp [A]
      exact ne_of_gt hApos
    change
      exactMaxCutEta
          (coordinatePerspective (m k + m k)) (diffuseRotation (m k) (θ k)) =
        (exactMaxCutEta
            (coordinatePerspective (m k + m k)) (diffuseRotation (m k) (θ k)) / A) * A
    exact (div_mul_cancel₀ _ hAne).symm
  rw [hfun]
  simpa using hprod

/-- Geometric diffuse sequences with m -> infinity and theta -> 0 attain the
complete-diffusion threshold 1/8, while the global budget vanishes and the
optimal two-cell tail tends to one. -/
theorem diffuse_completeDiffusion_attains_eighth
    (m : ℕ → ℕ) (θ : ℕ → ℝ)
    (hm2 : ∀ k, 2 ≤ m k)
    (hθ0 : ∀ k, 0 < θ k)
    (hθpi2 : ∀ k, θ k < Real.pi / 2)
    (hminv : Tendsto (fun k => 1 / (m k : ℝ)) atTop (𝓝 0))
    (hθ : Tendsto θ atTop (𝓝 0)) :
    Tendsto
      (fun k =>
        operatorNormProjectorCommutatorL2
          (coordinatePerspective (m k + m k)) (diffuseRotation (m k) (θ k)) ^ 2)
      atTop (𝓝 0) ∧
    Tendsto
      (fun k => exactMaxCutEta
        (coordinatePerspective (m k + m k)) (diffuseRotation (m k) (θ k)))
      atTop (𝓝 0) ∧
    Tendsto
      (fun k => exactTwoCellTau
        (coordinatePerspective (m k + m k)) (diffuseRotation (m k) (θ k)))
      atTop (𝓝 1) ∧
    Tendsto
      (fun k =>
        exactMaxCutEta
            (coordinatePerspective (m k + m k)) (diffuseRotation (m k) (θ k)) /
          operatorNormProjectorCommutatorL2
            (coordinatePerspective (m k + m k)) (diffuseRotation (m k) (θ k)) ^ 2)
      atTop (𝓝 (1 / 8 : ℝ)) := by
  exact ⟨
    diffuseGlobalSq_tendsto_zero m θ hm2 hminv hθ,
    diffuseExactEta_tendsto_zero m θ hm2 hθ0 hθpi2 hminv hθ,
    diffuseExactTau_tendsto_one m θ hm2 hθ0 hθpi2 hminv,
    diffuseExactEtaOverGlobal_tendsto_eighth
      m θ hm2 hθ0 hθpi2 hminv hθ⟩

end
end EverettianDecoherence.Approximation

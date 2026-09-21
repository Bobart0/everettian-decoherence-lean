import EverettianDecoherence.Approximation.StabilitySharpness.V12TwoParameterInvariants

/-!
**FR.** Conséquences asymptotiques de la famille continue v12 à deux
paramètres. On introduit le défaut relatif eta=E/A et le ratio sharp
A*tau/eta=A*tail/E. Pour x fixé dans (0,1), A->0, eta->0 et le ratio tend
vers 4/max{x,1-x}. Le chemin symétrique x=1/2 donne exactement
8-5d+(3/4)d^2. Le chemin x=d est ultra-near : eta/A->0 et le ratio tend
vers 4.

**EN.** Asymptotic consequences of the continuous v12 two-parameter family.
We introduce the relative defect eta=E/A and sharp ratio
A*tau/eta=A*tail/E. For fixed x in (0,1), A->0, eta->0 and the ratio tends
to 4/max{x,1-x}. The symmetric path x=1/2 is exactly
8-5d+(3/4)d^2. The path x=d is ultra-near: eta/A->0 and the ratio tends
to 4.
-/

namespace EverettianDecoherence.Approximation

open Filter
open scoped Topology

noncomputable section

def v12TwoParamEta (d x : ℝ) : ℝ :=
  v12TwoParamDefect d x / v12TwoParamGlobal d x

def v12TwoParamScaledRatio (d x : ℝ) : ℝ :=
  v12TwoParamGlobal d x * v12TwoParamTail d x /
    v12TwoParamDefect d x

def v12TwoParamEtaOverGlobal (d x : ℝ) : ℝ :=
  v12TwoParamDefect d x / v12TwoParamGlobal d x ^ 2

theorem v12TwoParamScaledRatio_eq_simplified
    (d x : ℝ)
    (hd : d ≠ 0) (hx : x ≠ 0) (h1x : 1 - x ≠ 0) :
    v12TwoParamScaledRatio d x =
      v12TwoParamSimplifiedRatio d x := by
  unfold v12TwoParamScaledRatio
  exact v12TwoParam_scaled_ratio_eq_simplified d x hd hx h1x

theorem v12TwoParamEta_eq_canceled
    (d x : ℝ) :
    v12TwoParamEta d x =
      x * (1 - x) * d /
        (2 - d + x * (1 - x) * d) := by
  by_cases hd : d = 0
  · subst d
    simp [v12TwoParamEta, v12TwoParamDefect,
      v12TwoParamGlobal]
  · unfold v12TwoParamEta
    rw [show v12TwoParamGlobal d x =
        2 * d * (2 - d + x * (1 - x) * d) by
        exact v12TwoParam_global_factor d x]
    unfold v12TwoParamDefect
    by_cases hB : 2 - d + x * (1 - x) * d = 0
    · simp [hB]
    · field_simp [hd, hB]
      ring

theorem v12TwoParamGlobal_tendsto_zero
    {α : Type*} {l : Filter α}
    (x : ℝ) (d : α → ℝ)
    (hd : Tendsto d l (𝓝 0)) :
    Tendsto (fun k => v12TwoParamGlobal (d k) x)
      l (𝓝 0) := by
  have hd2 : Tendsto (fun k => d k ^ 2) l (𝓝 0) := by
    simpa [pow_two] using hd.mul hd
  have h1 :=
    (tendsto_const_nhds :
      Tendsto (fun _ : α => (4 : ℝ)) l (𝓝 4)).mul hd
  have h2 :=
    (tendsto_const_nhds :
      Tendsto (fun _ : α => (2 : ℝ)) l (𝓝 2)).mul hd2
  have hq :
      Tendsto
        (fun _ : α => (2 * x * (1 - x) : ℝ))
        l (𝓝 (2 * x * (1 - x))) :=
    tendsto_const_nhds
  have h3 := hq.mul hd2
  unfold v12TwoParamGlobal
  convert (h1.sub h2).add h3 using 1 <;> norm_num

theorem v12TwoParamEta_tendsto_zero
    {α : Type*} {l : Filter α}
    (x : ℝ) (d : α → ℝ)
    (hd : Tendsto d l (𝓝 0)) :
    Tendsto (fun k => v12TwoParamEta (d k) x)
      l (𝓝 0) := by
  have hnum :
      Tendsto
        (fun k => x * (1 - x) * d k)
        l (𝓝 0) := by
    have hc :
        Tendsto
          (fun _ : α => (x * (1 - x) : ℝ))
          l (𝓝 (x * (1 - x))) :=
      tendsto_const_nhds
    simpa using hc.mul hd
  have hqd :
      Tendsto
        (fun k => x * (1 - x) * d k)
        l (𝓝 0) := hnum
  have hden :
      Tendsto
        (fun k => 2 - d k + x * (1 - x) * d k)
        l (𝓝 2) := by
    have htwo :
        Tendsto (fun _ : α => (2 : ℝ)) l (𝓝 2) :=
      tendsto_const_nhds
    simpa using (htwo.sub hd).add hqd
  have hdiv := hnum.div hden (by norm_num : (2 : ℝ) ≠ 0)
  have hfun :
      (fun k => v12TwoParamEta (d k) x) =
      (fun k =>
        x * (1 - x) * d k /
          (2 - d k + x * (1 - x) * d k)) := by
    funext k
    exact v12TwoParamEta_eq_canceled (d k) x
  rw [hfun]
  norm_num at hdiv
  exact hdiv

theorem v12TwoParamScaledRatio_tendsto_fixed_x
    {α : Type*} {l : Filter α}
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (d : α → ℝ)
    (hd : Tendsto d l (𝓝 0))
    (hdne : ∀ k, d k ≠ 0) :
    Tendsto
      (fun k => v12TwoParamScaledRatio (d k) x)
      l (𝓝 (4 / max x (1 - x))) := by
  have hx : x ≠ 0 := ne_of_gt hx0
  have h1x : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
  have hfun :
      (fun k => v12TwoParamScaledRatio (d k) x) =
      (fun k => v12TwoParamSimplifiedRatio (d k) x) := by
    funext k
    exact v12TwoParamScaledRatio_eq_simplified
      (d k) x (hdne k) hx h1x
  rw [hfun]
  exact v12TwoParamSimplifiedRatio_tendsto x hx0 hx1 d hd

theorem v12TwoParamSimplifiedRatio_half_exact (d : ℝ) :
    v12TwoParamSimplifiedRatio d (1 / 2 : ℝ) =
      8 - 5 * d + (3 / 4 : ℝ) * d ^ 2 := by
  unfold v12TwoParamSimplifiedRatio
  norm_num
  ring

theorem v12TwoParamScaledRatio_half_exact
    (d : ℝ) (hd : d ≠ 0) :
    v12TwoParamScaledRatio d (1 / 2 : ℝ) =
      8 - 5 * d + (3 / 4 : ℝ) * d ^ 2 := by
  rw [v12TwoParamScaledRatio_eq_simplified d (1 / 2 : ℝ)
    hd (by norm_num) (by norm_num)]
  exact v12TwoParamSimplifiedRatio_half_exact d

theorem v12TwoParamScaledRatio_half_tendsto_eight
    {α : Type*} {l : Filter α}
    (d : α → ℝ)
    (hd : Tendsto d l (𝓝 0))
    (hdne : ∀ k, d k ≠ 0) :
    Tendsto
      (fun k => v12TwoParamScaledRatio (d k) (1 / 2 : ℝ))
      l (𝓝 8) := by
  have hD2 : Tendsto (fun k => d k ^ 2) l (𝓝 0) := by
    simpa [pow_two] using hd.mul hd
  have h :=
    (tendsto_const_nhds :
      Tendsto (fun _ : α => (8 : ℝ)) l (𝓝 8)).sub
      ((tendsto_const_nhds :
        Tendsto (fun _ : α => (5 : ℝ)) l (𝓝 5)).mul hd)
  have h' :=
    h.add
      ((tendsto_const_nhds :
        Tendsto (fun _ : α => (3 / 4 : ℝ)) l
          (𝓝 (3 / 4))).mul hD2)
  have hfun :
      (fun k => v12TwoParamScaledRatio (d k) (1 / 2 : ℝ)) =
      (fun k => 8 - 5 * d k + (3 / 4 : ℝ) * d k ^ 2) := by
    funext k
    exact v12TwoParamScaledRatio_half_exact (d k) (hdne k)
  rw [hfun]
  convert h' using 1 <;> norm_num

theorem v12TwoParamSimplifiedRatio_diag_exact
    (d : ℝ) (hd0 : 0 < d) (hdhalf : d ≤ 1 / 2) :
    v12TwoParamSimplifiedRatio d d =
      (2 - d ^ 2) *
        (2 - d + d ^ 2 * (1 - d)) / (1 - d) := by
  have hmin : min d (1 - d) = d := by
    rw [min_eq_left]
    linarith
  have hdne : d ≠ 0 := ne_of_gt hd0
  have h1d : 1 - d ≠ 0 := by linarith
  unfold v12TwoParamSimplifiedRatio
  rw [hmin]
  field_simp [hdne, h1d]

theorem v12TwoParamSimplifiedRatio_diag_tendsto_four
    {α : Type*} {l : Filter α}
    (d : α → ℝ)
    (hd : Tendsto d l (𝓝 0))
    (hd0 : ∀ k, 0 < d k)
    (hdhalf : ∀ k, d k ≤ 1 / 2) :
    Tendsto
      (fun k => v12TwoParamSimplifiedRatio (d k) (d k))
      l (𝓝 4) := by
  have hd2 : Tendsto (fun k => d k ^ 2) l (𝓝 0) := by
    simpa [pow_two] using hd.mul hd
  have h1md :
      Tendsto (fun k => 1 - d k) l (𝓝 1) := by
    have hone :
        Tendsto (fun _ : α => (1 : ℝ)) l (𝓝 1) :=
      tendsto_const_nhds
    simpa using hone.sub hd
  have hleft :
      Tendsto (fun k => 2 - d k ^ 2) l (𝓝 2) := by
    have htwo :
        Tendsto (fun _ : α => (2 : ℝ)) l (𝓝 2) :=
      tendsto_const_nhds
    simpa using htwo.sub hd2
  have hcubic :
      Tendsto (fun k => d k ^ 2 * (1 - d k))
        l (𝓝 0) := by
    simpa using hd2.mul h1md
  have hright :
      Tendsto
        (fun k => 2 - d k + d k ^ 2 * (1 - d k))
        l (𝓝 2) := by
    have htwo :
        Tendsto (fun _ : α => (2 : ℝ)) l (𝓝 2) :=
      tendsto_const_nhds
    simpa using (htwo.sub hd).add hcubic
  have hnum := hleft.mul hright
  have hdiv := hnum.div h1md (by norm_num : (1 : ℝ) ≠ 0)
  have hfun :
      (fun k => v12TwoParamSimplifiedRatio (d k) (d k)) =
      (fun k =>
        (2 - d k ^ 2) *
          (2 - d k + d k ^ 2 * (1 - d k)) /
            (1 - d k)) := by
    funext k
    exact v12TwoParamSimplifiedRatio_diag_exact
      (d k) (hd0 k) (hdhalf k)
  rw [hfun]
  norm_num at hdiv
  exact hdiv

theorem v12TwoParamScaledRatio_diag_tendsto_four
    {α : Type*} {l : Filter α}
    (d : α → ℝ)
    (hd : Tendsto d l (𝓝 0))
    (hd0 : ∀ k, 0 < d k)
    (hdhalf : ∀ k, d k ≤ 1 / 2) :
    Tendsto
      (fun k => v12TwoParamScaledRatio (d k) (d k))
      l (𝓝 4) := by
  have hfun :
      (fun k => v12TwoParamScaledRatio (d k) (d k)) =
      (fun k => v12TwoParamSimplifiedRatio (d k) (d k)) := by
    funext k
    have h1d : 1 - d k ≠ 0 := by
      have := hdhalf k
      linarith
    exact v12TwoParamScaledRatio_eq_simplified
      (d k) (d k) (ne_of_gt (hd0 k)) (ne_of_gt (hd0 k)) h1d
  rw [hfun]
  exact v12TwoParamSimplifiedRatio_diag_tendsto_four
    d hd hd0 hdhalf

theorem v12TwoParamEtaOverGlobal_diag_exact
    (d : ℝ) (hd0 : 0 < d) (hdhalf : d ≤ 1 / 2) :
    v12TwoParamEtaOverGlobal d d =
      d * (1 - d) /
        (2 * (2 - d + d ^ 2 * (1 - d)) ^ 2) := by
  have hdne : d ≠ 0 := ne_of_gt hd0
  have hBpos : 0 < 2 - d + d ^ 2 * (1 - d) := by
    have h1d : 0 ≤ 1 - d := by linarith
    have hsq : 0 ≤ d ^ 2 := sq_nonneg d
    have hnon : 0 ≤ d ^ 2 * (1 - d) :=
      mul_nonneg hsq h1d
    linarith
  have hBne : 2 - d + d ^ 2 * (1 - d) ≠ 0 :=
    ne_of_gt hBpos
  unfold v12TwoParamEtaOverGlobal v12TwoParamDefect
  rw [v12TwoParam_global_factor]
  field_simp [hdne, hBne]

theorem v12TwoParamEtaOverGlobal_diag_tendsto_zero
    {α : Type*} {l : Filter α}
    (d : α → ℝ)
    (hd : Tendsto d l (𝓝 0))
    (hd0 : ∀ k, 0 < d k)
    (hdhalf : ∀ k, d k ≤ 1 / 2) :
    Tendsto
      (fun k => v12TwoParamEtaOverGlobal (d k) (d k))
      l (𝓝 0) := by
  have hd2 : Tendsto (fun k => d k ^ 2) l (𝓝 0) := by
    simpa [pow_two] using hd.mul hd
  have h1md :
      Tendsto (fun k => 1 - d k) l (𝓝 1) := by
    have hone :
        Tendsto (fun _ : α => (1 : ℝ)) l (𝓝 1) :=
      tendsto_const_nhds
    simpa using hone.sub hd
  have hnum :
      Tendsto (fun k => d k * (1 - d k)) l (𝓝 0) := by
    simpa using hd.mul h1md
  have hcubic :
      Tendsto (fun k => d k ^ 2 * (1 - d k))
        l (𝓝 0) := by
    simpa using hd2.mul h1md
  have hB :
      Tendsto
        (fun k => 2 - d k + d k ^ 2 * (1 - d k))
        l (𝓝 2) := by
    have htwo :
        Tendsto (fun _ : α => (2 : ℝ)) l (𝓝 2) :=
      tendsto_const_nhds
    simpa using (htwo.sub hd).add hcubic
  have hB2 :
      Tendsto
        (fun k => (2 - d k + d k ^ 2 * (1 - d k)) ^ 2)
        l (𝓝 4) := by
    have h := hB.mul hB
    convert h using 1 <;> norm_num <;> ring
  have hden :
      Tendsto
        (fun k =>
          2 * (2 - d k + d k ^ 2 * (1 - d k)) ^ 2)
        l (𝓝 8) := by
    have htwo :
        Tendsto (fun _ : α => (2 : ℝ)) l (𝓝 2) :=
      tendsto_const_nhds
    have h := htwo.mul hB2
    norm_num at h
    exact h
  have hdiv := hnum.div hden (by norm_num : (8 : ℝ) ≠ 0)
  have hfun :
      (fun k => v12TwoParamEtaOverGlobal (d k) (d k)) =
      (fun k =>
        d k * (1 - d k) /
          (2 * (2 - d k + d k ^ 2 * (1 - d k)) ^ 2)) := by
    funext k
    exact v12TwoParamEtaOverGlobal_diag_exact
      (d k) (hd0 k) (hdhalf k)
  rw [hfun]
  norm_num at hdiv
  exact hdiv

end
end EverettianDecoherence.Approximation

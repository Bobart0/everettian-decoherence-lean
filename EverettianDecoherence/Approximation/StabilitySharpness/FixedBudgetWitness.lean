import EverettianDecoherence.Approximation.StabilitySharpness.FixedBudgetSlope

namespace EverettianDecoherence.Approximation

open Filter
open scoped Topology

noncomputable section

/-- Ratio tau/eta = absolute tail / envelope defect in the continuous
three-cell family. -/
def v19FixedBudgetSlopePath (d x : ℝ) : ℝ :=
  v12TwoParamTail d x / v12TwoParamDefect d x

theorem v19FixedBudgetSlopePath_eq
    (d x : ℝ) (hd : d ≠ 0) (hx0 : 0 < x) (hxhalf : x ≤ 1 / 2) :
    v19FixedBudgetSlopePath d x =
      (2 - d * x) / (2 * d * (1 - x)) := by
  have hmin : min x (1 - x) = x := by
    rw [min_eq_left]
    linarith
  have hx : x ≠ 0 := ne_of_gt hx0
  have h1x : 1 - x ≠ 0 := by linarith
  unfold v19FixedBudgetSlopePath v12TwoParamTail v12TwoParamGap
    v12TwoParamDefect
  rw [hmin]
  field_simp [hd, hx, h1x]
  ring

theorem v19FixedBudgetGlobal_tendsto_base
    {α : Type*} {l : Filter α}
    (d : ℝ) (x : α → ℝ) (hx : Tendsto x l (𝓝 0)) :
    Tendsto (fun k => v12TwoParamGlobal d (x k)) l
      (𝓝 (v18FixedBudgetBase d)) := by
  unfold v12TwoParamGlobal v18FixedBudgetBase
  have hx1 : Tendsto (fun k => 1 - x k) l (𝓝 1) := by
    simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : α => (1 : ℝ)) l (𝓝 1)).sub hx
  have hprod : Tendsto (fun k => x k * (1 - x k)) l (𝓝 0) := by
    simpa using hx.mul hx1
  have hlast :
      Tendsto (fun k => 2 * x k * (1 - x k) * d ^ 2) l (𝓝 0) := by
    have htwo : Tendsto (fun _ : α => (2 : ℝ)) l (𝓝 2) :=
      tendsto_const_nhds
    simpa [mul_assoc] using
      (htwo.mul hprod).mul
        (tendsto_const_nhds :
          Tendsto (fun _ : α => d ^ 2) l (𝓝 (d ^ 2)))
  simpa using
    (tendsto_const_nhds :
      Tendsto (fun _ : α => (4 * d - 2 * d ^ 2 : ℝ)) l
        (𝓝 (4 * d - 2 * d ^ 2))).add hlast

theorem v19FixedBudgetSlopePath_tendsto_inv
    {α : Type*} {l : Filter α}
    (d : ℝ) (hd : d ≠ 0)
    (x : α → ℝ) (hx : Tendsto x l (𝓝 0))
    (hx0 : ∀ k, 0 < x k) (hxhalf : ∀ k, x k ≤ 1 / 2) :
    Tendsto (fun k => v19FixedBudgetSlopePath d (x k)) l (𝓝 (1 / d)) := by
  have hnum : Tendsto (fun k => 2 - d * x k) l (𝓝 2) := by
    simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : α => (2 : ℝ)) l (𝓝 2)).sub
      ((tendsto_const_nhds :
        Tendsto (fun _ : α => d) l (𝓝 d)).mul hx)
  have h1x : Tendsto (fun k => 1 - x k) l (𝓝 1) := by
    simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : α => (1 : ℝ)) l (𝓝 1)).sub hx
  have hden :
      Tendsto (fun k => 2 * d * (1 - x k)) l (𝓝 (2 * d)) := by
    simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : α => (2 * d : ℝ)) l (𝓝 (2 * d))).mul h1x
  have hdiv := hnum.div hden (mul_ne_zero (by norm_num) hd)
  have hfun :
      (fun k => v19FixedBudgetSlopePath d (x k)) =
      (fun k => (2 - d * x k) / (2 * d * (1 - x k))) := by
    funext k
    exact v19FixedBudgetSlopePath_eq d (x k) hd (hx0 k) (hxhalf k)
  rw [hfun]
  convert hdiv using 1 <;> field_simp [hd] <;> ring

end
end EverettianDecoherence.Approximation

import EverettianDecoherence.Approximation.StabilitySharpness.V12SharpConstants

/-!
**FR.** Couche scalaire de la famille continue v12 à deux paramètres.
Pour d,x réels, on pose
  f_d(y) = 2 d y - d^2 y^2,
  A(d,x) = 4d - 2d^2 + 2x(1-x)d^2,
  E(d,x) = 2x(1-x)d^2.
La queue top-two attendue est f_d(min(x,1-x)). Cette couche isole l'algèbre
et la limite d -> 0 de la construction géométrique C3.

**EN.** Scalar layer of the continuous two-parameter v12 family. It isolates
the exact algebra and the d -> 0 interpolation limit from the C3 geometric
realization.
-/

namespace EverettianDecoherence.Approximation

open Filter
open scoped Topology

noncomputable section

def v12TwoParamGap (d y : ℝ) : ℝ :=
  2 * d * y - d ^ 2 * y ^ 2

def v12TwoParamGlobal (d x : ℝ) : ℝ :=
  4 * d - 2 * d ^ 2 + 2 * x * (1 - x) * d ^ 2

def v12TwoParamDefect (d x : ℝ) : ℝ :=
  2 * x * (1 - x) * d ^ 2

def v12TwoParamTail (d x : ℝ) : ℝ :=
  v12TwoParamGap d (min x (1 - x))

def v12TwoParamSimplifiedRatio (d x : ℝ) : ℝ :=
  min x (1 - x) *
      (2 - d * min x (1 - x)) *
      (2 - d + x * (1 - x) * d) /
    (x * (1 - x))

theorem v12TwoParam_gap_sum_eq_global (d x : ℝ) :
    v12TwoParamGap d (1 - x) +
        v12TwoParamGap d x +
        v12TwoParamGap d 1 =
      v12TwoParamGlobal d x := by
  unfold v12TwoParamGap v12TwoParamGlobal
  ring

theorem v12TwoParam_global_sub_two_gap_one_eq_defect (d x : ℝ) :
    v12TwoParamGlobal d x - 2 * v12TwoParamGap d 1 =
      v12TwoParamDefect d x := by
  unfold v12TwoParamGlobal v12TwoParamGap v12TwoParamDefect
  ring

theorem v12TwoParam_global_factor (d x : ℝ) :
    v12TwoParamGlobal d x =
      2 * d * (2 - d + x * (1 - x) * d) := by
  unfold v12TwoParamGlobal
  ring

theorem v12TwoParam_tail_factor (d x : ℝ) :
    v12TwoParamTail d x =
      d * min x (1 - x) *
        (2 - d * min x (1 - x)) := by
  unfold v12TwoParamTail v12TwoParamGap
  ring

theorem v12TwoParam_scaled_ratio_eq_simplified
    (d x : ℝ)
    (hd : d ≠ 0)
    (hx : x ≠ 0)
    (h1x : 1 - x ≠ 0) :
    v12TwoParamGlobal d x * v12TwoParamTail d x /
        v12TwoParamDefect d x =
      v12TwoParamSimplifiedRatio d x := by
  rw [v12TwoParam_global_factor, v12TwoParam_tail_factor]
  unfold v12TwoParamDefect v12TwoParamSimplifiedRatio
  field_simp [hd, hx, h1x]
  ring

theorem four_min_div_prod_eq_four_div_max
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    min x (1 - x) * 2 * 2 / (x * (1 - x)) =
      4 / max x (1 - x) := by
  have hxne : x ≠ 0 := ne_of_gt hx0
  have h1xpos : 0 < 1 - x := sub_pos.mpr hx1
  have h1xne : 1 - x ≠ 0 := ne_of_gt h1xpos
  by_cases h : x ≤ 1 - x
  · rw [min_eq_left h, max_eq_right h]
    field_simp [hxne, h1xne]
    ring
  · have h' : 1 - x ≤ x := le_of_not_ge h
    rw [min_eq_right h', max_eq_left h']
    field_simp [hxne, h1xne]
    ring

/-- Fixed-x interpolation limit for the continuous two-parameter family. -/
theorem v12TwoParamSimplifiedRatio_tendsto
    {α : Type*} {l : Filter α}
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (d : α → ℝ)
    (hd : Tendsto d l (𝓝 0)) :
    Tendsto
      (fun k => v12TwoParamSimplifiedRatio (d k) x)
      l (𝓝 (4 / max x (1 - x))) := by
  let m : ℝ := min x (1 - x)
  let q : ℝ := x * (1 - x)
  have hm :
      Tendsto (fun _ : α => m) l (𝓝 m) :=
    tendsto_const_nhds
  have hq :
      Tendsto (fun _ : α => q) l (𝓝 q) :=
    tendsto_const_nhds
  have htwo :
      Tendsto (fun _ : α => (2 : ℝ)) l (𝓝 2) :=
    tendsto_const_nhds
  have hfirst :
      Tendsto (fun k => 2 - d k * m) l (𝓝 2) := by
    simpa using htwo.sub (hd.mul hm)
  have hsecond :
      Tendsto
        (fun k => 2 - d k + q * d k)
        l (𝓝 2) := by
    have hqd : Tendsto (fun k => q * d k) l (𝓝 0) := by
      simpa using hq.mul hd
    simpa using (htwo.sub hd).add hqd
  have hprod :
      Tendsto
        (fun k => m * (2 - d k * m) *
          (2 - d k + q * d k))
        l (𝓝 (m * 2 * 2)) := by
    simpa using (hm.mul hfirst).mul hsecond
  have hdiv :
      Tendsto
        (fun k =>
          m * (2 - d k * m) *
            (2 - d k + q * d k) / q)
        l (𝓝 (m * 2 * 2 / q)) := by
    simpa using hprod.div_const q
  have htarget :=
    four_min_div_prod_eq_four_div_max x hx0 hx1
  have hfun :
      (fun k =>
        v12TwoParamSimplifiedRatio (d k) x) =
      (fun k =>
        m * (2 - d k * m) *
          (2 - d k + q * d k) / q) := by
    funext k
    rfl
  have hlim :
      m * 2 * 2 / q = 4 / max x (1 - x) := by
    simpa [m, q] using htarget
  rw [hfun, hlim]
  exact hdiv

end
end EverettianDecoherence.Approximation

import Mathlib.Analysis.InnerProductSpace.Basic

/-!
**FR.** Lemme analytique élémentaire pour la normalisation utilisée dans la
stabilité T5. Si un résidu q satisfait un contrôle quadratique
||q||^2 ≤ p r et a composante réelle r le long d'un vecteur unitaire v,
alors sa version normalisée est à distance quadratique au plus
2 (p-r) de sqrt p * v.

**EN.** Elementary analytic lemma for the normalization used in T5
stability. If a residual vector q satisfies ||q||^2 ≤ p r and has
real component r along a unit vector v, then its normalized version is
within squared distance 2 (p-r) of sqrt p * v.
-/

namespace EverettianDecoherence.Metrics

open scoped InnerProductSpace ComplexConjugate

noncomputable section

/-- Normalized residual stability with the sharp elementary constant 2. -/
theorem normalized_residual_close
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v q : E) (p r : ℝ)
    (hv : ‖v‖ = 1)
    (hr : 0 < r) (hrp : r ≤ p)
    (hq : ‖q‖ ^ 2 ≤ p * r)
    (hinner : RCLike.re (inner ℂ v q) = r) :
    ‖(((Real.sqrt r : ℝ) : ℂ)⁻¹ • q) -
        (((Real.sqrt p : ℝ) : ℂ) • v)‖ ^ 2 ≤
      2 * (p - r) := by
  have hr0 : 0 ≤ r := hr.le
  have hp0 : 0 ≤ p := hr0.trans hrp
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hsr0 : Real.sqrt r ≠ 0 := ne_of_gt hsr
  have hsp0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have hspr : r ≤ Real.sqrt p * Real.sqrt r := by
    have hsqrt_mono : Real.sqrt r ≤ Real.sqrt p :=
      Real.sqrt_le_sqrt hrp
    nlinarith [Real.sq_sqrt hr0, Real.sq_sqrt hp0]
  have hnormq :
      ‖(((Real.sqrt r : ℝ) : ℂ)⁻¹ • q)‖ ^ 2 ≤ p := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hsr]
    have hcalc :
        ((Real.sqrt r)⁻¹ * ‖q‖) ^ 2 = ‖q‖ ^ 2 / r := by
      field_simp [hsr0]
      nlinarith [Real.sq_sqrt hr0]
    rw [hcalc]
    exact (div_le_iff₀ hr).2 (by simpa [mul_comm] using hq)
  have hnormv :
      ‖(((Real.sqrt p : ℝ) : ℂ) • v)‖ ^ 2 = p := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hsp0, hv, mul_one, Real.sq_sqrt hp0]
  have hrev : RCLike.re (inner ℂ q v) = r := by
    rw [inner_re_symm]
    exact hinner
  have hscalar :
      star (((Real.sqrt r : ℝ) : ℂ)⁻¹) *
          (((Real.sqrt p : ℝ) : ℂ) * inner ℂ q v) =
        (((Real.sqrt p / Real.sqrt r : ℝ) : ℂ) * inner ℂ q v) := by
    simp only [map_inv₀, RCLike.conj_ofReal]
    rw [← Complex.ofReal_inv]
    field_simp [hsr0]
    ring
  have hcross :
      RCLike.re
        (inner ℂ
          (((Real.sqrt r : ℝ) : ℂ)⁻¹ • q)
          (((Real.sqrt p : ℝ) : ℂ) • v)) =
        (Real.sqrt p / Real.sqrt r) * r := by
    rw [inner_smul_left, inner_smul_right, hscalar,
      RCLike.re_ofReal_mul, hrev]
  calc
    ‖(((Real.sqrt r : ℝ) : ℂ)⁻¹ • q) -
        (((Real.sqrt p : ℝ) : ℂ) • v)‖ ^ 2
        = ‖(((Real.sqrt r : ℝ) : ℂ)⁻¹ • q)‖ ^ 2 -
            2 * RCLike.re
              (inner ℂ
                (((Real.sqrt r : ℝ) : ℂ)⁻¹ • q)
                (((Real.sqrt p : ℝ) : ℂ) • v)) +
            ‖(((Real.sqrt p : ℝ) : ℂ) • v)‖ ^ 2 := by
              rw [norm_sub_sq (𝕜 := ℂ)]
    _ ≤ p - 2 * ((Real.sqrt p / Real.sqrt r) * r) + p := by
      rw [hnormv, hcross]
      linarith
    _ = 2 * p - 2 * (Real.sqrt p * Real.sqrt r) := by
      field_simp [hsr0]
      nlinarith [Real.sq_sqrt hr0]
    _ ≤ 2 * (p - r) := by
      nlinarith

end
end EverettianDecoherence.Metrics

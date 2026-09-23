import EverettianDecoherence.Metrics.NormalizedResidualStability

/-!
**FR.** Forme à rapport du lemme de normalisation. Sous les hypothèses
résiduelles usuelles, l'erreur quadratique est contrôlée par
  (p / r) (p - r).
Cette forme tend vers la constante 1 lorsque r/p tend vers 1 et sert au
seuil adaptatif de la preuve v12.

**EN.** Ratio form of normalized residual stability. Under the usual
residual hypotheses, the squared error is bounded by
  (p / r) (p - r).
The coefficient tends to 1 when r/p tends to 1 and is used by the adaptive
threshold in the v12 proof.
-/

namespace EverettianDecoherence.Metrics

open scoped InnerProductSpace ComplexConjugate

noncomputable section

theorem normalized_residual_close_ratio
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v q : E) (p r : ℝ)
    (hv : ‖v‖ = 1)
    (hr : 0 < r) (hrp : r ≤ p)
    (hq : ‖q‖ ^ 2 ≤ p * r)
    (hinner : RCLike.re (inner ℂ v q) = r) :
    ‖(((Real.sqrt r : ℝ) : ℂ)⁻¹ • q) -
        (((Real.sqrt p : ℝ) : ℂ) • v)‖ ^ 2 ≤
      (p / r) * (p - r) := by
  have hr0 : 0 ≤ r := hr.le
  have hp0 : 0 ≤ p := hr0.trans hrp
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hsr0 : Real.sqrt r ≠ 0 := ne_of_gt hsr
  have hsp0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
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
  have hstarReal :
      star (((Real.sqrt r : ℝ) : ℂ)) =
        (((Real.sqrt r : ℝ) : ℂ)) := by
    simpa [Complex.star_def] using
      (Complex.conj_ofReal (Real.sqrt r))
  have hstarInv :
      star (((Real.sqrt r : ℝ) : ℂ)⁻¹) =
        (((Real.sqrt r)⁻¹ : ℝ) : ℂ) := by
    rw [star_inv₀, hstarReal, ← Complex.ofReal_inv]
  have hcoef :
      (Real.sqrt r)⁻¹ * Real.sqrt p =
        Real.sqrt p / Real.sqrt r := by
    field_simp [hsr0]
  have hscalar :
      star (((Real.sqrt r : ℝ) : ℂ)⁻¹) *
          (((Real.sqrt p : ℝ) : ℂ) * inner ℂ q v) =
        (((Real.sqrt p / Real.sqrt r : ℝ) : ℂ) * inner ℂ q v) := by
    rw [hstarInv, ← mul_assoc, ← Complex.ofReal_mul, hcoef]
  have hcross :
      RCLike.re
        (inner ℂ
          (((Real.sqrt r : ℝ) : ℂ)⁻¹ • q)
          (((Real.sqrt p : ℝ) : ℂ) • v)) =
        (Real.sqrt p / Real.sqrt r) * r := by
    rw [inner_smul_left, inner_smul_right]
    change RCLike.re
      (star (((Real.sqrt r : ℝ) : ℂ)⁻¹) *
        (((Real.sqrt p : ℝ) : ℂ) * inner ℂ q v)) =
      (Real.sqrt p / Real.sqrt r) * r
    rw [hscalar]
    change Complex.re
      (((Real.sqrt p / Real.sqrt r : ℝ) : ℂ) * inner ℂ q v) =
        (Real.sqrt p / Real.sqrt r) * r
    rw [Complex.re_ofReal_mul]
    have hrev' : Complex.re (inner ℂ q v) = r := by
      simpa using hrev
    rw [hrev']
  have hbasic :
      ‖(((Real.sqrt r : ℝ) : ℂ)⁻¹ • q) -
          (((Real.sqrt p : ℝ) : ℂ) • v)‖ ^ 2 ≤
        2 * p - 2 * (Real.sqrt p * Real.sqrt r) := by
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
  have hsqrt_le : Real.sqrt r ≤ Real.sqrt p :=
    Real.sqrt_le_sqrt hrp
  have hfactor :
      0 ≤
        Real.sqrt p *
          (Real.sqrt p - Real.sqrt r) ^ 2 *
          (Real.sqrt p + 2 * Real.sqrt r) := by
    positivity
  have hmul :
      r * (2 * p - 2 * (Real.sqrt p * Real.sqrt r)) ≤
        p * (p - r) := by
    nlinarith [Real.sq_sqrt hp0, Real.sq_sqrt hr0, hfactor]
  have hratio :
      2 * p - 2 * (Real.sqrt p * Real.sqrt r) ≤
        (p / r) * (p - r) := by
    calc
      2 * p - 2 * (Real.sqrt p * Real.sqrt r) ≤
          (p * (p - r)) / r := by
        apply (le_div_iff₀ hr).2
        calc
          (2 * p - 2 * (Real.sqrt p * Real.sqrt r)) * r
              = r * (2 * p - 2 * (Real.sqrt p * Real.sqrt r)) := by ring
          _ ≤ p * (p - r) := hmul
      _ = (p / r) * (p - r) := by ring
  exact hbasic.trans hratio

end
end EverettianDecoherence.Metrics

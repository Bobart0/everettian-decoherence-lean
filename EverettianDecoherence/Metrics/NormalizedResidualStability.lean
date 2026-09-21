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


/-- Sharper normalized residual estimate on a good cell. Under the additional
half-mass condition p/2 <= r, the squared normalized error is at most
(47/40)(p-r). The rational coefficient 47/40 is a convenient strict upper
bound for the optimal 4 - 2*sqrt 2. -/
theorem normalized_residual_close_good_47_40
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v q : E) (p r : ℝ)
    (hv : ‖v‖ = 1)
    (hr : 0 < r) (hrp : r ≤ p) (hhalf : p / 2 ≤ r)
    (hq : ‖q‖ ^ 2 ≤ p * r)
    (hinner : RCLike.re (inner ℂ v q) = r) :
    ‖(((Real.sqrt r : ℝ) : ℂ)⁻¹ • q) -
        (((Real.sqrt p : ℝ) : ℂ) • v)‖ ^ 2 ≤
      (47 / 40 : ℝ) * (p - r) := by
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
  have hcoef_sqrt :
      33 * Real.sqrt p ≤ 47 * Real.sqrt r := by
    have hsq :
        (33 * Real.sqrt p) ^ 2 ≤ (47 * Real.sqrt r) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hp0, Real.sq_sqrt hr0]
      nlinarith
    exact
      (sq_le_sq₀
        (mul_nonneg (by norm_num) hsp0)
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg r))).1 hsq
  have hprod :
      0 ≤
        (Real.sqrt p - Real.sqrt r) *
          (47 * Real.sqrt r - 33 * Real.sqrt p) :=
    mul_nonneg (sub_nonneg.mpr hsqrt_le) (sub_nonneg.mpr hcoef_sqrt)
  have htarget :
      33 * p + 47 * r ≤
        80 * (Real.sqrt p * Real.sqrt r) := by
    nlinarith [Real.sq_sqrt hp0, Real.sq_sqrt hr0]
  calc
    ‖(((Real.sqrt r : ℝ) : ℂ)⁻¹ • q) -
        (((Real.sqrt p : ℝ) : ℂ) • v)‖ ^ 2
        ≤ 2 * p - 2 * (Real.sqrt p * Real.sqrt r) := hbasic
    _ ≤ (47 / 40 : ℝ) * (p - r) := by
      nlinarith


end
end EverettianDecoherence.Metrics

import EverettianDecoherence.Metrics.DimensionFreeSharpness.PellFamily

/-!
**FR.** Couche de calcul exact de T2. Elle fixe la perspective binaire, calcule
les projections et le profil `recordProfileL1` de la famille rationnelle.
Cette couche est **BORN-SENSITIVE**.

**EN.** Exact-calculation layer for T2. It fixes the binary perspective and
computes the projections and `recordProfileL1` profile of the rational family.
This layer is **BORN-SENSITIVE**.
-/

namespace EverettianDecoherence.Metrics

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open scoped BigOperators Classical InnerProductSpace

noncomputable section

theorem sharpnessLine_ne_orthogonal :
    sharpnessLine ≠ sharpnessLineᗮ := by
  intro h
  apply sharpnessLine_ne_bot
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hx' : x ∈ sharpnessLineᗮ := h ▸ hx
  rw [Submodule.mem_orthogonal] at hx'
  exact inner_self_eq_zero.mp (hx' x hx)

theorem sharpnessE0_inner_X (n : ℕ) :
    (⟪sharpnessE0, sharpnessX n⟫_ℂ) = (sharpnessA n : ℂ) := by
  unfold sharpnessX
  rw [inner_add_right, inner_smul_right, inner_smul_right,
    sharpnessE0_inner_self, sharpnessE0_inner_E1]
  simp

theorem sharpnessE0_inner_Y (n : ℕ) :
    (⟪sharpnessE0, sharpnessY n⟫_ℂ) = (sharpnessB n : ℂ) := by
  unfold sharpnessY
  rw [inner_add_right, inner_smul_right, inner_smul_right,
    sharpnessE0_inner_self, sharpnessE0_inner_E1]
  simp

theorem sharpnessLine_proj_X (n : ℕ) :
    projL sharpnessLine (sharpnessX n) =
      (sharpnessA n : ℂ) • sharpnessE0 := by
  change sharpnessLine.starProjection (sharpnessX n) = _
  unfold sharpnessLine
  rw [Submodule.starProjection_unit_singleton ℂ sharpnessE0_norm,
    sharpnessE0_inner_X]

theorem sharpnessLine_proj_Y (n : ℕ) :
    projL sharpnessLine (sharpnessY n) =
      (sharpnessB n : ℂ) • sharpnessE0 := by
  change sharpnessLine.starProjection (sharpnessY n) = _
  unfold sharpnessLine
  rw [Submodule.starProjection_unit_singleton ℂ sharpnessE0_norm,
    sharpnessE0_inner_Y]

theorem sharpnessOrthogonal_proj_X (n : ℕ) :
    projL sharpnessLineᗮ (sharpnessX n) =
      (sharpnessB n : ℂ) • sharpnessE1 := by
  change sharpnessLineᗮ.starProjection (sharpnessX n) = _
  rw [Submodule.starProjection_orthogonal_val]
  change sharpnessX n - projL sharpnessLine (sharpnessX n) = _
  rw [sharpnessLine_proj_X]
  unfold sharpnessX
  abel

theorem sharpnessOrthogonal_proj_Y (n : ℕ) :
    projL sharpnessLineᗮ (sharpnessY n) =
      (sharpnessA n : ℂ) • sharpnessE1 := by
  change sharpnessLineᗮ.starProjection (sharpnessY n) = _
  rw [Submodule.starProjection_orthogonal_val]
  change sharpnessY n - projL sharpnessLine (sharpnessY n) = _
  rw [sharpnessLine_proj_Y]
  unfold sharpnessY
  abel

theorem sharpnessLine_weight_X (n : ℕ) :
    ‖projL sharpnessLine (sharpnessX n)‖ ^ 2 = sharpnessA n ^ 2 := by
  rw [sharpnessLine_proj_X, norm_smul, sharpnessE0_norm, mul_one]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sharpnessA_nonneg n)]

theorem sharpnessLine_weight_Y (n : ℕ) :
    ‖projL sharpnessLine (sharpnessY n)‖ ^ 2 = sharpnessB n ^ 2 := by
  rw [sharpnessLine_proj_Y, norm_smul, sharpnessE0_norm, mul_one]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sharpnessB_nonneg n)]

theorem sharpnessOrthogonal_weight_X (n : ℕ) :
    ‖projL sharpnessLineᗮ (sharpnessX n)‖ ^ 2 = sharpnessB n ^ 2 := by
  rw [sharpnessOrthogonal_proj_X, norm_smul, sharpnessE1_norm, mul_one]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sharpnessB_nonneg n)]

theorem sharpnessOrthogonal_weight_Y (n : ℕ) :
    ‖projL sharpnessLineᗮ (sharpnessY n)‖ ^ 2 = sharpnessA n ^ 2 := by
  rw [sharpnessOrthogonal_proj_Y, norm_smul, sharpnessE1_norm, mul_one]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sharpnessA_nonneg n)]


end
end EverettianDecoherence.Metrics

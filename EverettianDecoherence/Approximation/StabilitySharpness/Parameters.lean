import EverettianDecoherence.Approximation.IterationSharpness.RotationParameters

/-!
**FR.** Paramètres de la famille C3 destinée à tester l'optimalité en échelle
du théorème de stabilité. On recycle les amplitudes Pell a_n,b_n de T2 et on
les tourne de 45 degrés:
  A_n = (a_n+b_n)/sqrt(2),
  B_n = (a_n-b_n)/sqrt(2).
Ainsi A_n^2+B_n^2=1 et B_n est explicitement petit, égal à
1/(sqrt(2) q_n). Un second indice utilisera les paramètres de rotation
c_m,s_m de T3.

**EN.** Parameters of the C3 family used to test scale-optimality of the
stability theorem. We recycle the Pell amplitudes a_n,b_n from T2 and rotate
them by 45 degrees. Thus A_n^2+B_n^2=1 and B_n is explicitly small,
1/(sqrt(2) q_n). A second index will use the T3 rotation parameters c_m,s_m.
-/

namespace EverettianDecoherence.Approximation

open EverettianDecoherence.Metrics
open Filter
open scoped Topology

noncomputable section

def stabilitySharpnessA (n : ℕ) : ℝ :=
  (sharpnessA n + sharpnessB n) / Real.sqrt 2

def stabilitySharpnessB (n : ℕ) : ℝ :=
  (sharpnessA n - sharpnessB n) / Real.sqrt 2

theorem stabilitySharpness_sqrt_two_pos :
    0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem stabilitySharpness_sqrt_two_ne :
    Real.sqrt (2 : ℝ) ≠ 0 :=
  ne_of_gt stabilitySharpness_sqrt_two_pos

theorem stabilitySharpness_sqrt_two_sq :
    Real.sqrt (2 : ℝ) ^ 2 = 2 :=
  Real.sq_sqrt (by norm_num)

theorem stabilitySharpnessA_sq_add_B_sq (n : ℕ) :
    stabilitySharpnessA n ^ 2 + stabilitySharpnessB n ^ 2 = 1 := by
  unfold stabilitySharpnessA stabilitySharpnessB
  have hab := sharpnessA_sq_add_B_sq n
  have hs := stabilitySharpness_sqrt_two_sq
  field_simp [stabilitySharpness_sqrt_two_ne]
  nlinarith

theorem stabilitySharpnessA_eq_P_div (n : ℕ) :
    stabilitySharpnessA n =
      (sharpnessP n : ℝ) /
        (Real.sqrt 2 * (sharpnessQ n : ℝ)) := by
  unfold stabilitySharpnessA
  rw [sharpnessA_add_B]
  have hq : (sharpnessQ n : ℝ) ≠ 0 :=
    ne_of_gt (sharpnessQ_real_pos n)
  field_simp [hq, stabilitySharpness_sqrt_two_ne]

theorem stabilitySharpnessB_eq_inv (n : ℕ) :
    stabilitySharpnessB n =
      1 / (Real.sqrt 2 * (sharpnessQ n : ℝ)) := by
  unfold stabilitySharpnessB
  rw [sharpnessA_sub_B]
  have hq : (sharpnessQ n : ℝ) ≠ 0 :=
    ne_of_gt (sharpnessQ_real_pos n)
  field_simp [hq, stabilitySharpness_sqrt_two_ne]

theorem stabilitySharpnessA_nonneg (n : ℕ) :
    0 ≤ stabilitySharpnessA n := by
  rw [stabilitySharpnessA_eq_P_div]
  exact div_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (stabilitySharpness_sqrt_two_pos.le)
      (sharpnessQ_real_pos n).le)

theorem stabilitySharpnessB_pos (n : ℕ) :
    0 < stabilitySharpnessB n := by
  rw [stabilitySharpnessB_eq_inv]
  exact one_div_pos.mpr
    (mul_pos stabilitySharpness_sqrt_two_pos
      (sharpnessQ_real_pos n))

theorem stabilitySharpnessB_nonneg (n : ℕ) :
    0 ≤ stabilitySharpnessB n :=
  (stabilitySharpnessB_pos n).le

/-- The Pell q-coordinate itself grows at least geometrically by factor 3. -/
theorem sharpnessQ_geometric_step_for_stability (n : ℕ) :
    (3 : ℝ) * (sharpnessQ n : ℝ) ≤ (sharpnessQ (n + 1) : ℝ) := by
  rw [sharpnessQ_succ]
  norm_cast
  omega

theorem sharpnessQ_tendsto_atTop_for_stability :
    Tendsto (fun n : ℕ => (sharpnessQ n : ℝ)) atTop atTop := by
  exact tendsto_atTop_of_geom_le
    (by norm_num) (by norm_num)
    sharpnessQ_geometric_step_for_stability

/-- The spreading parameter B_n tends to zero. -/
theorem stabilitySharpnessB_tendsto_zero :
    Tendsto stabilitySharpnessB atTop (𝓝 0) := by
  have hden :
      Tendsto
        (fun n : ℕ => Real.sqrt 2 * (sharpnessQ n : ℝ))
        atTop atTop := by
    exact (tendsto_const_mul_atTop_of_pos
      stabilitySharpness_sqrt_two_pos).2
      sharpnessQ_tendsto_atTop_for_stability
  have hinv :
      Tendsto
        (fun n : ℕ =>
          (Real.sqrt 2 * (sharpnessQ n : ℝ))⁻¹)
        atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hfun :
      stabilitySharpnessB =
        fun n : ℕ => (Real.sqrt 2 * (sharpnessQ n : ℝ))⁻¹ := by
    funext n
    rw [stabilitySharpnessB_eq_inv]
    simp [one_div]
  rw [hfun]
  exact hinv

end
end EverettianDecoherence.Approximation

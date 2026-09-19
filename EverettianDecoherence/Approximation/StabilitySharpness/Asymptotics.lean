import EverettianDecoherence.Approximation.StabilitySharpness.TopTwoTail

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open Filter
open scoped Classical BigOperators Topology

noncomputable section

theorem stabilitySharpnessB_sq_tendsto_zero :
    Tendsto (fun n : ℕ => stabilitySharpnessB n ^ 2) atTop (𝓝 0) := by
  have h :=
    stabilitySharpnessB_tendsto_zero.mul
      stabilitySharpnessB_tendsto_zero
  simpa [pow_two] using h

theorem stabilitySharpnessA_sq_tendsto_one :
    Tendsto (fun n : ℕ => stabilitySharpnessA n ^ 2) atTop (𝓝 1) := by
  have hB := stabilitySharpnessB_sq_tendsto_zero
  have h :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hB
  have hfun :
      (fun n : ℕ => stabilitySharpnessA n ^ 2) =
        fun n : ℕ => 1 - stabilitySharpnessB n ^ 2 := by
    funext n
    nlinarith [stabilitySharpnessA_sq_add_B_sq n]
  rw [hfun]
  simpa using h

/-- For fixed rotation parameter m, the eta-normalized top-two tail tends to
the reciprocal angular defect 1/d_m. -/
theorem stabilitySharpnessTau_div_Eta_tendsto_inv_D (m : ℕ) :
    Tendsto
      (fun n : ℕ =>
        stabilitySharpnessTau n m / stabilitySharpnessEta n m)
      atTop (𝓝 (1 / stabilitySharpnessD m)) := by
  have hB := stabilitySharpnessB_sq_tendsto_zero
  have hA := stabilitySharpnessA_sq_tendsto_one
  have hnum :
      Tendsto
        (fun n : ℕ =>
          2 - stabilitySharpnessD m * stabilitySharpnessB n ^ 2)
        atTop (𝓝 2) := by
    have hmul :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => stabilitySharpnessD m)
          atTop (𝓝 (stabilitySharpnessD m))).mul hB
    have hsub :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).sub hmul
    simpa using hsub
  have hden :
      Tendsto
        (fun n : ℕ =>
          2 * stabilitySharpnessD m * stabilitySharpnessA n ^ 2)
        atTop (𝓝 (2 * stabilitySharpnessD m)) := by
    have hmul :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => 2 * stabilitySharpnessD m)
          atTop (𝓝 (2 * stabilitySharpnessD m))).mul hA
    simpa [mul_assoc] using hmul
  have hdiv :=
    hnum.div hden
      (mul_ne_zero (by norm_num)
        (ne_of_gt (stabilitySharpnessD_pos m)))
  have hlimit :
      (2 : ℝ) / (2 * stabilitySharpnessD m) =
        1 / stabilitySharpnessD m := by
    field_simp [ne_of_gt (stabilitySharpnessD_pos m)]
  rw [hlimit] at hdiv
  have hfun :
      (fun n : ℕ =>
        stabilitySharpnessTau n m / stabilitySharpnessEta n m) =
      fun n : ℕ =>
        (2 - stabilitySharpnessD m * stabilitySharpnessB n ^ 2) /
          (2 * stabilitySharpnessD m * stabilitySharpnessA n ^ 2) := by
    funext n
    exact stabilitySharpnessTau_div_Eta_exact n m
  rw [hfun]
  exact hdiv

/-- For fixed m, the full squared commutator defect tends to 2 s_m^2 as the
spreading parameter B_n tends to zero. -/
theorem stabilitySharpness_delta_sq_tendsto_two_s_sq (m : ℕ) :
    Tendsto
      (fun n : ℕ =>
        operatorNormProjectorCommutatorL2 stabilitySharpnessPerspective3
          (stabilitySharpnessRotation n m) ^ 2)
      atTop (𝓝 (2 * iterationSharpnessS m ^ 2)) := by
  have hA := stabilitySharpnessA_sq_tendsto_one
  have hB := stabilitySharpnessB_sq_tendsto_zero
  have hAB :
      Tendsto
        (fun n : ℕ =>
          stabilitySharpnessA n ^ 2 * stabilitySharpnessB n ^ 2)
        atTop (𝓝 0) := by
    have h := hA.mul hB
    simpa using h
  have hextra :
      Tendsto
        (fun n : ℕ =>
          2 * stabilitySharpnessD m ^ 2 *
            (stabilitySharpnessA n ^ 2 * stabilitySharpnessB n ^ 2))
        atTop (𝓝 0) := by
    have h :=
      (tendsto_const_nhds :
        Tendsto
          (fun _ : ℕ => 2 * stabilitySharpnessD m ^ 2)
          atTop (𝓝 (2 * stabilitySharpnessD m ^ 2))).mul hAB
    simpa using h
  have hsum :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => 2 * iterationSharpnessS m ^ 2)
        atTop (𝓝 (2 * iterationSharpnessS m ^ 2))).add hextra
  have hfun :
      (fun n : ℕ =>
        operatorNormProjectorCommutatorL2 stabilitySharpnessPerspective3
          (stabilitySharpnessRotation n m) ^ 2) =
      fun n : ℕ =>
        2 * iterationSharpnessS m ^ 2 +
          2 * stabilitySharpnessD m ^ 2 *
            (stabilitySharpnessA n ^ 2 * stabilitySharpnessB n ^ 2) := by
    funext n
    rw [stabilitySharpness_globalSq]
    ring
  rw [hfun]
  simpa using hsum

/-- Fixed-m scale-obstruction limit after n -> infinity. -/
noncomputable def stabilitySharpnessScaleLimit (m : ℕ) : ℝ :=
  2 * iterationSharpnessS m ^ 2 / stabilitySharpnessD m

theorem stabilitySharpness_scaled_ratio_tendsto_scaleLimit (m : ℕ) :
    Tendsto
      (fun n : ℕ =>
        (stabilitySharpnessTau n m / stabilitySharpnessEta n m) *
          operatorNormProjectorCommutatorL2 stabilitySharpnessPerspective3
            (stabilitySharpnessRotation n m) ^ 2)
      atTop (𝓝 (stabilitySharpnessScaleLimit m)) := by
  have hratio := stabilitySharpnessTau_div_Eta_tendsto_inv_D m
  have hdelta := stabilitySharpness_delta_sq_tendsto_two_s_sq m
  have hprod := hratio.mul hdelta
  unfold stabilitySharpnessScaleLimit
  have hD : stabilitySharpnessD m ≠ 0 :=
    ne_of_gt (stabilitySharpnessD_pos m)
  convert hprod using 1
  · ext n
    rfl
  · field_simp [hD]
    ring

theorem stabilitySharpnessD_tendsto_zero :
    Tendsto stabilitySharpnessD atTop (𝓝 0) := by
  have h :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
        iterationSharpnessC_tendsto_one
  simpa [stabilitySharpnessD] using h

theorem stabilitySharpnessScaleLimit_eq_four_sub_two_D (m : ℕ) :
    stabilitySharpnessScaleLimit m =
      4 - 2 * stabilitySharpnessD m := by
  unfold stabilitySharpnessScaleLimit
  have hCS := iterationSharpnessC_sq_add_S_sq m
  have hD : stabilitySharpnessD m ≠ 0 :=
    ne_of_gt (stabilitySharpnessD_pos m)
  have hsD :
      iterationSharpnessS m ^ 2 =
        2 * stabilitySharpnessD m - stabilitySharpnessD m ^ 2 := by
    unfold stabilitySharpnessD
    nlinarith
  rw [hsD]
  field_simp [hD]
  ring

/-- Sharp scale obstruction: in the iterated regime n -> infinity followed by
m -> infinity, (tau/eta) * delta^2 tends to 4. -/
theorem stabilitySharpnessScaleLimit_tendsto_four :
    Tendsto stabilitySharpnessScaleLimit atTop (𝓝 4) := by
  have h :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (𝓝 4)).sub
        ((tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul
            stabilitySharpnessD_tendsto_zero)
  have hfun :
      stabilitySharpnessScaleLimit =
        fun m : ℕ => 4 - 2 * stabilitySharpnessD m := by
    funext m
    exact stabilitySharpnessScaleLimit_eq_four_sub_two_D m
  rw [hfun]
  simpa using h

end
end EverettianDecoherence.Approximation

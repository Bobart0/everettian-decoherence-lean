import EverettianDecoherence.Approximation.StabilitySharpness.Asymptotics
import EverettianDecoherence.Approximation.StabilitySharpness.TopTwoTail

/-!
**FR.** Spécialisations v12 de la famille C3 existante. Le chemin symétrique
n=0 réalise la constante asymptotique 8. La diagonale n=m est ultra-near,
avec eta/delta^2 -> 0, et réalise la constante 4.

**EN.** v12 specializations of the existing C3 family. The symmetric path
n=0 attains the asymptotic constant 8. The diagonal path n=m is ultra-near,
with eta/delta^2 -> 0, and attains the constant 4.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open Filter
open scoped Classical BigOperators Topology

noncomputable section

theorem stabilitySharpnessD_eq_inv_Q_sq (m : ℕ) :
    stabilitySharpnessD m =
      1 / (sharpnessQ m : ℝ) ^ 2 := by
  have hab := sharpnessA_sq_add_B_sq m
  have hdiff := sharpnessA_sub_B m
  unfold stabilitySharpnessD iterationSharpnessC
  calc
    1 - 2 * sharpnessA m * sharpnessB m =
        (sharpnessA m - sharpnessB m) ^ 2 := by
      nlinarith
    _ = (1 / (sharpnessQ m : ℝ)) ^ 2 := by rw [hdiff]
    _ = 1 / (sharpnessQ m : ℝ) ^ 2 := by ring

theorem stabilitySharpnessB_sq_eq_D_div_two (m : ℕ) :
    stabilitySharpnessB m ^ 2 = stabilitySharpnessD m / 2 := by
  rw [stabilitySharpnessB_eq_inv, stabilitySharpnessD_eq_inv_Q_sq]
  have hq : (sharpnessQ m : ℝ) ≠ 0 :=
    ne_of_gt (sharpnessQ_real_pos m)
  have hs := stabilitySharpness_sqrt_two_sq
  field_simp [hq, stabilitySharpness_sqrt_two_ne]
  nlinarith

theorem stabilitySharpnessA_sq_eq_one_sub_D_div_two (m : ℕ) :
    stabilitySharpnessA m ^ 2 = 1 - stabilitySharpnessD m / 2 := by
  have hab := stabilitySharpnessA_sq_add_B_sq m
  rw [stabilitySharpnessB_sq_eq_D_div_two] at hab
  linarith

theorem stabilitySharpnessD_zero : stabilitySharpnessD 0 = 1 := by
  norm_num [stabilitySharpnessD, iterationSharpnessC,
    sharpnessA, sharpnessB, sharpnessP, sharpnessQ,
    sharpnessPellPair]

theorem stabilitySharpnessA_zero_sq :
    stabilitySharpnessA 0 ^ 2 = 1 / 2 := by
  rw [stabilitySharpnessA_sq_eq_one_sub_D_div_two,
    stabilitySharpnessD_zero]
  norm_num

theorem stabilitySharpnessB_zero_sq :
    stabilitySharpnessB 0 ^ 2 = 1 / 2 := by
  rw [stabilitySharpnessB_sq_eq_D_div_two,
    stabilitySharpnessD_zero]

noncomputable def stabilitySharpnessScaledRatioV12 (n m : ℕ) : ℝ :=
  operatorNormProjectorCommutatorL2 stabilitySharpnessPerspective3
      (stabilitySharpnessRotation n m) ^ 2 *
    stabilitySharpnessTopTwoTail n m /
      stabilitySharpnessEta n m

theorem stabilitySharpnessScaledRatioV12_eq
    (n m : ℕ) :
    stabilitySharpnessScaledRatioV12 n m =
      ((2 - stabilitySharpnessD m * stabilitySharpnessB n ^ 2) /
        (2 * stabilitySharpnessD m * stabilitySharpnessA n ^ 2)) *
      (2 * iterationSharpnessS m ^ 2 +
        2 * stabilitySharpnessD m ^ 2 *
          stabilitySharpnessA n ^ 2 * stabilitySharpnessB n ^ 2) := by
  unfold stabilitySharpnessScaledRatioV12
  rw [stabilitySharpnessTopTwoTail_eq_Tau]
  have heta := stabilitySharpnessEta_pos n m
  have hetane : stabilitySharpnessEta n m ≠ 0 := ne_of_gt heta
  have hratio := stabilitySharpnessTau_div_Eta_exact n m
  rw [stabilitySharpness_globalSq]
  calc
    (2 * iterationSharpnessS m ^ 2 +
          2 * stabilitySharpnessD m ^ 2 *
            stabilitySharpnessA n ^ 2 * stabilitySharpnessB n ^ 2) *
        stabilitySharpnessTau n m / stabilitySharpnessEta n m =
      (stabilitySharpnessTau n m / stabilitySharpnessEta n m) *
        (2 * iterationSharpnessS m ^ 2 +
          2 * stabilitySharpnessD m ^ 2 *
            stabilitySharpnessA n ^ 2 * stabilitySharpnessB n ^ 2) := by
        field_simp [hetane]
    _ = _ := by rw [hratio]

private theorem iterationSharpnessS_sq_eq_two_D_sub_D_sq (m : ℕ) :
    iterationSharpnessS m ^ 2 =
      2 * stabilitySharpnessD m - stabilitySharpnessD m ^ 2 := by
  have hCS := iterationSharpnessC_sq_add_S_sq m
  unfold stabilitySharpnessD
  nlinarith

theorem stabilitySharpnessScaledRatioV12_zero_exact (m : ℕ) :
    stabilitySharpnessScaledRatioV12 0 m =
      8 - 5 * stabilitySharpnessD m +
        (3 / 4 : ℝ) * stabilitySharpnessD m ^ 2 := by
  rw [stabilitySharpnessScaledRatioV12_eq,
    stabilitySharpnessA_zero_sq, stabilitySharpnessB_zero_sq,
    iterationSharpnessS_sq_eq_two_D_sub_D_sq]
  have hD : stabilitySharpnessD m ≠ 0 :=
    ne_of_gt (stabilitySharpnessD_pos m)
  field_simp [hD]
  ring

/-- The symmetric path attains the general small-defect coefficient 8. -/
theorem stabilitySharpnessScaledRatioV12_zero_tendsto_eight :
    Tendsto (fun m : ℕ => stabilitySharpnessScaledRatioV12 0 m)
      atTop (𝓝 8) := by
  have hD := stabilitySharpnessD_tendsto_zero
  have hD2 := hD.mul hD
  have h :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (8 : ℝ)) atTop (𝓝 8)).sub
      ((tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (5 : ℝ)) atTop (𝓝 5)).mul hD)
  have h' :=
    h.add
      ((tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (3 / 4 : ℝ)) atTop (𝓝 (3 / 4))).mul hD2)
  convert h' using 1 <;>
    simp [stabilitySharpnessScaledRatioV12_zero_exact, pow_two]

theorem stabilitySharpnessScaledRatioV12_diag_exact (m : ℕ) :
    stabilitySharpnessScaledRatioV12 m m =
      4 - stabilitySharpnessD m ^ 4 / 4 := by
  rw [stabilitySharpnessScaledRatioV12_eq,
    stabilitySharpnessA_sq_eq_one_sub_D_div_two,
    stabilitySharpnessB_sq_eq_D_div_two,
    iterationSharpnessS_sq_eq_two_D_sub_D_sq]
  have hD : stabilitySharpnessD m ≠ 0 :=
    ne_of_gt (stabilitySharpnessD_pos m)
  have hA : 0 < stabilitySharpnessA m :=
    stabilitySharpnessA_pos m
  have hA2 : 0 < stabilitySharpnessA m ^ 2 := sq_pos_of_pos hA
  have hden :
      1 - stabilitySharpnessD m / 2 ≠ 0 := by
    rw [← stabilitySharpnessA_sq_eq_one_sub_D_div_two]
    exact ne_of_gt hA2
  have h2D : 2 - stabilitySharpnessD m ≠ 0 := by
    intro h
    apply hden
    linarith
  field_simp [hD, hden, h2D]
  ring_nf

/-- The diagonal path attains coefficient 4. -/
theorem stabilitySharpnessScaledRatioV12_diag_tendsto_four :
    Tendsto (fun m : ℕ => stabilitySharpnessScaledRatioV12 m m)
      atTop (𝓝 4) := by
  have hD := stabilitySharpnessD_tendsto_zero
  have hD4 : Tendsto (fun m : ℕ => stabilitySharpnessD m ^ 4)
      atTop (𝓝 0) := by
    have h2 := hD.mul hD
    have h4 := h2.mul h2
    convert h4 using 1 <;> norm_num <;> ring
  have h :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (𝓝 4)).sub
      (hD4.div_const 4)
  convert h using 1 <;>
    simp [stabilitySharpnessScaledRatioV12_diag_exact]

theorem stabilitySharpnessEta_div_deltaSq_diag_exact (m : ℕ) :
    stabilitySharpnessEta m m /
        operatorNormProjectorCommutatorL2 stabilitySharpnessPerspective3
          (stabilitySharpnessRotation m m) ^ 2 =
      (2 * stabilitySharpnessD m) /
        ((2 - stabilitySharpnessD m) *
          (stabilitySharpnessD m ^ 2 + 4) ^ 2) := by
  rw [stabilitySharpnessEta_exact, stabilitySharpness_globalSq,
    stabilitySharpnessA_sq_eq_one_sub_D_div_two,
    stabilitySharpnessB_sq_eq_D_div_two,
    iterationSharpnessS_sq_eq_two_D_sub_D_sq]
  have hD : stabilitySharpnessD m ≠ 0 :=
    ne_of_gt (stabilitySharpnessD_pos m)
  have hdelta :=
    stabilitySharpness_delta_pos m m
  have hdeltane :
      operatorNormProjectorCommutatorL2 stabilitySharpnessPerspective3
        (stabilitySharpnessRotation m m) ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_pos hdelta)
  have hC0 := iterationSharpnessC_nonneg m
  have hDle : stabilitySharpnessD m ≤ 1 := by
    unfold stabilitySharpnessD
    linarith
  have h2D : 2 - stabilitySharpnessD m ≠ 0 := by
    nlinarith
  have hD4 : stabilitySharpnessD m ^ 2 + 4 ≠ 0 := by
    nlinarith [sq_nonneg (stabilitySharpnessD m)]
  field_simp [hD, hdeltane, h2D, hD4]
  ring

/-- The diagonal path is ultra-near: eta/delta^2 tends to zero. -/
theorem stabilitySharpnessEta_div_deltaSq_diag_tendsto_zero :
    Tendsto
      (fun m : ℕ =>
        stabilitySharpnessEta m m /
          operatorNormProjectorCommutatorL2 stabilitySharpnessPerspective3
            (stabilitySharpnessRotation m m) ^ 2)
      atTop (𝓝 0) := by
  have hD := stabilitySharpnessD_tendsto_zero
  have hD2 := hD.mul hD
  have hnum :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul hD
  have hleft :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).sub hD
  have hright0 :=
    hD2.add
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (𝓝 4))
  have hright := hright0.mul hright0
  have hden := hleft.mul hright
  have hden0 :
      (2 - (0 : ℝ)) *
        (((0 : ℝ) * 0 + 4) * ((0 : ℝ) * 0 + 4)) ≠ 0 := by
    norm_num
  have hdiv := hnum.div hden hden0
  have hfun :
      (fun m : ℕ =>
        stabilitySharpnessEta m m /
          operatorNormProjectorCommutatorL2 stabilitySharpnessPerspective3
            (stabilitySharpnessRotation m m) ^ 2) =
      fun m : ℕ =>
        (2 * stabilitySharpnessD m) /
          ((2 - stabilitySharpnessD m) *
            ((stabilitySharpnessD m ^ 2 + 4) ^ 2)) := by
    funext m
    exact stabilitySharpnessEta_div_deltaSq_diag_exact m
  rw [hfun]
  change
    Tendsto
      (fun m : ℕ =>
        (2 * stabilitySharpnessD m) /
          ((2 - stabilitySharpnessD m) *
            ((stabilitySharpnessD m * stabilitySharpnessD m + 4) *
              (stabilitySharpnessD m * stabilitySharpnessD m + 4))))
      atTop (𝓝 0) at hdiv
  simpa [pow_two] using hdiv

end
end EverettianDecoherence.Approximation

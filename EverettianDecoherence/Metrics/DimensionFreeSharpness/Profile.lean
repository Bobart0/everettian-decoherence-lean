import EverettianDecoherence.Metrics.DimensionFreeSharpness.ProjectionProfile

/-!
**FR.** Deuxième couche de calcul exact de T2 : profil L1 fermé et distance
entre les deux états rationnels. Cette couche reste **BORN-SENSITIVE**.

**EN.** Second exact-calculation layer for T2: closed L1 profile and distance
between the two rational states. This layer remains **BORN-SENSITIVE**.
-/

namespace EverettianDecoherence.Metrics

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open scoped BigOperators Classical InnerProductSpace

noncomputable section

private theorem sharpnessB_le_A (n : ℕ) : sharpnessB n ≤ sharpnessA n := by
  have hq : 0 < (1 : ℝ) / sharpnessQ n := by
    exact one_div_pos.mpr (sharpnessQ_real_pos n)
  nlinarith [sharpnessA_sub_B n]

private theorem sharpnessB_sq_le_A_sq (n : ℕ) :
    sharpnessB n ^ 2 ≤ sharpnessA n ^ 2 := by
  nlinarith [sharpnessA_nonneg n, sharpnessB_nonneg n, sharpnessB_le_A n]

/-- Exact binary-cell L1 profile of the swapped rational pair. -/
theorem sharpness_recordProfileL1 (n : ℕ) :
    recordProfileL1 sharpnessPerspective (sharpnessX n) (sharpnessY n) =
      2 * (sharpnessA n ^ 2 - sharpnessB n ^ 2) := by
  unfold recordProfileL1 finiteProfileL1 recordProfile
  change
    (∑ c : {c : Submodule ℂ (H 2) // c ∈ sharpnessPerspective.cells},
      |‖projL c.val (sharpnessX n)‖ ^ 2 -
        ‖projL c.val (sharpnessY n)‖ ^ 2|) = _
  calc
    (∑ c : {c : Submodule ℂ (H 2) // c ∈ sharpnessPerspective.cells},
      |‖projL c.val (sharpnessX n)‖ ^ 2 -
        ‖projL c.val (sharpnessY n)‖ ^ 2|) =
        ∑ c ∈ sharpnessPerspective.cells,
          |‖projL c (sharpnessX n)‖ ^ 2 -
            ‖projL c (sharpnessY n)‖ ^ 2| := by
      symm
      exact Finset.sum_subtype sharpnessPerspective.cells (fun c => Iff.rfl)
        (fun c => |‖projL c (sharpnessX n)‖ ^ 2 -
          ‖projL c (sharpnessY n)‖ ^ 2|)
    _ =
        |sharpnessA n ^ 2 - sharpnessB n ^ 2| +
          |sharpnessB n ^ 2 - sharpnessA n ^ 2| := by
      change
        (∑ c ∈ ({sharpnessLine, sharpnessLineᗮ} : Finset (Submodule ℂ (H 2))),
          |‖projL c (sharpnessX n)‖ ^ 2 -
            ‖projL c (sharpnessY n)‖ ^ 2|) = _
      rw [Finset.sum_insert (by simpa using sharpnessLine_ne_orthogonal),
        Finset.sum_singleton, sharpnessLine_weight_X, sharpnessLine_weight_Y,
        sharpnessOrthogonal_weight_X, sharpnessOrthogonal_weight_Y]
    _ = 2 * (sharpnessA n ^ 2 - sharpnessB n ^ 2) := by
      rw [abs_of_nonneg (sub_nonneg.mpr (sharpnessB_sq_le_A_sq n)),
        abs_of_nonpos (sub_nonpos.mpr (sharpnessB_sq_le_A_sq n))]
      ring

/-- Closed rational form of the L1 profile. -/
theorem sharpness_recordProfileL1_rational (n : ℕ) :
    recordProfileL1 sharpnessPerspective (sharpnessX n) (sharpnessY n) =
      2 * (sharpnessP n : ℝ) / (sharpnessQ n : ℝ) ^ 2 := by
  rw [sharpness_recordProfileL1]
  have hq : (sharpnessQ n : ℝ) ≠ 0 := ne_of_gt (sharpnessQ_real_pos n)
  have hdiff := sharpnessA_sub_B n
  have hsum := sharpnessA_add_B n
  have hfactor :
      sharpnessA n ^ 2 - sharpnessB n ^ 2 =
        (sharpnessA n - sharpnessB n) * (sharpnessA n + sharpnessB n) := by
    ring
  rw [hfactor, hdiff, hsum]
  field_simp [hq]

theorem sharpness_state_difference_sq (n : ℕ) :
    ‖sharpnessX n - sharpnessY n‖ ^ 2 =
      2 / (sharpnessQ n : ℝ) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  change
    ‖sharpnessX n (0 : Fin 2) - sharpnessY n (0 : Fin 2)‖ ^ 2 +
      ‖sharpnessX n (1 : Fin 2) - sharpnessY n (1 : Fin 2)‖ ^ 2 =
        2 / (sharpnessQ n : ℝ) ^ 2
  rw [sharpnessX_zero, sharpnessY_zero, sharpnessX_one, sharpnessY_one]
  rw [← Complex.ofReal_sub, ← Complex.ofReal_sub]
  have hd : 0 < sharpnessA n - sharpnessB n := by
    rw [sharpnessA_sub_B]
    exact one_div_pos.mpr (sharpnessQ_real_pos n)
  have hdn : sharpnessB n - sharpnessA n < 0 := by linarith
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hd, abs_of_neg hdn]
  have hba :
      sharpnessB n - sharpnessA n = -(1 / (sharpnessQ n : ℝ)) := by
    linarith [sharpnessA_sub_B n]
  rw [sharpnessA_sub_B, hba]
  have hq : (sharpnessQ n : ℝ) ≠ 0 := ne_of_gt (sharpnessQ_real_pos n)
  field_simp [hq]
  ring

theorem sharpness_state_difference_ne_zero (n : ℕ) :
    sharpnessX n - sharpnessY n ≠ 0 := by
  intro h
  have hsq := sharpness_state_difference_sq n
  rw [h, norm_zero] at hsq
  norm_num at hsq
  have hq : 0 < (sharpnessQ n : ℝ) ^ 2 :=
    sq_pos_of_pos (sharpnessQ_real_pos n)
  have hrhs : 0 < 2 / (sharpnessQ n : ℝ) ^ 2 := div_pos (by norm_num) hq
  linarith

theorem sharpness_state_distance_pos (n : ℕ) :
    0 < ‖sharpnessX n - sharpnessY n‖ :=
  norm_pos_iff.mpr (sharpness_state_difference_ne_zero n)

end
end EverettianDecoherence.Metrics
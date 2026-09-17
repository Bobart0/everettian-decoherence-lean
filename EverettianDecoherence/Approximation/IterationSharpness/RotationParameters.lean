import EverettianDecoherence.Metrics.DimensionFreeSharpness.PellFamily

/-!
**FR.** Première brique de T3. On réutilise uniquement les amplitudes
rationnelles `sharpnessA` et `sharpnessB` de T2 pour définir deux paramètres
algébriques
`cₙ = 2 aₙ bₙ` et `sₙ = aₙ² - bₙ²`.
Ils vérifient exactement `cₙ² + sₙ² = 1`. Le paramètre `sₙ` possède en outre
la forme rationnelle `pₙ / qₙ²`, qui sera utilisée pour le régime de petite
rotation. Ce module n'introduit ni temps, ni dynamique physique, ni
`bornRecord` supplémentaire.

**EN.** First T3 building block. We only reuse the rational amplitudes
`sharpnessA` and `sharpnessB` from T2 to define the algebraic parameters
`cₙ = 2 aₙ bₙ` and `sₙ = aₙ² - bₙ²`.
They satisfy the exact identity `cₙ² + sₙ² = 1`. Moreover `sₙ` has the exact
rational form `pₙ / qₙ²`, which will be used for the small-rotation regime.
This module introduces no time variable, physical dynamics, or additional
`bornRecord` use.
-/

namespace EverettianDecoherence.Approximation

open EverettianDecoherence.Metrics

noncomputable section

/-- Cosine-like algebraic parameter of the T3 rational rotation family. -/
def iterationSharpnessC (n : ℕ) : ℝ :=
  2 * sharpnessA n * sharpnessB n

/-- Sine-like algebraic parameter of the T3 rational rotation family. -/
def iterationSharpnessS (n : ℕ) : ℝ :=
  sharpnessA n ^ 2 - sharpnessB n ^ 2

/-- The two algebraic parameters lie exactly on the real unit circle. -/
theorem iterationSharpnessC_sq_add_S_sq (n : ℕ) :
    iterationSharpnessC n ^ 2 + iterationSharpnessS n ^ 2 = 1 := by
  unfold iterationSharpnessC iterationSharpnessS
  calc
    (2 * sharpnessA n * sharpnessB n) ^ 2 +
        (sharpnessA n ^ 2 - sharpnessB n ^ 2) ^ 2 =
      (sharpnessA n ^ 2 + sharpnessB n ^ 2) ^ 2 := by ring
    _ = 1 := by rw [sharpnessA_sq_add_B_sq]; norm_num

/-- Exact rational form of the sine-like parameter. -/
theorem iterationSharpnessS_eq_rational (n : ℕ) :
    iterationSharpnessS n =
      (sharpnessP n : ℝ) / (sharpnessQ n : ℝ) ^ 2 := by
  have hq : (sharpnessQ n : ℝ) ≠ 0 := ne_of_gt (sharpnessQ_real_pos n)
  unfold iterationSharpnessS
  calc
    sharpnessA n ^ 2 - sharpnessB n ^ 2 =
        (sharpnessA n - sharpnessB n) *
          (sharpnessA n + sharpnessB n) := by ring
    _ = (1 / (sharpnessQ n : ℝ)) *
          ((sharpnessP n : ℝ) / (sharpnessQ n : ℝ)) := by
      rw [sharpnessA_sub_B, sharpnessA_add_B]
    _ = (sharpnessP n : ℝ) / (sharpnessQ n : ℝ) ^ 2 := by
      field_simp [hq]

/-- The sine-like parameter is strictly positive for every family member. -/
theorem iterationSharpnessS_pos (n : ℕ) : 0 < iterationSharpnessS n := by
  rw [iterationSharpnessS_eq_rational]
  exact div_pos (by exact_mod_cast sharpnessP_pos n)
    (sq_pos_of_pos (sharpnessQ_real_pos n))

/-- The cosine-like parameter is nonnegative. -/
theorem iterationSharpnessC_nonneg (n : ℕ) : 0 ≤ iterationSharpnessC n := by
  unfold iterationSharpnessC
  exact mul_nonneg (mul_nonneg (by norm_num) (sharpnessA_nonneg n))
    (sharpnessB_nonneg n)

end
end EverettianDecoherence.Approximation

import EverettianDecoherence.Approximation.IterationSharpness
import EverettianDecoherence.Approximation.UniformRecordPreservation
import EverettianDecoherence.Metrics.DimensionFreeSharpness.Profile

/-!
**FR.** # T5A — barrière `sqrt 2` pour le transfert uniforme ED3B

Ce module ouvre un front transversal sans nouvelle couche physique. Il réutilise
exactement la famille rationnelle de T2 et la rotation de T3. Pour chaque `n`,
la rotation `iterationSharpnessRotation n` envoie l'état normalisé
`sharpnessX n = (a_n,b_n)` sur `sharpnessY n = (b_n,a_n)`. Le profil L1
BORN-SENSITIVE vaut alors exactement `2 s_n`, tandis que le défaut uniforme
NON BORN-SENSITIVE vaut `sqrt 2 * s_n`. Leur rapport est donc exactement
`sqrt 2` pour chaque membre de la famille.

Conséquence : la constante uniforme `2` d'ED3B ne peut pas être remplacée par
une constante strictement inférieure à `sqrt 2`. Ce résultat est seulement une
borne inférieure sur la meilleure constante universelle : il ne prouve pas que
`sqrt 2` est une borne supérieure hors de cette famille.

**EN.** # T5A — `sqrt 2` barrier for the ED3B uniform transfer

This module opens a transversal front without adding a new physical layer. It
reuses exactly the rational family from T2 and the T3 rotation. For every `n`,
`iterationSharpnessRotation n` maps the normalized state
`sharpnessX n = (a_n,b_n)` to `sharpnessY n = (b_n,a_n)`. The BORN-SENSITIVE
L1 profile is then exactly `2 s_n`, while the NON BORN-SENSITIVE uniform defect
is `sqrt 2 * s_n`. Their ratio is therefore exactly `sqrt 2` for every family
member.

Consequently, the uniform constant `2` in ED3B cannot be replaced by any
constant strictly below `sqrt 2`. This is only a lower bound on the best
universal constant: it does not prove that `sqrt 2` is a universal upper bound
outside this family.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical InnerProductSpace

noncomputable section

/-- The T3 rational rotation exactly swaps the two T2 sharpness amplitudes. -/
theorem iterationSharpnessRotation_sharpnessX_eq_sharpnessY (n : ℕ) :
    iterationSharpnessRotation n (sharpnessX n) = sharpnessY n := by
  ext i
  fin_cases i
  · change iterationSharpnessRotation n (sharpnessX n) (0 : Fin 2) =
      sharpnessY n (0 : Fin 2)
    rw [iterationSharpnessRotation_zero, sharpnessX_zero, sharpnessX_one,
      sharpnessY_zero]
    have hreal :
        iterationSharpnessC n * sharpnessA n -
            iterationSharpnessS n * sharpnessB n = sharpnessB n := by
      unfold iterationSharpnessC iterationSharpnessS
      calc
        2 * sharpnessA n * sharpnessB n * sharpnessA n -
            (sharpnessA n ^ 2 - sharpnessB n ^ 2) * sharpnessB n =
          sharpnessB n * (sharpnessA n ^ 2 + sharpnessB n ^ 2) := by ring
        _ = sharpnessB n := by rw [sharpnessA_sq_add_B_sq]; ring
    apply Complex.ext
    · simpa using hreal
    · simp
  · change iterationSharpnessRotation n (sharpnessX n) (1 : Fin 2) =
      sharpnessY n (1 : Fin 2)
    rw [iterationSharpnessRotation_one, sharpnessX_zero, sharpnessX_one,
      sharpnessY_one]
    have hreal :
        iterationSharpnessS n * sharpnessA n +
            iterationSharpnessC n * sharpnessB n = sharpnessA n := by
      unfold iterationSharpnessC iterationSharpnessS
      calc
        (sharpnessA n ^ 2 - sharpnessB n ^ 2) * sharpnessA n +
            2 * sharpnessA n * sharpnessB n * sharpnessB n =
          sharpnessA n * (sharpnessA n ^ 2 + sharpnessB n ^ 2) := by ring
        _ = sharpnessA n := by rw [sharpnessA_sq_add_B_sq]; ring
    apply Complex.ext
    · simpa using hreal
    · simp

/-- Exact BORN-SENSITIVE profile produced by the T2/T3 compatible family. -/
theorem uniformTransferSharpness_profile_exact (n : ℕ) :
    recordProfileL1 sharpnessPerspective
        (iterationSharpnessRotation n (sharpnessX n)) (sharpnessX n) =
      2 * iterationSharpnessS n := by
  calc
    recordProfileL1 sharpnessPerspective
        (iterationSharpnessRotation n (sharpnessX n)) (sharpnessX n) =
      recordProfileL1 sharpnessPerspective (sharpnessY n) (sharpnessX n) := by
        rw [iterationSharpnessRotation_sharpnessX_eq_sharpnessY]
    _ = recordProfileL1 sharpnessPerspective (sharpnessX n) (sharpnessY n) :=
      recordProfileL1_symm sharpnessPerspective (sharpnessY n) (sharpnessX n)
    _ = 2 * (sharpnessA n ^ 2 - sharpnessB n ^ 2) :=
      sharpness_recordProfileL1 n
    _ = 2 * iterationSharpnessS n := by rfl

/-- The denominator in the T5A ratio is strictly positive. -/
theorem uniformTransferSharpness_defect_pos (n : ℕ) :
    0 < operatorNormProjectorCommutatorL2 sharpnessPerspective
      (iterationSharpnessRotation n) := by
  rw [operatorNormProjectorCommutatorL2_iterationSharpnessRotation]
  exact mul_pos (Real.sqrt_pos.2 (by norm_num)) (iterationSharpnessS_pos n)

/-- Ratio between the actual profile variation and the ED3B uniform defect. -/
noncomputable def uniformTransferSharpnessRatio (n : ℕ) : ℝ :=
  recordProfileL1 sharpnessPerspective
      (iterationSharpnessRotation n (sharpnessX n)) (sharpnessX n) /
    operatorNormProjectorCommutatorL2 sharpnessPerspective
      (iterationSharpnessRotation n)

/-- Every member of the explicit family has exact transfer ratio `sqrt 2`. -/
theorem uniformTransferSharpnessRatio_eq_sqrt_two (n : ℕ) :
    uniformTransferSharpnessRatio n = Real.sqrt 2 := by
  unfold uniformTransferSharpnessRatio
  rw [uniformTransferSharpness_profile_exact,
    operatorNormProjectorCommutatorL2_iterationSharpnessRotation]
  have hs : iterationSharpnessS n ≠ 0 := ne_of_gt (iterationSharpnessS_pos n)
  have hsqrt_pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt hsqrt_pos
  field_simp [hs, hsqrt]
  nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]

/-- ED3B still supplies the current universal upper bound `2` on this ratio. -/
theorem uniformTransferSharpnessRatio_le_two (n : ℕ) :
    uniformTransferSharpnessRatio n ≤ 2 := by
  unfold uniformTransferSharpnessRatio
  apply (div_le_iff₀ (uniformTransferSharpness_defect_pos n)).2
  exact recordProfileL1_unitary_le_two_mul_operatorNormCommutatorL2
    sharpnessPerspective (iterationSharpnessRotation n) (sharpnessX n)
    (sharpnessX_norm n)

/-- Operational lower barrier: every proposed universal coefficient below
`sqrt 2` is violated by an explicit normalized member of the family. -/
theorem exists_uniformTransfer_violation_of_lt_sqrt_two
    {K : ℝ} (hK : K < Real.sqrt 2) :
    ∃ n : ℕ,
      K * operatorNormProjectorCommutatorL2 sharpnessPerspective
          (iterationSharpnessRotation n) <
        recordProfileL1 sharpnessPerspective
          (iterationSharpnessRotation n (sharpnessX n)) (sharpnessX n) := by
  refine ⟨0, ?_⟩
  have hratio : K < uniformTransferSharpnessRatio 0 := by
    rw [uniformTransferSharpnessRatio_eq_sqrt_two]
    exact hK
  unfold uniformTransferSharpnessRatio at hratio
  exact (lt_div_iff₀ (uniformTransferSharpness_defect_pos 0)).mp hratio

end
end EverettianDecoherence.Approximation

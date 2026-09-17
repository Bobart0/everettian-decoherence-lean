import EverettianDecoherence.Approximation.IterationSharpness.ElementaryDefect
import EverettianDecoherence.Approximation.UniformRecordPreservation
import EverettianDecoherence.Metrics.DimensionFreeSharpness.ProjectionProfile

/-!
**FR.** # T4 — instance numérique exacte en dimension 2

Cette couche donne un exemple entièrement calculé sur la perspective binaire
`sharpnessPerspective`. On prend le premier membre non trivial (`n = 1`) de la
rotation rationnelle déjà auditée : sa matrice a les coefficients exacts
`24/25` et `7/25`. Sur l'état normalisé `sharpnessE0`, les poids Born passent de
`(1, 0)` à `(576/625, 49/625)`, donc le profil L1 réel vaut `98/625`.

Le défaut de commutateur en norme d'opérateur L2 vaut exactement
`7 * sqrt 2 / 25` et satisfait la certification rationnelle `≤ 2/5`. La borne
ED3B normalisée est donc `≤ 4/5`; l'écart entre cette enveloppe rationnelle et
le profil réellement calculé vaut exactement `402/625`.

La partie défaut de commutateur est **NON BORN-SENSITIVE**. Les poids, le profil
L1 et l'écart final sont **BORN-SENSITIVE** parce qu'ils passent par
`recordProfileL1`/`bornRecord`. Aucune dynamique temporelle ni décohérence
n'est introduite.

**EN.** # T4 — exact numerical instance in dimension 2

This layer gives a fully calculated example on the fixed binary perspective
`sharpnessPerspective`. We take the first nontrivial member (`n = 1`) of the
already-audited rational rotation: its matrix has exact coefficients `24/25`
and `7/25`. On the normalized state `sharpnessE0`, Born weights move from
`(1, 0)` to `(576/625, 49/625)`, so the actual L1 record profile is `98/625`.

The L2 operator-norm commutator defect is exactly `7 * sqrt 2 / 25` and obeys
the rational certificate `≤ 2/5`. Hence the normalized ED3B bound is `≤ 4/5`;
the gap between this rational envelope and the actually calculated profile is
exactly `402/625`.

The commutator-defect part is **NON BORN-SENSITIVE**. The weights, L1 profile,
and final gap are **BORN-SENSITIVE** because they pass through
`recordProfileL1`/`bornRecord`. No time dynamics or decoherence is introduced.
-/

namespace EverettianDecoherence.Metrics

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Approximation
open scoped BigOperators Classical InnerProductSpace

noncomputable section

/-- Fixed binary perspective used by the worked example. -/
noncomputable def workedPerspective : Perspective 2 := sharpnessPerspective

/-- Explicit rational unitary used by the worked example. -/
noncomputable def workedUnitary : H 2 ≃ₗᵢ[ℂ] H 2 :=
  iterationSharpnessRotation 1

/-- Normalized input state of the worked example. -/
noncomputable def workedState : H 2 := sharpnessE0

/-- Rational defect certificate used to produce a simple numerical budget. -/
def workedEpsilon : ℝ := 2 / 5

/-- Rational ED3B envelope used in the worked example. -/
def workedRecordBound : ℝ := 4 / 5

/-- Actually calculated Born-sensitive L1 profile. -/
def workedActualProfile : ℝ := 98 / 625

/-- Difference between the rational envelope and the actual profile. -/
def workedGap : ℝ := workedRecordBound - workedActualProfile

/-- Exact cosine-like coefficient at `n = 1`. -/
theorem workedC_exact : iterationSharpnessC 1 = (24 : ℝ) / 25 := by
  norm_num [iterationSharpnessC, sharpnessA, sharpnessB,
    sharpnessP, sharpnessQ, sharpnessPellPair]

/-- Exact sine-like coefficient at `n = 1`. -/
theorem workedS_exact : iterationSharpnessS 1 = (7 : ℝ) / 25 := by
  norm_num [iterationSharpnessS, sharpnessA, sharpnessB,
    sharpnessP, sharpnessQ, sharpnessPellPair]

/-- First row of the explicit unitary matrix. -/
theorem workedUnitary_zero (x : H 2) :
    workedUnitary x (0 : Fin 2) =
      ((24 : ℝ) / 25 : ℂ) * x (0 : Fin 2) -
        ((7 : ℝ) / 25 : ℂ) * x (1 : Fin 2) := by
  unfold workedUnitary
  rw [iterationSharpnessRotation_zero, workedC_exact, workedS_exact]
  norm_num

/-- Second row of the explicit unitary matrix. -/
theorem workedUnitary_one (x : H 2) :
    workedUnitary x (1 : Fin 2) =
      ((7 : ℝ) / 25 : ℂ) * x (0 : Fin 2) +
        ((24 : ℝ) / 25 : ℂ) * x (1 : Fin 2) := by
  unfold workedUnitary
  rw [iterationSharpnessRotation_one, workedC_exact, workedS_exact]
  norm_num

/-- The selected input state is normalized. -/
theorem workedState_norm : ‖workedState‖ = 1 := by
  exact sharpnessE0_norm

/-- Exact first transformed coordinate. -/
theorem workedTransformed_zero :
    workedUnitary workedState (0 : Fin 2) = ((24 : ℝ) / 25 : ℂ) := by
  rw [workedUnitary_zero]
  simp [workedState, sharpnessE0]

/-- Exact second transformed coordinate. -/
theorem workedTransformed_one :
    workedUnitary workedState (1 : Fin 2) = ((7 : ℝ) / 25 : ℂ) := by
  rw [workedUnitary_one]
  simp [workedState, sharpnessE0]

/-- Exact transformed Born weight on the first cell. -/
theorem workedTransformed_line_weight :
    ‖projL sharpnessLine (workedUnitary workedState)‖ ^ 2 = (576 : ℝ) / 625 := by
  rw [iterationSharpnessLine_proj, norm_smul, sharpnessE0_norm, mul_one,
    workedTransformed_zero]
  norm_num [Complex.norm_real, Real.norm_eq_abs]

/-- Exact transformed Born weight on the orthogonal cell. -/
theorem workedTransformed_orthogonal_weight :
    ‖projL sharpnessLineᗮ (workedUnitary workedState)‖ ^ 2 = (49 : ℝ) / 625 := by
  rw [iterationSharpnessOrthogonal_proj, norm_smul, sharpnessE1_norm, mul_one,
    workedTransformed_one]
  norm_num [Complex.norm_real, Real.norm_eq_abs]

/-- Exact original Born weight on the first cell. -/
theorem workedOriginal_line_weight :
    ‖projL sharpnessLine workedState‖ ^ 2 = 1 := by
  rw [iterationSharpnessLine_proj]
  simp [workedState, sharpnessE0, sharpnessE0_norm]

/-- Exact original Born weight on the orthogonal cell. -/
theorem workedOriginal_orthogonal_weight :
    ‖projL sharpnessLineᗮ workedState‖ ^ 2 = 0 := by
  rw [iterationSharpnessOrthogonal_proj]
  simp [workedState, sharpnessE0, sharpnessE1]

/-- Actual Born-sensitive L1 profile of the worked example. -/
theorem worked_recordProfileL1_exact :
    recordProfileL1 workedPerspective (workedUnitary workedState) workedState =
      workedActualProfile := by
  unfold workedPerspective workedActualProfile recordProfileL1 finiteProfileL1 recordProfile
  change
    (∑ c : {c : Submodule ℂ (H 2) // c ∈ sharpnessPerspective.cells},
      |‖projL c.val (workedUnitary workedState)‖ ^ 2 -
        ‖projL c.val workedState‖ ^ 2|) = (98 : ℝ) / 625
  calc
    (∑ c : {c : Submodule ℂ (H 2) // c ∈ sharpnessPerspective.cells},
      |‖projL c.val (workedUnitary workedState)‖ ^ 2 -
        ‖projL c.val workedState‖ ^ 2|) =
        ∑ c ∈ sharpnessPerspective.cells,
          |‖projL c (workedUnitary workedState)‖ ^ 2 -
            ‖projL c workedState‖ ^ 2| := by
      symm
      exact Finset.sum_subtype sharpnessPerspective.cells (fun c => Iff.rfl)
        (fun c => |‖projL c (workedUnitary workedState)‖ ^ 2 -
          ‖projL c workedState‖ ^ 2|)
    _ =
        |(576 : ℝ) / 625 - 1| + |(49 : ℝ) / 625 - 0| := by
      change
        (∑ c ∈ ({sharpnessLine, sharpnessLineᗮ} : Finset (Submodule ℂ (H 2))),
          |‖projL c (workedUnitary workedState)‖ ^ 2 -
            ‖projL c workedState‖ ^ 2|) = _
      rw [Finset.sum_insert (by simpa using sharpnessLine_ne_orthogonal),
        Finset.sum_singleton, workedTransformed_line_weight,
        workedOriginal_line_weight, workedTransformed_orthogonal_weight,
        workedOriginal_orthogonal_weight]
    _ = (98 : ℝ) / 625 := by norm_num

/-- Exact NON BORN-SENSITIVE operator-norm commutator defect. -/
theorem worked_commutator_defect_exact :
    operatorNormProjectorCommutatorL2 workedPerspective workedUnitary =
      Real.sqrt 2 * ((7 : ℝ) / 25) := by
  unfold workedPerspective workedUnitary
  rw [operatorNormProjectorCommutatorL2_iterationSharpnessRotation, workedS_exact]

/-- Simple rational certificate for the exact commutator defect. -/
theorem worked_commutator_defect_le_epsilon :
    operatorNormProjectorCommutatorL2 workedPerspective workedUnitary ≤ workedEpsilon := by
  rw [worked_commutator_defect_exact]
  unfold workedEpsilon
  have hsqrt_sq : Real.sqrt (2 : ℝ) ^ 2 = 2 := by norm_num
  have hsqrt_nonneg : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  nlinarith

/-- Exact symbolic ED3B budget before rational relaxation. -/
theorem worked_exact_ED3B_budget :
    2 * operatorNormProjectorCommutatorL2 workedPerspective workedUnitary =
      (14 : ℝ) * Real.sqrt 2 / 25 := by
  rw [worked_commutator_defect_exact]
  ring

/-- Calculated rational ED3B bound for the normalized worked state. -/
theorem worked_recordProfileL1_le_bound :
    recordProfileL1 workedPerspective (workedUnitary workedState) workedState ≤
      workedRecordBound := by
  have h := recordProfileL1_unitary_le_two_mul_operatorNormCommutatorL2
    workedPerspective workedUnitary workedState workedState_norm
  have hdef := worked_commutator_defect_le_epsilon
  unfold workedRecordBound workedEpsilon at *
  nlinarith

/-- Exact rational gap between the certified bound and the actual profile. -/
theorem worked_gap_exact : workedGap = (402 : ℝ) / 625 := by
  norm_num [workedGap, workedRecordBound, workedActualProfile]

/-- The rational certificate is strictly non-saturated in this concrete instance. -/
theorem worked_actualProfile_lt_bound : workedActualProfile < workedRecordBound := by
  norm_num [workedActualProfile, workedRecordBound]

end
end EverettianDecoherence.Metrics

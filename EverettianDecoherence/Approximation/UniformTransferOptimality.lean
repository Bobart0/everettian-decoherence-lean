import EverettianDecoherence.Approximation.RecordSubsetCommutatorBounds
import EverettianDecoherence.Approximation.UniformTransferSharpness

/-!
**FR.** # T5B — borne universelle optimale `sqrt 2` pour ED3B

Cette couche combine l'identité de variation totale sur le sous-ensemble
positif, la géométrie des projecteurs agrégés et le partage quadratique du
défaut uniforme. Elle établit la borne universelle `sqrt 2` puis la combine
avec la famille T5A pour caractériser exactement les coefficients universels.

La borne de profil est BORN-SENSITIVE ; le contrôle du commutateur agrégé par
le défaut uniforme est NON BORN-SENSITIVE. Aucune dynamique temporelle ni
décohérence n'est introduite.

**EN.** # T5B — optimal universal `sqrt 2` bound for ED3B

This layer combines the total-variation identity on the positive subset,
aggregated-projector geometry, and the quadratic split of the uniform defect.
It proves the universal `sqrt 2` bound and then combines it with the T5A
family to characterize exactly all universal coefficients.

The profile bound is BORN-SENSITIVE; control of the aggregate commutator by
the uniform defect is NON BORN-SENSITIVE. No time dynamics or decoherence is
introduced.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical InnerProductSpace

noncomputable section

/-- Statewise aggregate-projector commutator bound with the sharp
`1 / sqrt 2` factor encoded without division. -/
theorem sqrt_two_mul_norm_recordSubsetProjectorCommutator_le_global_mul_norm
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    Real.sqrt 2 * ‖recordSubsetProjectorCommutator D U S x‖ ≤
      operatorNormProjectorCommutatorL2 D U * ‖x‖ := by
  have hhalf :=
    norm_sq_recordSubsetProjectorCommutator_le_half_globalSq_mul_norm_sq
      D U S x
  have htwo :
      2 * ‖recordSubsetProjectorCommutator D U S x‖ ^ 2 ≤
        operatorNormProjectorCommutatorL2 D U ^ 2 * ‖x‖ ^ 2 := by
    nlinarith
  have hsquare :
      (Real.sqrt 2 * ‖recordSubsetProjectorCommutator D U S x‖) ^ 2 ≤
        (operatorNormProjectorCommutatorL2 D U * ‖x‖) ^ 2 := by
    calc
      (Real.sqrt 2 * ‖recordSubsetProjectorCommutator D U S x‖) ^ 2 =
          2 * ‖recordSubsetProjectorCommutator D U S x‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      _ ≤ operatorNormProjectorCommutatorL2 D U ^ 2 * ‖x‖ ^ 2 := htwo
      _ = (operatorNormProjectorCommutatorL2 D U * ‖x‖) ^ 2 := by
        rw [mul_pow]
  exact (sq_le_sq₀
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (mul_nonneg (operatorNormProjectorCommutatorL2_nonneg D U)
      (norm_nonneg _))).mp hsquare

/-- T5B universal upper bound: the ED3B transfer coefficient improves from
`2` to `sqrt 2` for arbitrary states. -/
theorem recordProfileL1_unitary_le_sqrt_two_mul_norm_sq_mul_operatorNormCommutatorL2
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) (x : H n) :
    recordProfileL1 D (U x) x ≤
      Real.sqrt 2 * ‖x‖ ^ 2 * operatorNormProjectorCommutatorL2 D U := by
  let S := positiveRecordSubset D (U x) x
  have hdiff :
      ‖Gleason.projL (recordSubsetSubspace D S) (U x)‖ ^ 2 -
          ‖Gleason.projL (recordSubsetSubspace D S) x‖ ^ 2 ≤
        ‖recordSubsetProjectorCommutator D U S x‖ * ‖x‖ := by
    exact (le_abs_self _).trans
      (abs_recordSubsetProjector_norm_sq_sub_le_commutator D U S x)
  have hcomm :=
    sqrt_two_mul_norm_recordSubsetProjectorCommutator_le_global_mul_norm
      D U S x
  have hscaled := mul_le_mul_of_nonneg_left hcomm
    (mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) (norm_nonneg x))
  have hsqrt_sq : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
  rw [recordProfileL1_unitary_eq_two_mul_recordSubsetProjector_excess]
  change 2 * (
      ‖Gleason.projL (recordSubsetSubspace D S) (U x)‖ ^ 2 -
      ‖Gleason.projL (recordSubsetSubspace D S) x‖ ^ 2) ≤ _
  calc
    2 * (
        ‖Gleason.projL (recordSubsetSubspace D S) (U x)‖ ^ 2 -
        ‖Gleason.projL (recordSubsetSubspace D S) x‖ ^ 2) ≤
      2 * (‖recordSubsetProjectorCommutator D U S x‖ * ‖x‖) := by
        gcongr
    _ = (Real.sqrt 2 * ‖x‖) *
        (Real.sqrt 2 * ‖recordSubsetProjectorCommutator D U S x‖) := by
      calc
        2 * (‖recordSubsetProjectorCommutator D U S x‖ * ‖x‖) =
            Real.sqrt (2 : ℝ) ^ 2 *
              (‖recordSubsetProjectorCommutator D U S x‖ * ‖x‖) := by
          rw [hsqrt_sq]
        _ = (Real.sqrt 2 * ‖x‖) *
            (Real.sqrt 2 * ‖recordSubsetProjectorCommutator D U S x‖) := by
          ring
    _ ≤ (Real.sqrt 2 * ‖x‖) *
        (operatorNormProjectorCommutatorL2 D U * ‖x‖) := hscaled
    _ = Real.sqrt 2 * ‖x‖ ^ 2 *
        operatorNormProjectorCommutatorL2 D U := by ring

/-- Normalized-state form of the sharp universal T5B upper bound. -/
theorem recordProfileL1_unitary_le_sqrt_two_mul_operatorNormCommutatorL2
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) (x : H n) (hx : ‖x‖ = 1) :
    recordProfileL1 D (U x) x ≤
      Real.sqrt 2 * operatorNormProjectorCommutatorL2 D U := by
  simpa [hx] using
    recordProfileL1_unitary_le_sqrt_two_mul_norm_sq_mul_operatorNormCommutatorL2
      D U x

/-- A real number is a universal ED3B transfer coefficient when it bounds the
record-profile variation of every normalized state, perspective, and supplied
unitary by that coefficient times the uniform commutator defect. -/
def IsUniversalUniformTransferCoefficient (K : ℝ) : Prop :=
  ∀ {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) (x : H n),
    ‖x‖ = 1 →
      recordProfileL1 D (U x) x ≤
        K * operatorNormProjectorCommutatorL2 D U

/-- T5A + T5B: the universal ED3B coefficients are exactly the real numbers
at least `sqrt 2`. -/
theorem isUniversalUniformTransferCoefficient_iff_sqrt_two_le (K : ℝ) :
    IsUniversalUniformTransferCoefficient K ↔ Real.sqrt 2 ≤ K := by
  constructor
  · intro hK
    by_contra hnot
    have hlt : K < Real.sqrt 2 := lt_of_not_ge hnot
    obtain ⟨n, hn⟩ := exists_uniformTransfer_violation_of_lt_sqrt_two hlt
    have hup :=
      hK sharpnessPerspective (iterationSharpnessRotation n) (sharpnessX n)
        (sharpnessX_norm n)
    exact (not_lt_of_ge hup) hn
  · intro hK n D U x hx
    calc
      recordProfileL1 D (U x) x ≤
          Real.sqrt 2 * operatorNormProjectorCommutatorL2 D U :=
        recordProfileL1_unitary_le_sqrt_two_mul_operatorNormCommutatorL2
          D U x hx
      _ ≤ K * operatorNormProjectorCommutatorL2 D U :=
        mul_le_mul_of_nonneg_right hK
          (operatorNormProjectorCommutatorL2_nonneg D U)

end
end EverettianDecoherence.Approximation

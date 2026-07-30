import EverettianDecoherence.Approximation.IteratedProjectorCommutator
import EverettianDecoherence.Approximation.UniformRecordPreservation

/-!
**FR.** L'accumulation d'erreurs sur une liste finie est algébrique ; le
transfert vers `recordProfileL1` est BORN-SENSITIVE. Aucun temps, aucune
dynamique et aucune décohérence ne sont formalisés.

**EN.** Error accumulation over a finite list is algebraic; the transfer to
`recordProfileL1` is BORN-SENSITIVE. No time, dynamics, or decoherence is
formalized.
-/

namespace EverettianDecoherence.Approximation

theorem recordProfileL1_iterated_le_operatorNormProjectorCommutatorSum
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (Us : List (Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)) (x : Gleason.H n) :
    EverettianDecoherence.Metrics.recordProfileL1
        D (iteratedLinearIsometryEquivComp Us x) x ≤
      2 * ‖x‖ ^ 2 * operatorNormProjectorCommutatorSum D Us := by
  calc
    EverettianDecoherence.Metrics.recordProfileL1
        D (iteratedLinearIsometryEquivComp Us x) x ≤
        2 * ‖x‖ ^ 2 * operatorNormProjectorCommutatorL2 D (iteratedLinearIsometryEquivComp Us) :=
      recordProfileL1_unitary_le_two_mul_norm_sq_mul_operatorNormCommutatorL2
        D (iteratedLinearIsometryEquivComp Us) x
    _ ≤ 2 * ‖x‖ ^ 2 * operatorNormProjectorCommutatorSum D Us :=
      mul_le_mul_of_nonneg_left (operatorNormProjectorCommutatorL2_iterated_le_sum D Us)
        (mul_nonneg (by norm_num) (sq_nonneg _))

theorem recordProfileL1_iterated_le_two_mul_operatorNormProjectorCommutatorSum
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (Us : List (Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)) (x : Gleason.H n) (hx : ‖x‖ = 1) :
    EverettianDecoherence.Metrics.recordProfileL1
        D (iteratedLinearIsometryEquivComp Us x) x ≤
      2 * operatorNormProjectorCommutatorSum D Us := by
  calc
    EverettianDecoherence.Metrics.recordProfileL1
        D (iteratedLinearIsometryEquivComp Us x) x ≤
        2 * ‖x‖ ^ 2 * operatorNormProjectorCommutatorSum D Us :=
      recordProfileL1_iterated_le_operatorNormProjectorCommutatorSum D Us x
    _ = 2 * operatorNormProjectorCommutatorSum D Us := by rw [hx]; ring

theorem recordProfileWithin_of_each_operatorNormProjectorCommutatorWithin_iterated
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (Us : List (Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)) (x : Gleason.H n) (ε : ℝ)
    (hx : ‖x‖ = 1)
    (h : ∀ U ∈ Us, operatorNormProjectorCommutatorWithin D U ε) :
    EverettianDecoherence.Metrics.recordProfileWithin
      D (2 * ((Us.length : ℝ) * ε)) (iteratedLinearIsometryEquivComp Us x) x := by
  unfold EverettianDecoherence.Metrics.recordProfileWithin
  have hsum : operatorNormProjectorCommutatorSum D Us ≤ (Us.length : ℝ) * ε :=
    operatorNormProjectorCommutatorSum_le_length_mul D Us ε h
  have hbound := recordProfileL1_iterated_le_two_mul_operatorNormProjectorCommutatorSum D Us x hx
  linarith

theorem sameRecord_forall_of_iterated_zero_operatorNormProjectorCommutator
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (Us : List (Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n))
    (h : ∀ U ∈ Us, operatorNormProjectorCommutatorL2 D U = 0) :
    ∀ x, EverettianProbability.API.ExactFinite.SameRecord
      D (iteratedLinearIsometryEquivComp Us x) x :=
  sameRecord_forall_of_operatorNormProjectorCommutatorL2_eq_zero
    D (iteratedLinearIsometryEquivComp Us)
    (operatorNormProjectorCommutatorL2_iterated_eq_zero_of_all_zero D Us h)

end EverettianDecoherence.Approximation

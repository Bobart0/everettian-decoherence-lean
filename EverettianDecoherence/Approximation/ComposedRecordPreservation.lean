import EverettianDecoherence.Approximation.ComposedProjectorCommutator
import EverettianDecoherence.Approximation.UniformRecordPreservation

/-!
**FR.** La composition et sa borne de commutateur sont algébriques ; le
transfert vers `recordProfileL1` est BORN-SENSITIVE. Aucune dynamique
temporelle ni décohérence n'est formalisée.

**EN.** The composition and its commutator bound are algebraic; the transfer
to `recordProfileL1` is BORN-SENSITIVE. No time dynamics or decoherence is
formalized.
-/

namespace EverettianDecoherence.Approximation

theorem recordProfileL1_comp_le_operatorNormCommutatorSum
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U V : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) :
    EverettianDecoherence.Metrics.recordProfileL1
        D (linearIsometryEquivComp U V x) x ≤
      2 * ‖x‖ ^ 2 *
        (operatorNormProjectorCommutatorL2 D U +
          operatorNormProjectorCommutatorL2 D V) := by
  calc
    EverettianDecoherence.Metrics.recordProfileL1
        D (linearIsometryEquivComp U V x) x ≤
        2 * ‖x‖ ^ 2 * operatorNormProjectorCommutatorL2 D (linearIsometryEquivComp U V) :=
      recordProfileL1_unitary_le_two_mul_norm_sq_mul_operatorNormCommutatorL2
        D (linearIsometryEquivComp U V) x
    _ ≤ 2 * ‖x‖ ^ 2 *
          (operatorNormProjectorCommutatorL2 D U + operatorNormProjectorCommutatorL2 D V) :=
      mul_le_mul_of_nonneg_left (operatorNormProjectorCommutatorL2_comp_le D U V)
        (mul_nonneg (by norm_num) (sq_nonneg _))

theorem recordProfileL1_comp_le_two_mul_operatorNormCommutatorSum
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U V : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) (hx : ‖x‖ = 1) :
    EverettianDecoherence.Metrics.recordProfileL1
        D (linearIsometryEquivComp U V x) x ≤
      2 * (operatorNormProjectorCommutatorL2 D U + operatorNormProjectorCommutatorL2 D V) := by
  calc
    EverettianDecoherence.Metrics.recordProfileL1
        D (linearIsometryEquivComp U V x) x ≤
        2 * ‖x‖ ^ 2 *
          (operatorNormProjectorCommutatorL2 D U + operatorNormProjectorCommutatorL2 D V) :=
      recordProfileL1_comp_le_operatorNormCommutatorSum D U V x
    _ = 2 * (operatorNormProjectorCommutatorL2 D U + operatorNormProjectorCommutatorL2 D V) := by
      rw [hx]; ring

theorem recordProfileWithin_of_operatorNormProjectorCommutatorWithin_comp
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U V : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) (ε δ : ℝ)
    (hx : ‖x‖ = 1)
    (hU : operatorNormProjectorCommutatorWithin D U ε)
    (hV : operatorNormProjectorCommutatorWithin D V δ) :
    EverettianDecoherence.Metrics.recordProfileWithin
      D (2 * (ε + δ)) (linearIsometryEquivComp U V x) x := by
  unfold EverettianDecoherence.Metrics.recordProfileWithin
  have hsum : operatorNormProjectorCommutatorL2 D U + operatorNormProjectorCommutatorL2 D V ≤
      ε + δ := add_le_add hU hV
  have hbound := recordProfileL1_comp_le_two_mul_operatorNormCommutatorSum D U V x hx
  linarith

theorem sameRecord_forall_of_comp_zero_operatorNormProjectorCommutator
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U V : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (hU : operatorNormProjectorCommutatorL2 D U = 0)
    (hV : operatorNormProjectorCommutatorL2 D V = 0) :
    ∀ x, EverettianProbability.API.ExactFinite.SameRecord
      D (linearIsometryEquivComp U V x) x :=
  sameRecord_forall_of_operatorNormProjectorCommutatorL2_eq_zero
    D (linearIsometryEquivComp U V)
    (operatorNormProjectorCommutatorL2_comp_eq_zero D U V hU hV)

end EverettianDecoherence.Approximation

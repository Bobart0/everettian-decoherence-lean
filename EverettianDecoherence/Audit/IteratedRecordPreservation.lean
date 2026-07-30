import EverettianDecoherence.Approximation.IteratedRecordPreservation

/-!
**FR.** Audit ED4B de l'itération finie et de l'accumulation d'erreurs.

**EN.** ED4B audit of finite iteration and error accumulation.
-/

open EverettianDecoherence.Approximation
open EverettianDecoherence.Metrics

#check iteratedLinearIsometryEquivComp
#check iteratedLinearIsometryEquivComp_nil_apply
#check iteratedLinearIsometryEquivComp_cons_apply
#check iteratedLinearIsometryEquivComp_singleton_apply
#check iteratedLinearIsometryEquivComp_append_apply
#check operatorNormProjectorCommutatorSum
#check operatorNormProjectorCommutatorSum_nil
#check operatorNormProjectorCommutatorSum_cons
#check operatorNormProjectorCommutatorSum_nonneg
#check operatorNormProjectorCommutatorL2_iterated_le_sum
#check operatorNormProjectorCommutatorSum_le_length_mul
#check operatorNormProjectorCommutatorL2_iterated_le_length_mul
#check operatorNormProjectorCommutatorWithin_iterated_of_each
#check operatorNormProjectorCommutatorL2_iterated_eq_zero_of_all_zero
#check recordProfileL1_iterated_le_operatorNormProjectorCommutatorSum
#check recordProfileL1_iterated_le_two_mul_operatorNormProjectorCommutatorSum
#check recordProfileWithin_of_each_operatorNormProjectorCommutatorWithin_iterated
#check sameRecord_forall_of_iterated_zero_operatorNormProjectorCommutator

example {n : ℕ} (x : Gleason.H n) :
    iteratedLinearIsometryEquivComp
        ([] : List (Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)) x = x :=
  iteratedLinearIsometryEquivComp_nil_apply x

example {n : ℕ} (U V : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) :
    iteratedLinearIsometryEquivComp [U, V] x = V (U x) := by
  rw [iteratedLinearIsometryEquivComp_cons_apply, iteratedLinearIsometryEquivComp_singleton_apply]

example {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (Us : List (Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)) (x : Gleason.H n) (hx : ‖x‖ = 1) :
    recordProfileL1 D (iteratedLinearIsometryEquivComp Us x) x ≤
      2 * operatorNormProjectorCommutatorSum D Us :=
  recordProfileL1_iterated_le_two_mul_operatorNormProjectorCommutatorSum D Us x hx

example {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (Us : List (Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n))
    (h : ∀ U ∈ Us, operatorNormProjectorCommutatorL2 D U = 0) :
    ∀ x, EverettianProbability.API.ExactFinite.SameRecord
      D (iteratedLinearIsometryEquivComp Us x) x :=
  sameRecord_forall_of_iterated_zero_operatorNormProjectorCommutator D Us h

#print axioms EverettianDecoherence.Approximation.iteratedLinearIsometryEquivComp_append_apply
#print axioms EverettianDecoherence.Approximation.operatorNormProjectorCommutatorSum_nonneg
#print axioms EverettianDecoherence.Approximation.operatorNormProjectorCommutatorL2_iterated_le_sum
#print axioms EverettianDecoherence.Approximation.operatorNormProjectorCommutatorSum_le_length_mul
#print axioms EverettianDecoherence.Approximation.operatorNormProjectorCommutatorWithin_iterated_of_each
#print axioms EverettianDecoherence.Approximation.recordProfileL1_iterated_le_operatorNormProjectorCommutatorSum
#print axioms EverettianDecoherence.Approximation.recordProfileWithin_of_each_operatorNormProjectorCommutatorWithin_iterated
#print axioms EverettianDecoherence.Approximation.sameRecord_forall_of_iterated_zero_operatorNormProjectorCommutator

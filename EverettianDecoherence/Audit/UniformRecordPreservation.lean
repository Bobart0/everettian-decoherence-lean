import EverettianDecoherence.Approximation.UniformRecordPreservation

/-!
**FR.** Audit ED3B des normes d'opérateur et du transfert uniforme.

**EN.** ED3B audit of operator norms and uniform transfer.
-/

open EverettianDecoherence.Metrics
open EverettianDecoherence.Approximation

#check finiteL2_eq_zero_iff
#check finiteL2_mono_of_nonneg
#check finiteL2_le_mul_of_pointwise
#check perspectiveProjectorCommutatorCLM
#check perspectiveProjectorCommutatorCLM_apply
#check perspectiveProjectorCommutatorCLM_toLinearMap
#check perspectiveProjectorCommutatorOpNormProfile
#check operatorNormProjectorCommutatorL2
#check operatorNormProjectorCommutatorWithin
#check perspectiveProjectorCommutatorNormProfile_le_opNorm_mul_norm
#check statewiseProjectorCommutatorL2_le_operatorNormProjectorCommutatorL2_mul_norm
#check operatorNormProjectorCommutatorL2_eq_zero_iff_global_commutation
#check operatorNormProjectorCommutatorL2_refl
#check statewiseProjectorCommutatorWithin_of_operatorNormProjectorCommutatorWithin
#check statewiseProjectorCommutatorWithin_of_normalized_operatorNormWithin
#check uniformRecordPreservationBudget
#check recordProfileL1_unitary_le_two_mul_norm_sq_mul_operatorNormCommutatorL2
#check recordProfileWithin_of_normalized_operatorNormProjectorCommutatorWithin
#check sameRecord_forall_of_operatorNormProjectorCommutatorL2_eq_zero

example {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    perspectiveProjectorCommutatorNormProfile D U x c ≤
      perspectiveProjectorCommutatorOpNormProfile D U c * ‖x‖ :=
  perspectiveProjectorCommutatorNormProfile_le_opNorm_mul_norm D U x c

example {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) :
    operatorNormProjectorCommutatorL2 D (LinearIsometryEquiv.refl ℂ (Gleason.H n)) = 0 :=
  operatorNormProjectorCommutatorL2_refl D

example {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) (ε : ℝ)
    (hx : ‖x‖ = 1) (h : operatorNormProjectorCommutatorWithin D U ε) :
    EverettianDecoherence.Metrics.recordProfileWithin D (2 * ε) (U x) x :=
  recordProfileWithin_of_normalized_operatorNormProjectorCommutatorWithin D U x ε hx h

example {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (h : operatorNormProjectorCommutatorL2 D U = 0) :
    ∀ x, EverettianProbability.API.ExactFinite.SameRecord D (U x) x :=
  sameRecord_forall_of_operatorNormProjectorCommutatorL2_eq_zero D U h

#print axioms EverettianDecoherence.Metrics.finiteL2_eq_zero_iff
#print axioms EverettianDecoherence.Metrics.finiteL2_le_mul_of_pointwise
#print axioms EverettianDecoherence.Approximation.perspectiveProjectorCommutatorNormProfile_le_opNorm_mul_norm
#print axioms EverettianDecoherence.Approximation.statewiseProjectorCommutatorL2_le_operatorNormProjectorCommutatorL2_mul_norm
#print axioms EverettianDecoherence.Approximation.operatorNormProjectorCommutatorL2_eq_zero_iff_global_commutation
#print axioms EverettianDecoherence.Approximation.recordProfileL1_unitary_le_two_mul_norm_sq_mul_operatorNormCommutatorL2
#print axioms EverettianDecoherence.Approximation.recordProfileWithin_of_normalized_operatorNormProjectorCommutatorWithin
#print axioms EverettianDecoherence.Approximation.sameRecord_forall_of_operatorNormProjectorCommutatorL2_eq_zero
#print axioms EverettianDecoherence.Approximation.operatorNormProjectorCommutatorL2_refl
#print axioms EverettianDecoherence.Approximation.statewiseProjectorCommutatorWithin_of_operatorNormProjectorCommutatorWithin
#print axioms EverettianDecoherence.Approximation.statewiseProjectorCommutatorWithin_of_normalized_operatorNormWithin

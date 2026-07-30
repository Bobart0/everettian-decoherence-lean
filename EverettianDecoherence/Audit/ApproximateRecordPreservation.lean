import EverettianDecoherence.Approximation.ApproximateRecordPreservation

/-!
**FR.** Audit ED3A du défaut statewise et de son transfert BORN-SENSITIVE.

**EN.** ED3A audit of the statewise defect and its BORN-SENSITIVE transfer.
-/

open EverettianDecoherence.Approximation
open EverettianDecoherence.Metrics

#check perspectiveProjectorCommutator
#check perspectiveProjectorCommutator_apply
#check perspectiveProjectorCommutatorNormProfile
#check statewiseProjectorCommutatorL2
#check statewiseProjectorCommutatorWithin
#check perspectiveProjectorCommutatorNormProfile_nonneg
#check statewiseProjectorCommutatorL2_nonneg
#check statewiseProjectorCommutatorWithin_mono
#check statewiseProjectorCommutatorL2_eq_zero_of_apply_eq_zero
#check perspectiveProjectorCommutator_refl
#check statewiseProjectorCommutatorL2_refl
#check abs_recordCellNormProfile_unitary_sub_le_commutator
#check statewiseRecordPreservationBudget
#check statewiseRecordPreservationBudget_nonneg
#check recordProfileL1_unitary_le_statewiseRecordPreservationBudget
#check recordProfileL1_unitary_le_two_mul_norm_mul_statewiseCommutatorL2
#check recordProfileL1_unitary_le_two_mul_statewiseCommutatorL2
#check recordProfileWithin_of_statewiseProjectorCommutatorWithin
#check recordProfileWithin_of_normalized_statewiseProjectorCommutatorWithin
#check recordProfileL1_eq_zero_of_statewiseProjectorCommutatorL2_eq_zero
#check sameRecord_of_statewiseProjectorCommutatorL2_eq_zero
#check sameRecord_of_exact_projector_commutation_at_state

example {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    perspectiveProjectorCommutator D (LinearIsometryEquiv.refl ℂ (Gleason.H n)) c = 0 :=
  perspectiveProjectorCommutator_refl D c

example {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) (x : Gleason.H n) :
    statewiseProjectorCommutatorL2 D (LinearIsometryEquiv.refl ℂ (Gleason.H n)) x = 0 :=
  statewiseProjectorCommutatorL2_refl D x

example {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) (ε : ℝ)
    (hx : ‖x‖ = 1) (h : statewiseProjectorCommutatorWithin D U x ε) :
    recordProfileWithin D (2 * ε) (U x) x :=
  recordProfileWithin_of_normalized_statewiseProjectorCommutatorWithin D U x ε hx h

#print axioms EverettianDecoherence.Approximation.perspectiveProjectorCommutator_refl
#print axioms EverettianDecoherence.Approximation.statewiseProjectorCommutatorL2_eq_zero_of_apply_eq_zero
#print axioms EverettianDecoherence.Approximation.abs_recordCellNormProfile_unitary_sub_le_commutator
#print axioms EverettianDecoherence.Approximation.recordProfileL1_unitary_le_two_mul_norm_mul_statewiseCommutatorL2
#print axioms EverettianDecoherence.Approximation.recordProfileWithin_of_normalized_statewiseProjectorCommutatorWithin
#print axioms EverettianDecoherence.Approximation.sameRecord_of_statewiseProjectorCommutatorL2_eq_zero
#print axioms EverettianDecoherence.Approximation.sameRecord_of_exact_projector_commutation_at_state

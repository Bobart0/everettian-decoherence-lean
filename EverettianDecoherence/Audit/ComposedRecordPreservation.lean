import EverettianDecoherence.Approximation.ComposedRecordPreservation

/-!
**FR.** Audit ED4A de la composition à perspective fixée.

**EN.** ED4A audit of composition at a fixed perspective.
-/

open EverettianDecoherence.Approximation
open EverettianDecoherence.Metrics

#check linearIsometryEquivComp
#check linearIsometryEquivComp_apply
#check perspectiveProjectorCommutator_comp_apply
#check perspectiveProjectorCommutator_comp
#check perspectiveProjectorCommutatorOpNormProfile_comp_le
#check operatorNormProjectorCommutatorL2_comp_le
#check operatorNormProjectorCommutatorWithin_comp
#check operatorNormProjectorCommutatorL2_comp_eq_zero
#check recordProfileL1_comp_le_operatorNormCommutatorSum
#check recordProfileL1_comp_le_two_mul_operatorNormCommutatorSum
#check recordProfileWithin_of_operatorNormProjectorCommutatorWithin_comp
#check sameRecord_forall_of_comp_zero_operatorNormProjectorCommutator

example {n : ℕ} (U V : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) :
    linearIsometryEquivComp U V x = U (V x) :=
  linearIsometryEquivComp_apply U V x

example {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U V : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D)
    (x : Gleason.H n) :
    perspectiveProjectorCommutator D (linearIsometryEquivComp U V) c x =
      perspectiveProjectorCommutator D U c (V x) +
        U (perspectiveProjectorCommutator D V c x) :=
  perspectiveProjectorCommutator_comp_apply D U V c x

example {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U V : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) (hx : ‖x‖ = 1) :
    recordProfileL1 D (linearIsometryEquivComp U V x) x ≤
      2 * (operatorNormProjectorCommutatorL2 D U + operatorNormProjectorCommutatorL2 D V) :=
  recordProfileL1_comp_le_two_mul_operatorNormCommutatorSum D U V x hx

example {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U V : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (hU : operatorNormProjectorCommutatorL2 D U = 0)
    (hV : operatorNormProjectorCommutatorL2 D V = 0) :
    ∀ x, EverettianProbability.API.ExactFinite.SameRecord
      D (linearIsometryEquivComp U V x) x :=
  sameRecord_forall_of_comp_zero_operatorNormProjectorCommutator D U V hU hV

#print axioms EverettianDecoherence.Metrics.finiteL2_add_le
#print axioms EverettianDecoherence.Approximation.perspectiveProjectorCommutator_comp
#print axioms EverettianDecoherence.Approximation.perspectiveProjectorCommutatorOpNormProfile_comp_le
#print axioms EverettianDecoherence.Approximation.operatorNormProjectorCommutatorL2_comp_le
#print axioms EverettianDecoherence.Approximation.operatorNormProjectorCommutatorWithin_comp
#print axioms EverettianDecoherence.Approximation.recordProfileL1_comp_le_operatorNormCommutatorSum
#print axioms EverettianDecoherence.Approximation.recordProfileWithin_of_operatorNormProjectorCommutatorWithin_comp
#print axioms EverettianDecoherence.Approximation.sameRecord_forall_of_comp_zero_operatorNormProjectorCommutator

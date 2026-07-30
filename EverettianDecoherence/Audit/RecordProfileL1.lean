import EverettianDecoherence.Metrics.RecordProfileL1

/-!
**FR.** Audit des définitions et théorèmes de géométrie de profils ED1.

**EN.** Audit of ED1 profile-geometry definitions and theorems.
-/

open EverettianDecoherence.Metrics

#check finiteProfileL1
#check finiteProfileL1_nonneg
#check finiteProfileL1_self
#check finiteProfileL1_symm
#check finiteProfileL1_triangle
#check abs_sub_le_finiteProfileL1
#check finiteProfileL1_eq_zero_iff
#check recordProfile
#check recordProfileL1
#check recordProfileWithin
#check recordProfileL1_nonneg
#check recordProfileL1_self
#check recordProfileL1_symm
#check recordProfileL1_triangle
#check abs_bornRecord_sub_le_recordProfileL1
#check recordProfileL1_eq_zero_iff_sameRecord
#check recordProfileL1_eq_zero_of_recordUnitaryOrbit
#check recordProfileWithin_refl
#check recordProfileWithin_symm
#check recordProfileWithin_trans
#check recordProfileWithin_zero_iff_sameRecord

example :
    finiteProfileL1 (fun _ : Unit => 0) (fun _ : Unit => 1) = 1 := by
  simp [finiteProfileL1]

#print axioms EverettianDecoherence.Metrics.finiteProfileL1_triangle
#print axioms EverettianDecoherence.Metrics.finiteProfileL1_eq_zero_iff
#print axioms EverettianDecoherence.Metrics.recordProfileL1_eq_zero_iff_sameRecord
#print axioms EverettianDecoherence.Metrics.recordProfileL1_eq_zero_of_recordUnitaryOrbit
#print axioms EverettianDecoherence.Metrics.recordProfileWithin_trans

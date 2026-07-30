import EverettianDecoherence.Factorization.FiniteBipartiteSlices

/-!
**FR.** Audit ED5B des tranches bipartites finies et des profils de normes.

**EN.** ED5B audit of finite bipartite slices and norm profiles.
-/

open EverettianDecoherence.Factorization

#check FiniteSystemCoordinateSpace
#check FiniteEnvironmentCoordinateSpace
#check environmentSliceAtSystemIndex
#check systemSliceAtEnvironmentIndex
#check environmentSliceAtSystemIndex_apply
#check systemSliceAtEnvironmentIndex_apply
#check environmentSliceAtSystemIndex_zero
#check environmentSliceAtSystemIndex_add
#check environmentSliceAtSystemIndex_smul
#check systemSliceAtEnvironmentIndex_zero
#check systemSliceAtEnvironmentIndex_add
#check systemSliceAtEnvironmentIndex_smul
#check systemIndexSliceNormSqProfile
#check environmentIndexSliceNormSqProfile
#check systemIndexSliceNormSqProfile_nonneg
#check environmentIndexSliceNormSqProfile_nonneg
#check environmentSliceAtSystemIndex_norm_sq
#check systemSliceAtEnvironmentIndex_norm_sq
#check sum_systemIndexSliceNormSqProfile_eq_norm_sq
#check sum_environmentIndexSliceNormSqProfile_eq_norm_sq
#check sum_systemIndexSliceNormSqProfile_eq_one_of_normalized
#check sum_environmentIndexSliceNormSqProfile_eq_one_of_normalized
#check eq_of_environmentSliceAtSystemIndex_eq
#check eq_of_systemSliceAtEnvironmentIndex_eq

example {n s e : ℕ} (F : FiniteBipartiteFactorization n s e)
    (x : Gleason.H n) (i : Fin s) (j : Fin e) :
    environmentSliceAtSystemIndex F x i j = bipartiteCoordinate F x i j :=
  environmentSliceAtSystemIndex_apply F x i j

example {n s e : ℕ} (F : FiniteBipartiteFactorization n s e)
    (x : Gleason.H n) (j : Fin e) :
    ‖systemSliceAtEnvironmentIndex F x j‖ ^ 2 =
      ∑ i : Fin s, ‖bipartiteCoordinate F x i j‖ ^ 2 :=
  systemSliceAtEnvironmentIndex_norm_sq F x j

example {n s e : ℕ} (F : FiniteBipartiteFactorization n s e)
    (x : Gleason.H n) (hx : ‖x‖ = 1) :
    ∑ i : Fin s, systemIndexSliceNormSqProfile F x i = 1 :=
  sum_systemIndexSliceNormSqProfile_eq_one_of_normalized F x hx

example {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x y : Gleason.H n)
    (h : ∀ i, environmentSliceAtSystemIndex F x i = environmentSliceAtSystemIndex F y i) :
    x = y :=
  eq_of_environmentSliceAtSystemIndex_eq F x y h

#print axioms EverettianDecoherence.Factorization.environmentSliceAtSystemIndex_apply
#print axioms EverettianDecoherence.Factorization.systemSliceAtEnvironmentIndex_apply
#print axioms EverettianDecoherence.Factorization.environmentSliceAtSystemIndex_norm_sq
#print axioms EverettianDecoherence.Factorization.systemSliceAtEnvironmentIndex_norm_sq
#print axioms EverettianDecoherence.Factorization.sum_systemIndexSliceNormSqProfile_eq_norm_sq
#print axioms EverettianDecoherence.Factorization.sum_environmentIndexSliceNormSqProfile_eq_norm_sq
#print axioms EverettianDecoherence.Factorization.eq_of_environmentSliceAtSystemIndex_eq

import EverettianDecoherence.Factorization.FiniteBipartiteFactorization

/-!
**FR.** Audit ED5A de la factorisation bipartite finie typée en coordonnées.

**EN.** ED5A audit of the typed finite bipartite coordinate factorization.
-/

open EverettianDecoherence.Factorization

#check FiniteBipartiteCoordinateSpace
#check finiteProductIndexEquiv
#check finiteBipartiteCoordinateReindex
#check finiteBipartiteCoordinateReindex_apply
#check FiniteBipartiteFactorization
#check standardFiniteBipartiteFactorization
#check toBipartiteCoordinates
#check fromBipartiteCoordinates
#check toBipartiteCoordinates_apply
#check fromBipartiteCoordinates_apply
#check from_toBipartiteCoordinates
#check to_fromBipartiteCoordinates
#check norm_toBipartiteCoordinates
#check norm_fromBipartiteCoordinates
#check bipartiteCoordinate
#check bipartiteCoordinate_zero
#check bipartiteCoordinate_add
#check bipartiteCoordinate_smul
#check eq_of_bipartiteCoordinate_eq
#check sum_sq_bipartiteCoordinate_eq_norm_sq
#check sum_sum_sq_bipartiteCoordinate_eq_norm_sq

noncomputable example (s e : ℕ) :
    FiniteBipartiteFactorization (s * e) s e :=
  standardFiniteBipartiteFactorization s e

example {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x : Gleason.H n) :
    fromBipartiteCoordinates F (toBipartiteCoordinates F x) = x :=
  from_toBipartiteCoordinates F x

example {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x y : Gleason.H n)
    (h : ∀ i j, bipartiteCoordinate F x i j = bipartiteCoordinate F y i j) :
    x = y :=
  eq_of_bipartiteCoordinate_eq F x y h

example {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x : Gleason.H n) :
    ∑ i : Fin s, ∑ j : Fin e, ‖bipartiteCoordinate F x i j‖ ^ 2 = ‖x‖ ^ 2 :=
  sum_sum_sq_bipartiteCoordinate_eq_norm_sq F x

#print axioms EverettianDecoherence.Factorization.finiteBipartiteCoordinateReindex
#print axioms EverettianDecoherence.Factorization.standardFiniteBipartiteFactorization
#print axioms EverettianDecoherence.Factorization.from_toBipartiteCoordinates
#print axioms EverettianDecoherence.Factorization.norm_toBipartiteCoordinates
#print axioms EverettianDecoherence.Factorization.eq_of_bipartiteCoordinate_eq
#print axioms EverettianDecoherence.Factorization.sum_sq_bipartiteCoordinate_eq_norm_sq
#print axioms EverettianDecoherence.Factorization.sum_sum_sq_bipartiteCoordinate_eq_norm_sq

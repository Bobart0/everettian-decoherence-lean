import EverettianDecoherence.Factorization.AmbientBipartiteCoordinateMasks

/-!
**FR.** Audit ED5C des masques finis de coordonnées bipartites et de leur
transport dans l'espace ambiant.

**EN.** ED5C audit of finite bipartite coordinate masks and their transport
into the ambient space.
-/

open EverettianDecoherence.Factorization

#check systemCoordinateMask
#check environmentCoordinateMask
#check systemCoordinateMask_apply
#check environmentCoordinateMask_apply
#check systemCoordinateMask_comp_self
#check environmentCoordinateMask_comp_self
#check systemCoordinateMask_comp_eq_zero_of_ne
#check environmentCoordinateMask_comp_eq_zero_of_ne
#check systemCoordinateMask_comp_environmentCoordinateMask
#check sum_systemCoordinateMask_apply
#check sum_environmentCoordinateMask_apply
#check sum_systemCoordinateMask_eq_id
#check sum_environmentCoordinateMask_eq_id
#check ambientSystemCoordinateMask
#check ambientEnvironmentCoordinateMask
#check bipartiteCoordinate_ambientSystemCoordinateMask
#check bipartiteCoordinate_ambientEnvironmentCoordinateMask
#check ambientSystemCoordinateMask_comp_self
#check ambientEnvironmentCoordinateMask_comp_self
#check ambientSystemCoordinateMask_comp_eq_zero_of_ne
#check ambientEnvironmentCoordinateMask_comp_eq_zero_of_ne
#check ambientSystemCoordinateMask_comp_environmentCoordinateMask
#check sum_ambientSystemCoordinateMask_apply
#check sum_ambientEnvironmentCoordinateMask_apply
#check sum_ambientSystemCoordinateMask_eq_id
#check sum_ambientEnvironmentCoordinateMask_eq_id
#check ambientSystemCoordinateMask_norm_sq
#check ambientEnvironmentCoordinateMask_norm_sq
#check sum_norm_sq_ambientSystemCoordinateMask_eq_norm_sq
#check sum_norm_sq_ambientEnvironmentCoordinateMask_eq_norm_sq

example (s e : ℕ) (i : Fin s) (ψ : FiniteBipartiteCoordinateSpace s e) (p : Fin s × Fin e) :
    systemCoordinateMask s e i ψ p = if p.1 = i then ψ p else 0 :=
  systemCoordinateMask_apply s e i ψ p

example (s e : ℕ) (i k : Fin s) (hik : i ≠ k) :
    (systemCoordinateMask s e i).comp (systemCoordinateMask s e k) = 0 :=
  systemCoordinateMask_comp_eq_zero_of_ne s e i k hik

example {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x : Gleason.H n) :
    (∑ i : Fin s, ambientSystemCoordinateMask F i) x = x :=
  sum_ambientSystemCoordinateMask_apply F x

example {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x : Gleason.H n) :
    ∑ i : Fin s, ‖ambientSystemCoordinateMask F i x‖ ^ 2 = ‖x‖ ^ 2 :=
  sum_norm_sq_ambientSystemCoordinateMask_eq_norm_sq F x

#print axioms EverettianDecoherence.Factorization.systemCoordinateMask_comp_self
#print axioms EverettianDecoherence.Factorization.systemCoordinateMask_comp_eq_zero_of_ne
#print axioms EverettianDecoherence.Factorization.systemCoordinateMask_comp_environmentCoordinateMask
#print axioms EverettianDecoherence.Factorization.sum_systemCoordinateMask_eq_id
#print axioms EverettianDecoherence.Factorization.bipartiteCoordinate_ambientSystemCoordinateMask
#print axioms EverettianDecoherence.Factorization.sum_ambientSystemCoordinateMask_eq_id
#print axioms EverettianDecoherence.Factorization.ambientSystemCoordinateMask_norm_sq
#print axioms EverettianDecoherence.Factorization.sum_norm_sq_ambientSystemCoordinateMask_eq_norm_sq

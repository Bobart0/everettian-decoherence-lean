import EverettianDecoherence.Factorization.FiniteBipartiteCoordinates

/-!
**FR.** `F` désigne une factorisation bipartite finie choisie et fournie
comme donnée : aucune unicité n'est établie, aucune factorisation préférée
n'est sélectionnée, et aucun lien entre `F` et une perspective `D` n'est
encore défini. Aucune structure tensorielle hilbertienne abstraite n'est
formalisée ; aucune opération locale (trace partielle, état réduit,
intrication) n'est encore introduite. Aucune dynamique ni décohérence.
Aucune utilisation de `bornRecord`, `recordProfileL1` ou `SameRecord`.

**EN.** `F` denotes a chosen, explicitly supplied finite bipartite
factorization: no uniqueness is established, no preferred factorization is
selected, and no link between `F` and a perspective `D` is yet defined. No
abstract Hilbert tensor structure is formalized; no local operation (partial
trace, reduced state, entanglement) is introduced yet. No dynamics or
decoherence. No use of `bornRecord`, `recordProfileL1`, or `SameRecord`.
-/

namespace EverettianDecoherence.Factorization

abbrev FiniteBipartiteFactorization
    (ambientDim systemDim environmentDim : ℕ) :=
  Gleason.H ambientDim
    ≃ₗᵢ[ℂ]
  FiniteBipartiteCoordinateSpace systemDim environmentDim

noncomputable def standardFiniteBipartiteFactorization
    (systemDim environmentDim : ℕ) :
    FiniteBipartiteFactorization
      (systemDim * environmentDim)
      systemDim
      environmentDim :=
  finiteBipartiteCoordinateReindex systemDim environmentDim

noncomputable def toBipartiteCoordinates
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e)
    (x : Gleason.H n) :
    FiniteBipartiteCoordinateSpace s e :=
  F x

noncomputable def fromBipartiteCoordinates
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e)
    (ψ : FiniteBipartiteCoordinateSpace s e) :
    Gleason.H n :=
  F.symm ψ

theorem toBipartiteCoordinates_apply
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x : Gleason.H n) :
    toBipartiteCoordinates F x = F x :=
  rfl

theorem fromBipartiteCoordinates_apply
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e)
    (ψ : FiniteBipartiteCoordinateSpace s e) :
    fromBipartiteCoordinates F ψ = F.symm ψ :=
  rfl

theorem from_toBipartiteCoordinates
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x : Gleason.H n) :
    fromBipartiteCoordinates F (toBipartiteCoordinates F x) = x := by
  rw [fromBipartiteCoordinates_apply, toBipartiteCoordinates_apply, F.symm_apply_apply]

theorem to_fromBipartiteCoordinates
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e)
    (ψ : FiniteBipartiteCoordinateSpace s e) :
    toBipartiteCoordinates F (fromBipartiteCoordinates F ψ) = ψ := by
  rw [toBipartiteCoordinates_apply, fromBipartiteCoordinates_apply, F.apply_symm_apply]

theorem norm_toBipartiteCoordinates
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x : Gleason.H n) :
    ‖toBipartiteCoordinates F x‖ = ‖x‖ := by
  rw [toBipartiteCoordinates_apply]
  exact F.norm_map x

theorem norm_fromBipartiteCoordinates
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e)
    (ψ : FiniteBipartiteCoordinateSpace s e) :
    ‖fromBipartiteCoordinates F ψ‖ = ‖ψ‖ := by
  rw [fromBipartiteCoordinates_apply]
  exact F.symm.norm_map ψ

noncomputable def bipartiteCoordinate
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e)
    (x : Gleason.H n)
    (i : Fin s)
    (j : Fin e) : ℂ :=
  toBipartiteCoordinates F x (i, j)

theorem bipartiteCoordinate_zero
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (i : Fin s) (j : Fin e) :
    bipartiteCoordinate F 0 i j = 0 := by
  unfold bipartiteCoordinate toBipartiteCoordinates
  simp

theorem bipartiteCoordinate_add
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x y : Gleason.H n)
    (i : Fin s) (j : Fin e) :
    bipartiteCoordinate F (x + y) i j =
      bipartiteCoordinate F x i j + bipartiteCoordinate F y i j := by
  unfold bipartiteCoordinate toBipartiteCoordinates
  simp

theorem bipartiteCoordinate_smul
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (c : ℂ) (x : Gleason.H n)
    (i : Fin s) (j : Fin e) :
    bipartiteCoordinate F (c • x) i j = c • bipartiteCoordinate F x i j := by
  unfold bipartiteCoordinate toBipartiteCoordinates
  simp

theorem eq_of_bipartiteCoordinate_eq
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x y : Gleason.H n)
    (h : ∀ i j, bipartiteCoordinate F x i j = bipartiteCoordinate F y i j) :
    x = y := by
  have hxy : toBipartiteCoordinates F x = toBipartiteCoordinates F y := by
    ext p
    have hij := h p.1 p.2
    unfold bipartiteCoordinate at hij
    simpa using hij
  have hfromEq := congrArg (fromBipartiteCoordinates F) hxy
  rwa [from_toBipartiteCoordinates, from_toBipartiteCoordinates] at hfromEq

theorem sum_sq_bipartiteCoordinate_eq_norm_sq
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x : Gleason.H n) :
    ∑ p : Fin s × Fin e, ‖bipartiteCoordinate F x p.1 p.2‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [← norm_toBipartiteCoordinates F x, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro p _
  unfold bipartiteCoordinate
  rfl

theorem sum_sum_sq_bipartiteCoordinate_eq_norm_sq
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x : Gleason.H n) :
    ∑ i : Fin s, ∑ j : Fin e, ‖bipartiteCoordinate F x i j‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [← sum_sq_bipartiteCoordinate_eq_norm_sq F x, Fintype.sum_prod_type]

end EverettianDecoherence.Factorization

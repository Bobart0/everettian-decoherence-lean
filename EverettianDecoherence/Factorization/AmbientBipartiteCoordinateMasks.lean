import EverettianDecoherence.Factorization.FiniteBipartiteCoordinateMasks
import EverettianDecoherence.Factorization.FiniteBipartiteSlices

/-!
**FR.** Transport des masques coordonnés dans l'espace ambiant `Gleason.H n`
par une factorisation `F` choisie et fournie. Les masques ambiants dépendent
de `F` : aucune canonicité, aucune sélection d'une factorisation préférée et
aucune relation avec une perspective de records ne sont établies. Aucune
auto-adjonction n'est encore établie ; le terme « projecteur orthogonal »
n'est pas employé. Aucune probabilité, aucun état réduit, aucune opération
locale physique, aucune dynamique et aucune décohérence.

**EN.** Transport of the coordinate masks into the ambient space
`Gleason.H n` through a chosen, explicitly supplied factorization `F`.
Ambient masks depend on `F`: no canonicity, no selection of a preferred
factorization, and no relation to a record perspective are established. No
self-adjointness is established yet; the term "orthogonal projector" is not
used. No probability, reduced state, local physical operation, dynamics, or
decoherence.
-/

namespace EverettianDecoherence.Factorization

noncomputable def ambientSystemCoordinateMask
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (i : Fin s) :
    Gleason.H n →ₗ[ℂ] Gleason.H n :=
  F.symm.toLinearEquiv.toLinearMap.comp
    ((systemCoordinateMask s e i).comp F.toLinearEquiv.toLinearMap)

noncomputable def ambientEnvironmentCoordinateMask
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (j : Fin e) :
    Gleason.H n →ₗ[ℂ] Gleason.H n :=
  F.symm.toLinearEquiv.toLinearMap.comp
    ((environmentCoordinateMask s e j).comp F.toLinearEquiv.toLinearMap)

theorem bipartiteCoordinate_ambientSystemCoordinateMask
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (i : Fin s) (x : Gleason.H n)
    (k : Fin s) (j : Fin e) :
    bipartiteCoordinate F (ambientSystemCoordinateMask F i x) k j =
      if k = i then bipartiteCoordinate F x k j else 0 := by
  unfold ambientSystemCoordinateMask
  show bipartiteCoordinate F (F.symm (systemCoordinateMask s e i (F x))) k j = _
  unfold bipartiteCoordinate toBipartiteCoordinates
  rw [F.apply_symm_apply, systemCoordinateMask_apply]

theorem bipartiteCoordinate_ambientEnvironmentCoordinateMask
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (j : Fin e) (x : Gleason.H n)
    (i : Fin s) (l : Fin e) :
    bipartiteCoordinate F (ambientEnvironmentCoordinateMask F j x) i l =
      if l = j then bipartiteCoordinate F x i l else 0 := by
  unfold ambientEnvironmentCoordinateMask
  show bipartiteCoordinate F (F.symm (environmentCoordinateMask s e j (F x))) i l = _
  unfold bipartiteCoordinate toBipartiteCoordinates
  rw [F.apply_symm_apply, environmentCoordinateMask_apply]

theorem ambientSystemCoordinateMask_comp_self
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (i : Fin s) :
    (ambientSystemCoordinateMask F i).comp (ambientSystemCoordinateMask F i) =
      ambientSystemCoordinateMask F i := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply]
  apply eq_of_bipartiteCoordinate_eq F
  intro a b
  simp only [bipartiteCoordinate_ambientSystemCoordinateMask]
  by_cases h : a = i <;> simp [h]

theorem ambientEnvironmentCoordinateMask_comp_self
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (j : Fin e) :
    (ambientEnvironmentCoordinateMask F j).comp (ambientEnvironmentCoordinateMask F j) =
      ambientEnvironmentCoordinateMask F j := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply]
  apply eq_of_bipartiteCoordinate_eq F
  intro a b
  simp only [bipartiteCoordinate_ambientEnvironmentCoordinateMask]
  by_cases h : b = j <;> simp [h]

theorem ambientSystemCoordinateMask_comp_eq_zero_of_ne
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (i k : Fin s) (hik : i ≠ k) :
    (ambientSystemCoordinateMask F i).comp (ambientSystemCoordinateMask F k) = 0 := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.zero_apply]
  apply eq_of_bipartiteCoordinate_eq F
  intro a b
  simp only [bipartiteCoordinate_ambientSystemCoordinateMask, bipartiteCoordinate_zero]
  by_cases h : a = i <;> simp [h, hik]

theorem ambientEnvironmentCoordinateMask_comp_eq_zero_of_ne
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (j l : Fin e) (hjl : j ≠ l) :
    (ambientEnvironmentCoordinateMask F j).comp (ambientEnvironmentCoordinateMask F l) = 0 := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.zero_apply]
  apply eq_of_bipartiteCoordinate_eq F
  intro a b
  simp only [bipartiteCoordinate_ambientEnvironmentCoordinateMask, bipartiteCoordinate_zero]
  by_cases h : b = j <;> simp [h, hjl]

theorem ambientSystemCoordinateMask_comp_environmentCoordinateMask
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (i : Fin s) (j : Fin e) :
    (ambientSystemCoordinateMask F i).comp (ambientEnvironmentCoordinateMask F j) =
      (ambientEnvironmentCoordinateMask F j).comp (ambientSystemCoordinateMask F i) := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  apply eq_of_bipartiteCoordinate_eq F
  intro a b
  simp only [bipartiteCoordinate_ambientSystemCoordinateMask,
    bipartiteCoordinate_ambientEnvironmentCoordinateMask]
  by_cases h1 : a = i <;> by_cases h2 : b = j <;> simp [h1, h2]

theorem sum_ambientSystemCoordinateMask_apply
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x : Gleason.H n) :
    (∑ i : Fin s, ambientSystemCoordinateMask F i) x = x := by
  apply eq_of_bipartiteCoordinate_eq F
  intro a b
  rw [LinearMap.sum_apply]
  have hcoord : bipartiteCoordinate F (∑ i : Fin s, ambientSystemCoordinateMask F i x) a b =
      ∑ i : Fin s, bipartiteCoordinate F (ambientSystemCoordinateMask F i x) a b := by
    unfold bipartiteCoordinate toBipartiteCoordinates
    rw [map_sum]
    simp
  rw [hcoord]
  simp only [bipartiteCoordinate_ambientSystemCoordinateMask]
  simp

theorem sum_ambientEnvironmentCoordinateMask_apply
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x : Gleason.H n) :
    (∑ j : Fin e, ambientEnvironmentCoordinateMask F j) x = x := by
  apply eq_of_bipartiteCoordinate_eq F
  intro a b
  rw [LinearMap.sum_apply]
  have hcoord : bipartiteCoordinate F (∑ j : Fin e, ambientEnvironmentCoordinateMask F j x) a b =
      ∑ j : Fin e, bipartiteCoordinate F (ambientEnvironmentCoordinateMask F j x) a b := by
    unfold bipartiteCoordinate toBipartiteCoordinates
    rw [map_sum]
    simp
  rw [hcoord]
  simp only [bipartiteCoordinate_ambientEnvironmentCoordinateMask]
  simp

theorem sum_ambientSystemCoordinateMask_eq_id
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) :
    ∑ i : Fin s, ambientSystemCoordinateMask F i = LinearMap.id := by
  apply LinearMap.ext
  intro x
  rw [sum_ambientSystemCoordinateMask_apply, LinearMap.id_apply]

theorem sum_ambientEnvironmentCoordinateMask_eq_id
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) :
    ∑ j : Fin e, ambientEnvironmentCoordinateMask F j = LinearMap.id := by
  apply LinearMap.ext
  intro x
  rw [sum_ambientEnvironmentCoordinateMask_apply, LinearMap.id_apply]

theorem ambientSystemCoordinateMask_norm_sq
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (i : Fin s) (x : Gleason.H n) :
    ‖ambientSystemCoordinateMask F i x‖ ^ 2 = systemIndexSliceNormSqProfile F x i := by
  unfold systemIndexSliceNormSqProfile
  rw [environmentSliceAtSystemIndex_norm_sq]
  unfold ambientSystemCoordinateMask
  show ‖F.symm (systemCoordinateMask s e i (F x))‖ ^ 2 = _
  rw [F.symm.norm_map, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  simp only [systemCoordinateMask_apply]
  rw [show (fun a => ∑ b : Fin e, ‖(if (a, b).1 = i then (F x) (a, b) else 0)‖ ^ 2) =
      (fun a => if a = i then ∑ b : Fin e, ‖(F x) (a, b)‖ ^ 2 else 0) from by
    funext a
    by_cases h : a = i <;> simp [h]]
  rw [Finset.sum_ite_eq']
  simp
  rfl

theorem ambientEnvironmentCoordinateMask_norm_sq
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (j : Fin e) (x : Gleason.H n) :
    ‖ambientEnvironmentCoordinateMask F j x‖ ^ 2 = environmentIndexSliceNormSqProfile F x j := by
  unfold environmentIndexSliceNormSqProfile
  rw [systemSliceAtEnvironmentIndex_norm_sq]
  unfold ambientEnvironmentCoordinateMask
  show ‖F.symm (environmentCoordinateMask s e j (F x))‖ ^ 2 = _
  rw [F.symm.norm_map, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  simp only [environmentCoordinateMask_apply]
  rw [show (fun a => ∑ b : Fin e, ‖(if (a, b).2 = j then (F x) (a, b) else 0)‖ ^ 2) =
      (fun a => ∑ b : Fin e, if b = j then ‖(F x) (a, b)‖ ^ 2 else 0) from by
    funext a
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : b = j <;> simp [h]]
  simp_rw [Finset.sum_ite_eq']
  simp
  rfl

theorem sum_norm_sq_ambientSystemCoordinateMask_eq_norm_sq
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x : Gleason.H n) :
    ∑ i : Fin s, ‖ambientSystemCoordinateMask F i x‖ ^ 2 = ‖x‖ ^ 2 := by
  simp_rw [ambientSystemCoordinateMask_norm_sq]
  exact sum_systemIndexSliceNormSqProfile_eq_norm_sq F x

theorem sum_norm_sq_ambientEnvironmentCoordinateMask_eq_norm_sq
    {n s e : ℕ} (F : FiniteBipartiteFactorization n s e) (x : Gleason.H n) :
    ∑ j : Fin e, ‖ambientEnvironmentCoordinateMask F j x‖ ^ 2 = ‖x‖ ^ 2 := by
  simp_rw [ambientEnvironmentCoordinateMask_norm_sq]
  exact sum_environmentIndexSliceNormSqProfile_eq_norm_sq F x

end EverettianDecoherence.Factorization

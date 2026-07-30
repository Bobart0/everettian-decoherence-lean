import EverettianDecoherence.Factorization.FiniteBipartiteSlices

/-!
**FR.** Masques linéaires de sélection coordonnée sur l'espace de
coordonnées bipartite fini : `mask` désigne une sélection coordonnée
idempotente, sans revendication d'auto-adjonction. Le terme « projecteur
orthogonal » n'est donc pas employé. Aucun lien avec `Gleason.projL` ni avec
une perspective `D`. Aucune opération locale physique, aucune dynamique et
aucune décohérence ne sont introduites. Aucun transfert BORN-SENSITIVE.

**EN.** Linear coordinate-selection masks on the finite bipartite coordinate
space: `mask` denotes an idempotent coordinate selection, with no
self-adjointness claim. The term "orthogonal projector" is therefore not
used. No link to `Gleason.projL` or to a perspective `D`. No physical local
operation, dynamics, or decoherence is introduced. No BORN-SENSITIVE
transfer.
-/

namespace EverettianDecoherence.Factorization

noncomputable def systemCoordinateMask
    (s e : ℕ) (i : Fin s) :
    FiniteBipartiteCoordinateSpace s e →ₗ[ℂ] FiniteBipartiteCoordinateSpace s e where
  toFun ψ := WithLp.toLp 2 (fun p => if p.1 = i then ψ p else 0)
  map_add' ψ φ := by
    apply PiLp.ext
    intro p
    by_cases h : p.1 = i <;> simp [h]
  map_smul' c ψ := by
    apply PiLp.ext
    intro p
    by_cases h : p.1 = i <;> simp [h]

noncomputable def environmentCoordinateMask
    (s e : ℕ) (j : Fin e) :
    FiniteBipartiteCoordinateSpace s e →ₗ[ℂ] FiniteBipartiteCoordinateSpace s e where
  toFun ψ := WithLp.toLp 2 (fun p => if p.2 = j then ψ p else 0)
  map_add' ψ φ := by
    apply PiLp.ext
    intro p
    by_cases h : p.2 = j <;> simp [h]
  map_smul' c ψ := by
    apply PiLp.ext
    intro p
    by_cases h : p.2 = j <;> simp [h]

theorem systemCoordinateMask_apply
    (s e : ℕ) (i : Fin s) (ψ : FiniteBipartiteCoordinateSpace s e) (p : Fin s × Fin e) :
    systemCoordinateMask s e i ψ p = if p.1 = i then ψ p else 0 :=
  rfl

theorem environmentCoordinateMask_apply
    (s e : ℕ) (j : Fin e) (ψ : FiniteBipartiteCoordinateSpace s e) (p : Fin s × Fin e) :
    environmentCoordinateMask s e j ψ p = if p.2 = j then ψ p else 0 :=
  rfl

theorem systemCoordinateMask_comp_self
    (s e : ℕ) (i : Fin s) :
    (systemCoordinateMask s e i).comp (systemCoordinateMask s e i) =
      systemCoordinateMask s e i := by
  apply LinearMap.ext
  intro ψ
  apply PiLp.ext
  intro p
  rw [LinearMap.comp_apply, systemCoordinateMask_apply, systemCoordinateMask_apply]
  by_cases h : p.1 = i <;> simp [h]

theorem environmentCoordinateMask_comp_self
    (s e : ℕ) (j : Fin e) :
    (environmentCoordinateMask s e j).comp (environmentCoordinateMask s e j) =
      environmentCoordinateMask s e j := by
  apply LinearMap.ext
  intro ψ
  apply PiLp.ext
  intro p
  rw [LinearMap.comp_apply, environmentCoordinateMask_apply, environmentCoordinateMask_apply]
  by_cases h : p.2 = j <;> simp [h]

theorem systemCoordinateMask_comp_eq_zero_of_ne
    (s e : ℕ) (i k : Fin s) (hik : i ≠ k) :
    (systemCoordinateMask s e i).comp (systemCoordinateMask s e k) = 0 := by
  apply LinearMap.ext
  intro ψ
  apply PiLp.ext
  intro p
  rw [LinearMap.comp_apply, systemCoordinateMask_apply, systemCoordinateMask_apply]
  by_cases h : p.1 = i <;> simp [h, hik]

theorem environmentCoordinateMask_comp_eq_zero_of_ne
    (s e : ℕ) (j l : Fin e) (hjl : j ≠ l) :
    (environmentCoordinateMask s e j).comp (environmentCoordinateMask s e l) = 0 := by
  apply LinearMap.ext
  intro ψ
  apply PiLp.ext
  intro p
  rw [LinearMap.comp_apply, environmentCoordinateMask_apply, environmentCoordinateMask_apply]
  by_cases h : p.2 = j <;> simp [h, hjl]

theorem systemCoordinateMask_comp_environmentCoordinateMask
    (s e : ℕ) (i : Fin s) (j : Fin e) :
    (systemCoordinateMask s e i).comp (environmentCoordinateMask s e j) =
      (environmentCoordinateMask s e j).comp (systemCoordinateMask s e i) := by
  apply LinearMap.ext
  intro ψ
  apply PiLp.ext
  intro p
  rw [LinearMap.comp_apply, LinearMap.comp_apply, systemCoordinateMask_apply,
    environmentCoordinateMask_apply, environmentCoordinateMask_apply, systemCoordinateMask_apply]
  by_cases h1 : p.1 = i <;> by_cases h2 : p.2 = j <;> simp [h1, h2]

theorem sum_systemCoordinateMask_apply
    (s e : ℕ) (ψ : FiniteBipartiteCoordinateSpace s e) :
    (∑ i : Fin s, systemCoordinateMask s e i) ψ = ψ := by
  apply PiLp.ext
  intro p
  rw [LinearMap.sum_apply]
  simp [systemCoordinateMask_apply]

theorem sum_environmentCoordinateMask_apply
    (s e : ℕ) (ψ : FiniteBipartiteCoordinateSpace s e) :
    (∑ j : Fin e, environmentCoordinateMask s e j) ψ = ψ := by
  apply PiLp.ext
  intro p
  rw [LinearMap.sum_apply]
  simp [environmentCoordinateMask_apply]

theorem sum_systemCoordinateMask_eq_id
    (s e : ℕ) :
    ∑ i : Fin s, systemCoordinateMask s e i = LinearMap.id := by
  apply LinearMap.ext
  intro ψ
  rw [sum_systemCoordinateMask_apply, LinearMap.id_apply]

theorem sum_environmentCoordinateMask_eq_id
    (s e : ℕ) :
    ∑ j : Fin e, environmentCoordinateMask s e j = LinearMap.id := by
  apply LinearMap.ext
  intro ψ
  rw [sum_environmentCoordinateMask_apply, LinearMap.id_apply]

end EverettianDecoherence.Factorization

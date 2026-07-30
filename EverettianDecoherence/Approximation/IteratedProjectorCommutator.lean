import EverettianDecoherence.Approximation.ComposedProjectorCommutator

/-!
**FR.** Composition itérée finie d'une liste ordonnée de transformations pour
une perspective `D` fixée. L'ordre est explicitement chronologique :
`iteratedLinearIsometryEquivComp [U₁, ..., Uₖ] x = Uₖ (... (U₁ x) ...)`. Cette
couche est algébrique, finie, n'utilise aucun `bornRecord` et ne porte aucune
interprétation temporelle ni aucune décohérence.

**EN.** Finite iterated composition of an ordered list of transformations for
a fixed perspective `D`. The order is explicitly chronological:
`iteratedLinearIsometryEquivComp [U₁, ..., Uₖ] x = Uₖ (... (U₁ x) ...)`. This
layer is algebraic, finite, uses no `bornRecord`, and carries no temporal
interpretation or decoherence.
-/

namespace EverettianDecoherence.Approximation

noncomputable def iteratedLinearIsometryEquivComp
    {n : ℕ} :
    List (Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) →
      Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n
  | [] =>
      LinearIsometryEquiv.refl ℂ (Gleason.H n)
  | U :: Us =>
      linearIsometryEquivComp
        (iteratedLinearIsometryEquivComp Us)
        U

private theorem iteratedLinearIsometryEquivComp_nil_eq
    {n : ℕ} :
    iteratedLinearIsometryEquivComp
        ([] : List (Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)) =
      LinearIsometryEquiv.refl ℂ (Gleason.H n) :=
  rfl

private theorem iteratedLinearIsometryEquivComp_cons_eq
    {n : ℕ} (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (Us : List (Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)) :
    iteratedLinearIsometryEquivComp (U :: Us) =
      linearIsometryEquivComp (iteratedLinearIsometryEquivComp Us) U :=
  rfl

theorem iteratedLinearIsometryEquivComp_nil_apply
    {n : ℕ} (x : Gleason.H n) :
    iteratedLinearIsometryEquivComp
        ([] : List (Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)) x = x :=
  rfl

theorem iteratedLinearIsometryEquivComp_cons_apply
    {n : ℕ} (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (Us : List (Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)) (x : Gleason.H n) :
    iteratedLinearIsometryEquivComp (U :: Us) x =
      iteratedLinearIsometryEquivComp Us (U x) := by
  rw [iteratedLinearIsometryEquivComp_cons_eq, linearIsometryEquivComp_apply]

theorem iteratedLinearIsometryEquivComp_singleton_apply
    {n : ℕ} (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) :
    iteratedLinearIsometryEquivComp [U] x = U x := by
  rw [iteratedLinearIsometryEquivComp_cons_apply, iteratedLinearIsometryEquivComp_nil_apply]

theorem iteratedLinearIsometryEquivComp_append_apply
    {n : ℕ} (Us Vs : List (Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)) (x : Gleason.H n) :
    iteratedLinearIsometryEquivComp (Us ++ Vs) x =
      iteratedLinearIsometryEquivComp Vs (iteratedLinearIsometryEquivComp Us x) := by
  induction Us generalizing x with
  | nil => simp [iteratedLinearIsometryEquivComp_nil_apply]
  | cons U Us' ih =>
    rw [List.cons_append, iteratedLinearIsometryEquivComp_cons_apply,
      iteratedLinearIsometryEquivComp_cons_apply, ih]

noncomputable def operatorNormProjectorCommutatorSum
    {n : ℕ}
    (D : QuantumFoundations.BornRule.Perspective n)
    (Us : List (Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)) : ℝ :=
  (Us.map
    (fun U =>
      operatorNormProjectorCommutatorL2 D U)).sum

theorem operatorNormProjectorCommutatorSum_nil
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) :
    operatorNormProjectorCommutatorSum D
        ([] : List (Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)) = 0 := by
  unfold operatorNormProjectorCommutatorSum
  simp

theorem operatorNormProjectorCommutatorSum_cons
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (Us : List (Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)) :
    operatorNormProjectorCommutatorSum D (U :: Us) =
      operatorNormProjectorCommutatorL2 D U + operatorNormProjectorCommutatorSum D Us := by
  unfold operatorNormProjectorCommutatorSum
  simp [List.sum_cons]

theorem operatorNormProjectorCommutatorSum_nonneg
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (Us : List (Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)) :
    0 ≤ operatorNormProjectorCommutatorSum D Us := by
  unfold operatorNormProjectorCommutatorSum
  apply List.sum_nonneg
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨U, _, rfl⟩ := hy
  exact operatorNormProjectorCommutatorL2_nonneg D U

theorem operatorNormProjectorCommutatorL2_iterated_le_sum
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (Us : List (Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)) :
    operatorNormProjectorCommutatorL2 D (iteratedLinearIsometryEquivComp Us) ≤
      operatorNormProjectorCommutatorSum D Us := by
  induction Us with
  | nil =>
    rw [iteratedLinearIsometryEquivComp_nil_eq, operatorNormProjectorCommutatorL2_refl,
      operatorNormProjectorCommutatorSum_nil]
  | cons U Us' ih =>
    rw [iteratedLinearIsometryEquivComp_cons_eq, operatorNormProjectorCommutatorSum_cons]
    have hstep := operatorNormProjectorCommutatorL2_comp_le D (iteratedLinearIsometryEquivComp Us') U
    linarith [ih]

theorem operatorNormProjectorCommutatorSum_le_length_mul
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (Us : List (Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)) (ε : ℝ)
    (h : ∀ U ∈ Us, operatorNormProjectorCommutatorL2 D U ≤ ε) :
    operatorNormProjectorCommutatorSum D Us ≤ (Us.length : ℝ) * ε := by
  induction Us with
  | nil =>
    rw [operatorNormProjectorCommutatorSum_nil]
    simp
  | cons U Us' ih =>
    rw [operatorNormProjectorCommutatorSum_cons, List.length_cons]
    have hU : operatorNormProjectorCommutatorL2 D U ≤ ε := h U List.mem_cons_self
    have hUs' : operatorNormProjectorCommutatorSum D Us' ≤ (Us'.length : ℝ) * ε :=
      ih (fun V hV => h V (List.mem_cons_of_mem U hV))
    calc
      operatorNormProjectorCommutatorL2 D U + operatorNormProjectorCommutatorSum D Us' ≤
          ε + (Us'.length : ℝ) * ε := add_le_add hU hUs'
      _ = ((Us'.length : ℝ) + 1) * ε := by ring
      _ = ((Us'.length + 1 : ℕ) : ℝ) * ε := by norm_cast

theorem operatorNormProjectorCommutatorL2_iterated_le_length_mul
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (Us : List (Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)) (ε : ℝ)
    (h : ∀ U ∈ Us, operatorNormProjectorCommutatorL2 D U ≤ ε) :
    operatorNormProjectorCommutatorL2 D (iteratedLinearIsometryEquivComp Us) ≤
      (Us.length : ℝ) * ε :=
  (operatorNormProjectorCommutatorL2_iterated_le_sum D Us).trans
    (operatorNormProjectorCommutatorSum_le_length_mul D Us ε h)

theorem operatorNormProjectorCommutatorWithin_iterated_of_each
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (Us : List (Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)) (ε : ℝ)
    (h : ∀ U ∈ Us, operatorNormProjectorCommutatorWithin D U ε) :
    operatorNormProjectorCommutatorWithin
      D (iteratedLinearIsometryEquivComp Us) ((Us.length : ℝ) * ε) :=
  operatorNormProjectorCommutatorL2_iterated_le_length_mul D Us ε h

theorem operatorNormProjectorCommutatorL2_iterated_eq_zero_of_all_zero
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (Us : List (Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n))
    (h : ∀ U ∈ Us, operatorNormProjectorCommutatorL2 D U = 0) :
    operatorNormProjectorCommutatorL2 D (iteratedLinearIsometryEquivComp Us) = 0 := by
  induction Us with
  | nil =>
    rw [iteratedLinearIsometryEquivComp_nil_eq]
    exact operatorNormProjectorCommutatorL2_refl D
  | cons U Us' ih =>
    rw [iteratedLinearIsometryEquivComp_cons_eq]
    exact operatorNormProjectorCommutatorL2_comp_eq_zero D (iteratedLinearIsometryEquivComp Us') U
      (ih (fun V hV => h V (List.mem_cons_of_mem U hV)))
      (h U List.mem_cons_self)

end EverettianDecoherence.Approximation

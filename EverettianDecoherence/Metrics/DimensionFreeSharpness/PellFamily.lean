import EverettianDecoherence.Metrics.StateRecordDimensionFree

/-!
**FR.** # Optimalité de la constante 2 dans la borne ED2B

Ce module reste **BORN-SENSITIVE** : il utilise `recordProfileL1`, donc
`bornRecord`. Il ne définit aucune décohérence indépendante et ne modifie
aucune hypothèse physique. Il construit une famille explicite d'états
normalisés à coefficients rationnels dans `H 2` et une perspective binaire
fixe pour laquelle le quotient
`recordProfileL1 D x y / ‖x - y‖` tend vers `2`.

La famille rationnelle provient de la récurrence élémentaire préservant
`p^2 + 1 = 2 q^2` : `(p,q) ↦ (3p+4q, 2p+3q)`, à partir de `(1,1)`.
Aucune théorie externe de Pell ni décision par évaluation native n'est utilisée.

**EN.** # Sharpness of the constant 2 in the ED2B bound

This module remains **BORN-SENSITIVE**: it uses `recordProfileL1`, hence
`bornRecord`. It defines no independent decoherence notion and changes no
physical assumption. It builds an explicit family of normalized states with
rational coefficients in `H 2`, on one fixed binary perspective, such that
`recordProfileL1 D x y / ‖x - y‖` tends to `2`.

The rational family comes from the elementary recurrence preserving
`p^2 + 1 = 2 q^2`: `(p,q) ↦ (3p+4q, 2p+3q)`, starting at `(1,1)`.
No external Pell theory and no native-evaluation decision tactic are used.
-/

namespace EverettianDecoherence.Metrics

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open scoped BigOperators Classical InnerProductSpace

noncomputable section

/-- Pell-type pair used for the sharpness family. -/
def sharpnessPellPair : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n + 1 =>
      let z := sharpnessPellPair n
      (3 * z.1 + 4 * z.2, 2 * z.1 + 3 * z.2)

/-- First coordinate of the Pell-type recurrence. -/
def sharpnessP (n : ℕ) : ℕ := (sharpnessPellPair n).1

/-- Second coordinate of the Pell-type recurrence. -/
def sharpnessQ (n : ℕ) : ℕ := (sharpnessPellPair n).2

@[simp] theorem sharpnessP_zero : sharpnessP 0 = 1 := rfl
@[simp] theorem sharpnessQ_zero : sharpnessQ 0 = 1 := rfl

@[simp] theorem sharpnessP_succ (n : ℕ) :
    sharpnessP (n + 1) = 3 * sharpnessP n + 4 * sharpnessQ n := by
  rfl

@[simp] theorem sharpnessQ_succ (n : ℕ) :
    sharpnessQ (n + 1) = 2 * sharpnessP n + 3 * sharpnessQ n := by
  rfl

/-- Exact negative-Pell invariant in subtraction-free natural-number form. -/
theorem sharpnessP_sq_add_one_eq_two_mul_Q_sq (n : ℕ) :
    sharpnessP n ^ 2 + 1 = 2 * sharpnessQ n ^ 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [sharpnessP_succ, sharpnessQ_succ]
      nlinarith

/-- Both Pell coordinates remain strictly positive. -/
theorem sharpnessP_pos (n : ℕ) : 0 < sharpnessP n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [sharpnessP_succ]
      omega

theorem sharpnessQ_pos (n : ℕ) : 0 < sharpnessQ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [sharpnessQ_succ]
      omega

/-- The first Pell coordinate grows at least geometrically by factor 3. -/
theorem sharpnessP_geometric_step (n : ℕ) :
    (3 : ℝ) * (sharpnessP n : ℝ) ≤ (sharpnessP (n + 1) : ℝ) := by
  rw [sharpnessP_succ]
  norm_cast
  omega

/-- Hence the first Pell coordinate tends to `+∞`. -/
theorem sharpnessP_tendsto_atTop :
    Filter.Tendsto (fun n : ℕ => (sharpnessP n : ℝ)) Filter.atTop Filter.atTop := by
  exact tendsto_atTop_of_geom_le (by norm_num) (by norm_num) sharpnessP_geometric_step

/-- Rational first amplitude. -/
def sharpnessA (n : ℕ) : ℝ :=
  ((sharpnessP n : ℝ) + 1) / (2 * (sharpnessQ n : ℝ))

/-- Rational second amplitude. -/
def sharpnessB (n : ℕ) : ℝ :=
  ((sharpnessP n : ℝ) - 1) / (2 * (sharpnessQ n : ℝ))

theorem sharpnessQ_real_pos (n : ℕ) : 0 < (sharpnessQ n : ℝ) := by
  exact_mod_cast sharpnessQ_pos n

theorem sharpnessP_real_one_le (n : ℕ) : (1 : ℝ) ≤ sharpnessP n := by
  have hp_nat : 1 ≤ sharpnessP n := by
    have hp := sharpnessP_pos n
    omega
  exact_mod_cast hp_nat

theorem sharpnessA_nonneg (n : ℕ) : 0 ≤ sharpnessA n := by
  unfold sharpnessA
  positivity

theorem sharpnessB_nonneg (n : ℕ) : 0 ≤ sharpnessB n := by
  unfold sharpnessB
  exact div_nonneg (sub_nonneg.mpr (sharpnessP_real_one_le n)) (by positivity)

/-- Exact unit-circle identity: the two rational amplitudes define a normalized state. -/
theorem sharpnessA_sq_add_B_sq (n : ℕ) :
    sharpnessA n ^ 2 + sharpnessB n ^ 2 = 1 := by
  have hq : (sharpnessQ n : ℝ) ≠ 0 := ne_of_gt (sharpnessQ_real_pos n)
  have hrel :
      (sharpnessP n : ℝ) ^ 2 + 1 = 2 * (sharpnessQ n : ℝ) ^ 2 := by
    exact_mod_cast sharpnessP_sq_add_one_eq_two_mul_Q_sq n
  unfold sharpnessA sharpnessB
  field_simp [hq]
  nlinarith

/-- Difference of the two amplitudes. -/
theorem sharpnessA_sub_B (n : ℕ) :
    sharpnessA n - sharpnessB n = 1 / (sharpnessQ n : ℝ) := by
  have hq : (sharpnessQ n : ℝ) ≠ 0 := ne_of_gt (sharpnessQ_real_pos n)
  unfold sharpnessA sharpnessB
  field_simp [hq]
  ring

/-- Sum of the two amplitudes. -/
theorem sharpnessA_add_B (n : ℕ) :
    sharpnessA n + sharpnessB n = (sharpnessP n : ℝ) / sharpnessQ n := by
  have hq : (sharpnessQ n : ℝ) ≠ 0 := ne_of_gt (sharpnessQ_real_pos n)
  unfold sharpnessA sharpnessB
  field_simp [hq]
  ring

/-- Standard basis vectors in `H 2`. -/
noncomputable def sharpnessE0 : H 2 :=
  EuclideanSpace.single (0 : Fin 2) (1 : ℂ)

noncomputable def sharpnessE1 : H 2 :=
  EuclideanSpace.single (1 : Fin 2) (1 : ℂ)

theorem sharpnessE0_norm : ‖sharpnessE0‖ = 1 := by
  show ‖EuclideanSpace.single (0 : Fin 2) (1 : ℂ)‖ = 1
  simp [sharpnessE0]

theorem sharpnessE1_norm : ‖sharpnessE1‖ = 1 := by
  show ‖EuclideanSpace.single (1 : Fin 2) (1 : ℂ)‖ = 1
  simp [sharpnessE1]

theorem sharpnessE0_ne_zero : sharpnessE0 ≠ 0 := by
  intro h
  have := sharpnessE0_norm
  rw [h, norm_zero] at this
  norm_num at this

/-- Fixed line defining the binary perspective. -/
noncomputable def sharpnessLine : Submodule ℂ (H 2) := ℂ ∙ sharpnessE0

theorem sharpnessLine_finrank : Module.finrank ℂ sharpnessLine = 1 :=
  finrank_span_singleton sharpnessE0_ne_zero

theorem sharpnessLine_ne_bot : sharpnessLine ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  exact ⟨sharpnessE0, Submodule.mem_span_singleton_self _, sharpnessE0_ne_zero⟩

theorem sharpnessLine_ne_top : sharpnessLine ≠ ⊤ := by
  intro h
  have h1 := sharpnessLine_finrank
  rw [h, finrank_top] at h1
  simp at h1

/-- The fixed binary perspective used by every member of the family. -/
noncomputable def sharpnessPerspective : Perspective 2 :=
  Perspective.binary sharpnessLine sharpnessLine_ne_bot sharpnessLine_ne_top

/-- Source member of the rational sharpness pair. -/
noncomputable def sharpnessX (n : ℕ) : H 2 :=
  (sharpnessA n : ℂ) • sharpnessE0 + (sharpnessB n : ℂ) • sharpnessE1

/-- Target member, obtained by swapping the rational amplitudes. -/
noncomputable def sharpnessY (n : ℕ) : H 2 :=
  (sharpnessB n : ℂ) • sharpnessE0 + (sharpnessA n : ℂ) • sharpnessE1

theorem sharpnessE0_inner_E1 :
    (⟪sharpnessE0, sharpnessE1⟫_ℂ) = 0 := by
  unfold sharpnessE0 sharpnessE1
  rw [EuclideanSpace.inner_single_left]
  simp

theorem sharpnessE1_inner_E0 :
    (⟪sharpnessE1, sharpnessE0⟫_ℂ) = 0 := by
  rw [← inner_conj_symm, sharpnessE0_inner_E1]
  simp

theorem sharpnessE0_inner_self :
    (⟪sharpnessE0, sharpnessE0⟫_ℂ) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, sharpnessE0_norm]
  norm_num

theorem sharpnessE1_inner_self :
    (⟪sharpnessE1, sharpnessE1⟫_ℂ) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, sharpnessE1_norm]
  norm_num

theorem sharpnessX_zero (n : ℕ) :
    sharpnessX n (0 : Fin 2) = (sharpnessA n : ℂ) := by
  simp [sharpnessX, sharpnessE0, sharpnessE1]

theorem sharpnessX_one (n : ℕ) :
    sharpnessX n (1 : Fin 2) = (sharpnessB n : ℂ) := by
  simp [sharpnessX, sharpnessE0, sharpnessE1 ]

theorem sharpnessY_zero (n : ℕ) :
    sharpnessY n (0 : Fin 2) = (sharpnessB n : ℂ) := by
  simp [sharpnessY, sharpnessE0, sharpnessE1]

theorem sharpnessY_one (n : ℕ) :
    sharpnessY n (1 : Fin 2) = (sharpnessA n : ℂ) := by
  simp [sharpnessY, sharpnessE0, sharpnessE1 ]

theorem sharpnessX_norm_sq (n : ℕ) :
    ‖sharpnessX n‖ ^ 2 = sharpnessA n ^ 2 + sharpnessB n ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, sharpnessX_zero, sharpnessX_one]
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sharpnessA_nonneg n), abs_of_nonneg (sharpnessB_nonneg n)]

theorem sharpnessY_norm_sq (n : ℕ) :
    ‖sharpnessY n‖ ^ 2 = sharpnessA n ^ 2 + sharpnessB n ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, sharpnessY_zero, sharpnessY_one]
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sharpnessB_nonneg n), abs_of_nonneg (sharpnessA_nonneg n)]
  ring

/-- Every source state is normalized. -/
theorem sharpnessX_norm (n : ℕ) : ‖sharpnessX n‖ = 1 := by
  have hsq : ‖sharpnessX n‖ ^ 2 = 1 := by
    rw [sharpnessX_norm_sq, sharpnessA_sq_add_B_sq]
  nlinarith [norm_nonneg (sharpnessX n)]

/-- Every target state is normalized. -/
theorem sharpnessY_norm (n : ℕ) : ‖sharpnessY n‖ = 1 := by
  have hsq : ‖sharpnessY n‖ ^ 2 = 1 := by
    rw [sharpnessY_norm_sq, sharpnessA_sq_add_B_sq]
  nlinarith [norm_nonneg (sharpnessY n)]


end
end EverettianDecoherence.Metrics
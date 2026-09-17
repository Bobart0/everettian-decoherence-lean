import EverettianDecoherence.Approximation.IterationSharpness.RationalRotation
import EverettianDecoherence.Approximation.OperatorNormProjectorCommutator

/-!
**FR.** Troisième brique de T3. On calcule exactement, pour la perspective
binaire fixe de T2, le défaut de commutation en norme d'opérateur de la
rotation rationnelle `iterationSharpnessRotation n`. Cette couche est
**NON BORN-SENSITIVE** : elle n'utilise ni `bornRecord` ni poids de branche.

Chaque projecteur de la perspective binaire a un commutateur de norme
`iterationSharpnessS n`; l'agrégat L2 sur les deux cellules vaut donc
`sqrt 2 * iterationSharpnessS n`.

**EN.** Third T3 building block. For the fixed binary perspective from T2, we
compute exactly the operator-norm commutator defect of the rational rotation
`iterationSharpnessRotation n`. This layer is **NON BORN-SENSITIVE**: it uses
neither `bornRecord` nor branch weights.

Each projector in the binary perspective has commutator norm
`iterationSharpnessS n`; hence the two-cell L2 aggregate is
`sqrt 2 * iterationSharpnessS n`.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical InnerProductSpace

noncomputable section

private theorem iterationSharpnessLine_ne_orthogonal :
    sharpnessLine ≠ sharpnessLineᗮ := by
  intro h
  apply sharpnessLine_ne_bot
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hx' : x ∈ sharpnessLineᗮ := h ▸ hx
  rw [Submodule.mem_orthogonal] at hx'
  exact inner_self_eq_zero.mp (hx' x hx)

/-- The first cell of the fixed binary perspective. -/
noncomputable def iterationSharpnessLineCell :
    (EverettianProbability.Abstract.Projective.interface 2).Cell sharpnessPerspective :=
  ⟨sharpnessLine, by
    simpa [sharpnessPerspective, Perspective.binary]⟩

/-- The orthogonal cell of the fixed binary perspective. -/
noncomputable def iterationSharpnessOrthogonalCell :
    (EverettianProbability.Abstract.Projective.interface 2).Cell sharpnessPerspective :=
  ⟨sharpnessLineᗮ, by
    simpa [sharpnessPerspective, Perspective.binary]⟩

/-- Projection onto the first binary cell, on an arbitrary qubit vector. -/
theorem iterationSharpnessLine_proj (x : H 2) :
    projL sharpnessLine x = x (0 : Fin 2) • sharpnessE0 := by
  change sharpnessLine.starProjection x = _
  unfold sharpnessLine
  rw [Submodule.starProjection_unit_singleton ℂ sharpnessE0_norm]
  simp [sharpnessE0, EuclideanSpace.inner_single_left]

/-- Projection onto the orthogonal binary cell. -/
theorem iterationSharpnessOrthogonal_proj (x : H 2) :
    projL sharpnessLineᗮ x = x (1 : Fin 2) • sharpnessE1 := by
  change sharpnessLineᗮ.starProjection x = _
  rw [Submodule.starProjection_orthogonal_val]
  have hproj : sharpnessLine.starProjection x =
      x (0 : Fin 2) • sharpnessE0 := by
    unfold sharpnessLine
    rw [Submodule.starProjection_unit_singleton ℂ sharpnessE0_norm]
    simp [sharpnessE0, EuclideanSpace.inner_single_left]
  rw [hproj]
  ext i
  fin_cases i <;> simp [sharpnessE0, sharpnessE1]

/-- Orthogonal projection as the complementary projector. -/
theorem iterationSharpnessOrthogonal_proj_sub (x : H 2) :
    projL sharpnessLineᗮ x = x - projL sharpnessLine x := by
  change sharpnessLineᗮ.starProjection x = _
  rw [Submodule.starProjection_orthogonal_val]

private theorem iterationSharpnessLineCommutator_zero (n : ℕ) (x : H 2) :
    (perspectiveProjectorCommutatorCLM sharpnessPerspective
      (iterationSharpnessRotation n) iterationSharpnessLineCell x) (0 : Fin 2) =
      -(iterationSharpnessS n : ℂ) * x (1 : Fin 2) := by
  rw [perspectiveProjectorCommutatorCLM_apply, perspectiveProjectorCommutator_apply]
  change
    (projL sharpnessLine (iterationSharpnessRotation n x) -
      iterationSharpnessRotation n (projL sharpnessLine x)) (0 : Fin 2) = _
  rw [iterationSharpnessLine_proj, iterationSharpnessLine_proj]
  simp [iterationSharpnessRotation_zero, sharpnessE0]
  ring

private theorem iterationSharpnessLineCommutator_one (n : ℕ) (x : H 2) :
    (perspectiveProjectorCommutatorCLM sharpnessPerspective
      (iterationSharpnessRotation n) iterationSharpnessLineCell x) (1 : Fin 2) =
      -(iterationSharpnessS n : ℂ) * x (0 : Fin 2) := by
  rw [perspectiveProjectorCommutatorCLM_apply, perspectiveProjectorCommutator_apply]
  change
    (projL sharpnessLine (iterationSharpnessRotation n x) -
      iterationSharpnessRotation n (projL sharpnessLine x)) (1 : Fin 2) = _
  rw [iterationSharpnessLine_proj, iterationSharpnessLine_proj]
  simp [iterationSharpnessRotation_one, sharpnessE0]
  ring

/-- Pointwise norm of the first-cell commutator. -/
theorem iterationSharpnessLineCommutator_norm (n : ℕ) (x : H 2) :
    ‖perspectiveProjectorCommutatorCLM sharpnessPerspective
      (iterationSharpnessRotation n) iterationSharpnessLineCell x‖ =
      iterationSharpnessS n * ‖x‖ := by
  have hs : 0 ≤ iterationSharpnessS n := le_of_lt (iterationSharpnessS_pos n)
  have hsq :
      ‖perspectiveProjectorCommutatorCLM sharpnessPerspective
        (iterationSharpnessRotation n) iterationSharpnessLineCell x‖ ^ 2 =
        (iterationSharpnessS n * ‖x‖) ^ 2 := by
    calc
      ‖perspectiveProjectorCommutatorCLM sharpnessPerspective
          (iterationSharpnessRotation n) iterationSharpnessLineCell x‖ ^ 2 =
          ‖(perspectiveProjectorCommutatorCLM sharpnessPerspective
              (iterationSharpnessRotation n) iterationSharpnessLineCell x) (0 : Fin 2)‖ ^ 2 +
            ‖(perspectiveProjectorCommutatorCLM sharpnessPerspective
              (iterationSharpnessRotation n) iterationSharpnessLineCell x) (1 : Fin 2)‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      _ = iterationSharpnessS n ^ 2 *
          (‖x (0 : Fin 2)‖ ^ 2 + ‖x (1 : Fin 2)‖ ^ 2) := by
        rw [iterationSharpnessLineCommutator_zero,
          iterationSharpnessLineCommutator_one]
        simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
        ring
      _ = iterationSharpnessS n ^ 2 * ‖x‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      _ = (iterationSharpnessS n * ‖x‖) ^ 2 := by ring
  nlinarith [norm_nonneg
    (perspectiveProjectorCommutatorCLM sharpnessPerspective
      (iterationSharpnessRotation n) iterationSharpnessLineCell x),
    norm_nonneg x, mul_nonneg hs (norm_nonneg x)]

/-- Exact operator norm of the first-cell commutator. -/
theorem iterationSharpnessLineCommutator_opNorm (n : ℕ) :
    ‖perspectiveProjectorCommutatorCLM sharpnessPerspective
      (iterationSharpnessRotation n) iterationSharpnessLineCell‖ =
      iterationSharpnessS n := by
  have hs : 0 ≤ iterationSharpnessS n := le_of_lt (iterationSharpnessS_pos n)
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ hs
      (fun x => by rw [iterationSharpnessLineCommutator_norm])
  · have h := ContinuousLinearMap.le_opNorm
      (perspectiveProjectorCommutatorCLM sharpnessPerspective
        (iterationSharpnessRotation n) iterationSharpnessLineCell) sharpnessE0
    rw [iterationSharpnessLineCommutator_norm, sharpnessE0_norm, mul_one, mul_one] at h
    exact h

private theorem iterationSharpnessOrthogonalCommutator_eq_neg (n : ℕ) :
    perspectiveProjectorCommutatorCLM sharpnessPerspective
      (iterationSharpnessRotation n) iterationSharpnessOrthogonalCell =
      - perspectiveProjectorCommutatorCLM sharpnessPerspective
        (iterationSharpnessRotation n) iterationSharpnessLineCell := by
  apply ContinuousLinearMap.ext
  intro x
  change
    perspectiveProjectorCommutator sharpnessPerspective
      (iterationSharpnessRotation n) iterationSharpnessOrthogonalCell x =
      -(perspectiveProjectorCommutator sharpnessPerspective
        (iterationSharpnessRotation n) iterationSharpnessLineCell x)
  rw [perspectiveProjectorCommutator_apply,
    perspectiveProjectorCommutator_apply]
  change
    projL sharpnessLineᗮ (iterationSharpnessRotation n x) -
      iterationSharpnessRotation n (projL sharpnessLineᗮ x) =
      -(projL sharpnessLine (iterationSharpnessRotation n x) -
        iterationSharpnessRotation n (projL sharpnessLine x))
  rw [iterationSharpnessOrthogonal_proj_sub,
    iterationSharpnessOrthogonal_proj_sub, map_sub]
  abel

/-- Exact operator norm of the orthogonal-cell commutator. -/
theorem iterationSharpnessOrthogonalCommutator_opNorm (n : ℕ) :
    ‖perspectiveProjectorCommutatorCLM sharpnessPerspective
      (iterationSharpnessRotation n) iterationSharpnessOrthogonalCell‖ =
      iterationSharpnessS n := by
  rw [iterationSharpnessOrthogonalCommutator_eq_neg, norm_neg,
    iterationSharpnessLineCommutator_opNorm]

/-- Every cell of the fixed binary perspective has the same elementary defect. -/
theorem iterationSharpnessCommutatorOpNormProfile_eq (n : ℕ)
    (c : (EverettianProbability.Abstract.Projective.interface 2).Cell sharpnessPerspective) :
    perspectiveProjectorCommutatorOpNormProfile sharpnessPerspective
      (iterationSharpnessRotation n) c = iterationSharpnessS n := by
  have hc0 : c.val ∈ sharpnessPerspective.cells := c.property
  change c.val ∈ ({sharpnessLine, sharpnessLineᗮ} :
    Finset (Submodule ℂ (H 2))) at hc0
  have hc : c.val = sharpnessLine ∨ c.val = sharpnessLineᗮ := by
    rcases Finset.mem_insert.mp hc0 with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.mp h)
  rcases hc with hc | hc
  · have hcell : c = iterationSharpnessLineCell := Subtype.ext hc
    subst c
    exact iterationSharpnessLineCommutator_opNorm n
  · have hcell : c = iterationSharpnessOrthogonalCell := Subtype.ext hc
    subst c
    exact iterationSharpnessOrthogonalCommutator_opNorm n

private theorem iterationSharpnessPerspective_cell_card :
    Fintype.card
      ((EverettianProbability.Abstract.Projective.interface 2).Cell sharpnessPerspective) = 2 := by
  change Fintype.card ↥sharpnessPerspective.cells = 2
  rw [Fintype.card_coe]
  change ({sharpnessLine, sharpnessLineᗮ} : Finset (Submodule ℂ (H 2))).card = 2
  simp [iterationSharpnessLine_ne_orthogonal]

/-- Exact elementary ED4B operator-norm defect of the rational rotation. -/
theorem operatorNormProjectorCommutatorL2_iterationSharpnessRotation (n : ℕ) :
    operatorNormProjectorCommutatorL2 sharpnessPerspective
      (iterationSharpnessRotation n) =
      Real.sqrt 2 * iterationSharpnessS n := by
  unfold operatorNormProjectorCommutatorL2
  have hp :
      perspectiveProjectorCommutatorOpNormProfile sharpnessPerspective
        (iterationSharpnessRotation n) =
        fun _ => iterationSharpnessS n := by
    funext c
    exact iterationSharpnessCommutatorOpNormProfile_eq n c
  rw [hp]
  unfold EverettianDecoherence.Metrics.finiteL2
    EverettianDecoherence.Metrics.finiteL2Sq
  rw [Finset.sum_const, Finset.card_univ, iterationSharpnessPerspective_cell_card]
  norm_num
  rw [Real.sqrt_sq (le_of_lt (iterationSharpnessS_pos n))]

end
end EverettianDecoherence.Approximation

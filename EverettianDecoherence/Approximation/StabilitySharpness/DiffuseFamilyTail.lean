import EverettianDecoherence.Approximation.StabilitySharpness.DiffuseFamilyCellInvariants
import EverettianDecoherence.Approximation.OptimalTwoCellTail
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
**FR.** Queue top-two exacte de la famille diffuse, exprimée dans les objets
publication-facing du formalisme principal.

**EN.** Exact top-two tail of the diffuse family, expressed in the
publication-facing objects of the main formalism.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped Classical InnerProductSpace BigOperators

noncomputable section

theorem diffuseCoordinateCell_budget_sq
    {m : ℕ} (hm : 0 < m) (θ : ℝ) (k : Fin (m + m)) :
    cellCommutatorOpNormSq
        (coordinatePerspective (m + m)) (diffuseRotation m θ)
        (coordinateCell k) =
      v18DiffuseCellBudget m (diffuseAngularDefect θ) := by
  refine Fin.addCases ?_ ?_ k
  · intro i
    exact diffuseLeftCell_budget_sq hm θ i
  · intro i
    exact diffuseRightCell_budget_sq hm θ i

theorem diffuseAnyCell_budget_sq
    {m : ℕ} (hm : 0 < m) (θ : ℝ)
    (c : (Projective.interface (m + m)).Cell
      (coordinatePerspective (m + m))) :
    cellCommutatorOpNormSq
        (coordinatePerspective (m + m)) (diffuseRotation m θ) c =
      v18DiffuseCellBudget m (diffuseAngularDefect θ) := by
  obtain ⟨k, hk⟩ := (coordinateCell_bijective (m + m)).2 c
  rw [← hk]
  exact diffuseCoordinateCell_budget_sq hm θ k

theorem diffuse_has_distinct_cells
    {m : ℕ} (hm : 0 < m) :
    ∃ i j :
        (Projective.interface (m + m)).Cell
          (coordinatePerspective (m + m)),
      i ≠ j := by
  let i0 : Fin m := ⟨0, hm⟩
  let li : Fin (m + m) := Fin.castAdd m i0
  let ri : Fin (m + m) := Fin.natAdd m i0
  have hidx : li ≠ ri := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [li, ri, i0] at hv
    omega
  exact ⟨coordinateCell li, coordinateCell ri,
    coordinateCell_ne hidx⟩

theorem diffuseMaxTwoCellCapturedBudget_eq
    {m : ℕ} (hm : 0 < m) (θ : ℝ) :
    maxTwoCellCapturedBudget
        (coordinatePerspective (m + m)) (diffuseRotation m θ) =
      2 * v18DiffuseCellBudget m (diffuseAngularDefect θ) := by
  obtain ⟨i, j, hij, hmax⟩ :=
    exists_pair_eq_maxTwoCellCapturedBudget
      (coordinatePerspective (m + m)) (diffuseRotation m θ)
      (diffuse_has_distinct_cells hm)
  rw [diffuseAnyCell_budget_sq hm θ i,
    diffuseAnyCell_budget_sq hm θ j] at hmax
  linarith

theorem diffuseOptimalTwoCellTail_eq
    {m : ℕ} (hm : 0 < m) (θ : ℝ) :
    optimalTwoCellTail
        (coordinatePerspective (m + m)) (diffuseRotation m θ) =
      v18DiffuseGlobal m (diffuseAngularDefect θ) -
        2 * v18DiffuseCellBudget m (diffuseAngularDefect θ) := by
  unfold optimalTwoCellTail
  rw [diffuseGlobal_budget_sq hm θ,
    diffuseMaxTwoCellCapturedBudget_eq hm θ]

theorem diffuseAngularDefect_pos
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi2 : θ < Real.pi / 2) :
    0 < diffuseAngularDefect θ := by
  have hθpi : θ < Real.pi := by
    linarith [Real.pi_pos]
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 hθpi
  have htrig := Real.sin_sq_add_cos_sq θ
  unfold diffuseAngularDefect
  nlinarith [sq_pos_of_pos hsin]

theorem diffuseAngularDefect_lt_one
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi2 : θ < Real.pi / 2) :
    diffuseAngularDefect θ < 1 := by
  have hneg : -(Real.pi / 2) < θ := by
    linarith [Real.pi_pos]
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨hneg, hθpi2⟩
  unfold diffuseAngularDefect
  linarith

theorem diffuseCellBudget_pos
    {m : ℕ} (hm2 : 2 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi2 : θ < Real.pi / 2) :
    0 < v18DiffuseCellBudget m (diffuseAngularDefect θ) := by
  have hm : 0 < m := by omega
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hd0 := diffuseAngularDefect_pos hθ0 hθpi2
  have hd1 := diffuseAngularDefect_lt_one hθ0 hθpi2
  let d := diffuseAngularDefect θ
  have hfac :
      v18DiffuseCellBudget m d =
        d * (2 * (m : ℝ) - d) / (m : ℝ) ^ 2 := by
    unfold v18DiffuseCellBudget
    field_simp [ne_of_gt hmR]
  rw [hfac]
  have hsecond : 0 < 2 * (m : ℝ) - d := by
    dsimp [d]
    have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    nlinarith
  positivity

theorem diffuseOptimalTwoCellTailFraction_eq_tau
    {m : ℕ} (hm2 : 2 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi2 : θ < Real.pi / 2) :
    optimalTwoCellTailFraction
        (coordinatePerspective (m + m)) (diffuseRotation m θ) =
      v18DiffuseTau m := by
  have hm : 0 < m := by omega
  let p := v18DiffuseCellBudget m (diffuseAngularDefect θ)
  have hp : 0 < p := by
    dsimp [p]
    exact diffuseCellBudget_pos hm2 hθ0 hθpi2
  have hmR : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  unfold optimalTwoCellTailFraction
  rw [diffuseOptimalTwoCellTail_eq hm θ,
    diffuseGlobal_budget_sq hm θ]
  unfold v18DiffuseGlobal v18DiffuseTau
  change
    (2 * (m : ℝ) * p - 2 * p) /
        (2 * (m : ℝ) * p) =
      1 - 1 / (m : ℝ)
  field_simp [hmR, ne_of_gt hp]

end
end EverettianDecoherence.Approximation

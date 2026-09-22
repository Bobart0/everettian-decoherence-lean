import EverettianDecoherence.Approximation.StabilitySharpness.DiffuseFamilyDiagonal
import EverettianDecoherence.Approximation.StabilitySharpness.DiffuseFamilyScalar
import EverettianDecoherence.Approximation.RankOneCellCommutatorFormula
import Mathlib.Algebra.BigOperators.Fin

/-!
**FR.** Invariants publication-facing de la famille diffuse : chaque cellule
coordonnée a exactement le budget scalaire annoncé dans le manuscrit, puis la
somme L2 globale reproduit la formule A = 4d - 2d^2/m avec
d = 1 - cos(theta).

**EN.** Publication-facing invariants of the diffuse family: every coordinate
cell has exactly the scalar budget stated in the manuscript, and the global
L2 budget reproduces A = 4d - 2d^2/m with d = 1 - cos(theta).
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped Classical InnerProductSpace BigOperators

noncomputable section

def diffuseAngularDefect (θ : ℝ) : ℝ :=
  1 - Real.cos θ

theorem diffuseLeftFamily_is_coordinate
    (m : ℕ) (i : Fin m) :
    diffuseLeftFamily m i =
      coordinateOrthonormalBasis (m + m) (Fin.castAdd m i) := by
  rfl

theorem diffuseRightFamily_is_coordinate
    (m : ℕ) (i : Fin m) :
    diffuseRightFamily m i =
      coordinateOrthonormalBasis (m + m) (Fin.natAdd m i) := by
  rfl

theorem diffuseLeftCell_val
    (m : ℕ) (i : Fin m) :
    (coordinateCell (Fin.castAdd m i) :
      (Projective.interface (m + m)).Cell (coordinatePerspective (m + m))).val =
      ℂ ∙ diffuseLeftFamily m i := by
  rw [coordinateCell_val]
  rfl

theorem diffuseRightCell_val
    (m : ℕ) (i : Fin m) :
    (coordinateCell (Fin.natAdd m i) :
      (Projective.interface (m + m)).Cell (coordinatePerspective (m + m))).val =
      ℂ ∙ diffuseRightFamily m i := by
  rw [coordinateCell_val]
  rfl

private theorem diffuseDiagonal_norm_sq
    {m : ℕ} (hm : 0 < m) (θ : ℝ) :
    ‖(1 : ℂ) - (diffuseModeScale m : ℂ) ^ 2 *
        ((1 : ℂ) - (Real.cos θ : ℂ))‖ ^ 2 =
      (1 - (1 / (m : ℝ)) * diffuseAngularDefect θ) ^ 2 := by
  have hs := diffuseModeScale_sq hm
  have hreal :
      (1 : ℂ) - (diffuseModeScale m : ℂ) ^ 2 *
          ((1 : ℂ) - (Real.cos θ : ℂ)) =
        ((1 - diffuseModeScale m ^ 2 * diffuseAngularDefect θ : ℝ) : ℂ) := by
    unfold diffuseAngularDefect
    norm_num
  rw [hreal, Complex.norm_real, Real.norm_eq_abs, sq_abs, hs]

private theorem diffuseCellBudget_from_diagonal
    {m : ℕ} (hm : 0 < m) (θ : ℝ) :
    1 -
        ‖(1 : ℂ) - (diffuseModeScale m : ℂ) ^ 2 *
            ((1 : ℂ) - (Real.cos θ : ℂ))‖ ^ 2 =
      v18DiffuseCellBudget m (diffuseAngularDefect θ) := by
  rw [diffuseDiagonal_norm_sq hm θ]
  unfold v18DiffuseCellBudget diffuseAngularDefect
  have hmR : (m : ℝ) ≠ 0 := by positivity
  field_simp [hmR]
  ring

theorem diffuseLeftCell_budget_sq
    {m : ℕ} (hm : 0 < m) (θ : ℝ) (i : Fin m) :
    cellCommutatorOpNormSq
        (coordinatePerspective (m + m)) (diffuseRotation m θ)
        (coordinateCell (Fin.castAdd m i)) =
      v18DiffuseCellBudget m (diffuseAngularDefect θ) := by
  unfold cellCommutatorOpNormSq
  rw [perspectiveProjectorCommutatorOpNormProfile_sq_rankOne
    (coordinatePerspective (m + m)) (diffuseRotation m θ)
    (coordinateCell (Fin.castAdd m i)) (diffuseLeftFamily m i)
    ((diffuseLeftFamily_orthonormal m).1 i)
    (diffuseLeftCell_val m i)]
  rw [diffuseLeftFamily_diagonal hm θ i]
  exact diffuseCellBudget_from_diagonal hm θ

theorem diffuseRightCell_budget_sq
    {m : ℕ} (hm : 0 < m) (θ : ℝ) (i : Fin m) :
    cellCommutatorOpNormSq
        (coordinatePerspective (m + m)) (diffuseRotation m θ)
        (coordinateCell (Fin.natAdd m i)) =
      v18DiffuseCellBudget m (diffuseAngularDefect θ) := by
  unfold cellCommutatorOpNormSq
  rw [perspectiveProjectorCommutatorOpNormProfile_sq_rankOne
    (coordinatePerspective (m + m)) (diffuseRotation m θ)
    (coordinateCell (Fin.natAdd m i)) (diffuseRightFamily m i)
    ((diffuseRightFamily_orthonormal m).1 i)
    (diffuseRightCell_val m i)]
  rw [diffuseRightFamily_diagonal hm θ i]
  exact diffuseCellBudget_from_diagonal hm θ

theorem diffuseGlobal_budget_sq
    {m : ℕ} (hm : 0 < m) (θ : ℝ) :
    operatorNormProjectorCommutatorL2
        (coordinatePerspective (m + m)) (diffuseRotation m θ) ^ 2 =
      v18DiffuseGlobal m (diffuseAngularDefect θ) := by
  unfold operatorNormProjectorCommutatorL2
  rw [EverettianDecoherence.Metrics.finiteL2_sq]
  unfold EverettianDecoherence.Metrics.finiteL2Sq
  change
    (∑ c :
        (Projective.interface (m + m)).Cell
          (coordinatePerspective (m + m)),
      cellCommutatorOpNormSq
        (coordinatePerspective (m + m)) (diffuseRotation m θ) c) =
      v18DiffuseGlobal m (diffuseAngularDefect θ)
  rw [sum_coordinateCells]
  rw [Fin.sum_univ_add]
  simp_rw [diffuseLeftCell_budget_sq hm θ,
    diffuseRightCell_budget_sq hm θ]
  unfold v18DiffuseGlobal
  simp
  ring

theorem diffuseGlobal_budget_sq_exact
    {m : ℕ} (hm : 0 < m) (θ : ℝ) :
    operatorNormProjectorCommutatorL2
        (coordinatePerspective (m + m)) (diffuseRotation m θ) ^ 2 =
      4 * diffuseAngularDefect θ -
        2 * diffuseAngularDefect θ ^ 2 / (m : ℝ) := by
  rw [diffuseGlobal_budget_sq hm θ]
  exact v18DiffuseGlobal_exact m (Nat.ne_of_gt hm) (diffuseAngularDefect θ)

end
end EverettianDecoherence.Approximation

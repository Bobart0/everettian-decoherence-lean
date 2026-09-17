import EverettianDecoherence.Approximation.OperatorNormProjectorCommutator

/-!
**FR.** Budget quadratique du défaut uniforme restreint à un sous-ensemble
fini de cellules. Cette couche est purement algébrique et NON BORN-SENSITIVE.

**EN.** Quadratic uniform-defect budget restricted to a finite subset of
cells. This layer is purely algebraic and NON BORN-SENSITIVE.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

/-- Squared operator-norm commutator budget carried by a finite subset of
cells. -/
noncomputable def subsetProjectorCommutatorOpNormSq
    {n : ℕ} (D : Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (S : Finset ((Projective.interface n).Cell D)) : ℝ :=
  ∑ c ∈ S, (perspectiveProjectorCommutatorOpNormProfile D U c) ^ 2

theorem subsetProjectorCommutatorOpNormSq_nonneg
    {n : ℕ} (D : Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    0 ≤ subsetProjectorCommutatorOpNormSq D U S := by
  unfold subsetProjectorCommutatorOpNormSq
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- A subset and its finite complement partition the full squared L2 defect. -/
theorem subsetProjectorCommutatorOpNormSq_add_compl
    {n : ℕ} (D : Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    subsetProjectorCommutatorOpNormSq D U S +
        subsetProjectorCommutatorOpNormSq D U Sᶜ =
      operatorNormProjectorCommutatorL2 D U ^ 2 := by
  have hsplit :
      (∑ c ∈ S, (perspectiveProjectorCommutatorOpNormProfile D U c) ^ 2) +
          ∑ c ∈ Sᶜ, (perspectiveProjectorCommutatorOpNormProfile D U c) ^ 2 =
        ∑ c : (Projective.interface n).Cell D,
          (perspectiveProjectorCommutatorOpNormProfile D U c) ^ 2 := by
    exact S.sum_add_sum_compl
      (fun c => (perspectiveProjectorCommutatorOpNormProfile D U c) ^ 2)
  have hsq :
      operatorNormProjectorCommutatorL2 D U ^ 2 =
        ∑ c : (Projective.interface n).Cell D,
          (perspectiveProjectorCommutatorOpNormProfile D U c) ^ 2 := by
    exact finiteL2_sq (perspectiveProjectorCommutatorOpNormProfile D U)
  unfold subsetProjectorCommutatorOpNormSq
  rw [hsq]
  simpa using hsplit

/-- The smaller side of a cell partition carries at most half of the full
squared L2 defect. -/
theorem min_subset_compl_commutatorSq_le_half
    {n : ℕ} (D : Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    min (subsetProjectorCommutatorOpNormSq D U S)
        (subsetProjectorCommutatorOpNormSq D U Sᶜ) ≤
      (operatorNormProjectorCommutatorL2 D U ^ 2) / 2 := by
  have hsum := subsetProjectorCommutatorOpNormSq_add_compl D U S
  rcases le_total
      (subsetProjectorCommutatorOpNormSq D U S)
      (subsetProjectorCommutatorOpNormSq D U Sᶜ) with hle | hle
  · rw [min_eq_left hle]
    linarith
  · rw [min_eq_right hle]
    linarith

end
end EverettianDecoherence.Approximation

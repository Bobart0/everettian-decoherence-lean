import EverettianDecoherence.Approximation.RecordSubsetCommutatorBounds
import EverettianDecoherence.Approximation.RecordSubsetCrossBlockOpNorm
import EverettianDecoherence.Metrics.FiniteDimensionalOpNorm

/-!
**FR.** Bornes de norme opératorielle pour les commutateurs agrégés. Elles
extraient des bornes pointwise déjà établies les inégalités scalaires
c^2 ≤ A_S et c^2 ≤ A_{S^c}, et identifient la norme du cut à celle de son
complément.

**EN.** Operator-norm bounds for aggregate subset commutators. They lift the
existing pointwise estimates to the scalar inequalities c^2 ≤ A_S and
c^2 ≤ A_{S^c}, and identify the cut norm with that of its complement.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped Classical

noncomputable section

/-- The squared aggregate commutator operator norm is bounded by the squared
cellwise commutator budget on the subset. -/
theorem recordSubsetProjectorCommutatorCLM_opNorm_sq_le_subsetSq
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2 ≤
      subsetProjectorCommutatorOpNormSq D U S := by
  by_cases hz : ‖recordSubsetProjectorCommutatorCLM D U S‖ = 0
  · simpa [hz] using
      (subsetProjectorCommutatorOpNormSq_nonneg D U S)
  · have hpos : 0 < ‖recordSubsetProjectorCommutatorCLM D U S‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    obtain ⟨x, hx, hnorm⟩ :=
      exists_unit_norm_apply_eq_opNorm_of_pos
        (recordSubsetProjectorCommutatorCLM D U S) hpos
    have h :=
      norm_sq_recordSubsetProjectorCommutator_le_subsetSq_mul_norm_sq
        D U S x
    change
      ‖recordSubsetProjectorCommutatorCLM D U S x‖ ^ 2 ≤
        subsetProjectorCommutatorOpNormSq D U S * ‖x‖ ^ 2 at h
    rw [hnorm, hx, one_pow, mul_one] at h
    exact h

/-- The aggregate commutator CLM for the complementary cut is the negative of
the original one. -/
theorem recordSubsetProjectorCommutatorCLM_compl
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    recordSubsetProjectorCommutatorCLM D U Sᶜ =
      - recordSubsetProjectorCommutatorCLM D U S := by
  apply ContinuousLinearMap.ext
  intro x
  change
    recordSubsetProjectorCommutator D U Sᶜ x =
      - recordSubsetProjectorCommutator D U S x
  exact recordSubsetProjectorCommutator_compl_apply D U S x

theorem recordSubsetProjectorCommutatorCLM_opNorm_compl
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    ‖recordSubsetProjectorCommutatorCLM D U Sᶜ‖ =
      ‖recordSubsetProjectorCommutatorCLM D U S‖ := by
  rw [recordSubsetProjectorCommutatorCLM_compl D U S, norm_neg]

/-- The same aggregate norm is bounded by the complementary cell budget. -/
theorem recordSubsetProjectorCommutatorCLM_opNorm_sq_le_complSq
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2 ≤
      subsetProjectorCommutatorOpNormSq D U Sᶜ := by
  rw [← recordSubsetProjectorCommutatorCLM_opNorm_compl D U S]
  exact recordSubsetProjectorCommutatorCLM_opNorm_sq_le_subsetSq
    D U Sᶜ

end
end EverettianDecoherence.Approximation

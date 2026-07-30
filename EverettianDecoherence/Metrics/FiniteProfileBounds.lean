import EverettianDecoherence.Metrics.FiniteProfileL1

/-!
**FR.** Mathématiques génériques : conversion de bornes coordonnées en borne L1
globale sur un type fini. La borne par cardinalité peut être non optimale.

**EN.** Generic mathematics: conversion of coordinate bounds into a global L1
bound on a finite type. The cardinality bound may be non-optimal.
-/

namespace EverettianDecoherence.Metrics

open scoped BigOperators

theorem finiteProfileL1_le_sum_of_pointwise
    {α : Type*} [Fintype α] (p q b : α → ℝ)
    (h : ∀ i, |p i - q i| ≤ b i) :
    finiteProfileL1 p q ≤ ∑ i, b i := by
  unfold finiteProfileL1
  exact Finset.sum_le_sum fun i _ => h i

theorem finiteProfileL1_le_card_mul_of_pointwise
    {α : Type*} [Fintype α] (p q : α → ℝ) (δ : ℝ)
    (h : ∀ i, |p i - q i| ≤ δ) :
    finiteProfileL1 p q ≤ (Fintype.card α : ℝ) * δ := by
  calc
    finiteProfileL1 p q ≤ ∑ _ : α, δ :=
      finiteProfileL1_le_sum_of_pointwise p q (fun _ => δ) h
    _ = (Fintype.card α : ℝ) * δ := by
      simp [Finset.sum_const, nsmul_eq_mul]

end EverettianDecoherence.Metrics

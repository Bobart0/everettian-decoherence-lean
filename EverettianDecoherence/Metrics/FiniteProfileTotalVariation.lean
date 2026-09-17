import EverettianDecoherence.Metrics.FiniteProfileL1

/-!
**FR.** Identité purement finie de variation totale. Pour deux profils réels
sur un type fini ayant la même somme, la distance L1 est deux fois la somme
des différences positives. Aucune interprétation quantique ou probabiliste
n'est utilisée.

**EN.** Purely finite total-variation identity. For two real profiles on a
finite type with the same total mass, their L1 distance is twice the sum of
the positive differences. No quantum or probabilistic interpretation is used.
-/

namespace EverettianDecoherence.Metrics

open scoped BigOperators

/-- If two finite real profiles have the same total mass, their L1 distance is
exactly twice the positive part of their difference. -/
theorem finiteProfileL1_eq_two_mul_sum_filter_of_sum_eq
    {α : Type*} [Fintype α] (p q : α → ℝ)
    (hsum : (∑ i, p i) = ∑ i, q i) :
    finiteProfileL1 p q =
      2 * ∑ i ∈ Finset.univ.filter (fun i => q i ≤ p i), (p i - q i) := by
  classical
  have hdiff : (∑ i, (p i - q i)) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  have hsplit :
      (∑ i ∈ Finset.univ.filter (fun i => q i ≤ p i), (p i - q i)) +
          (∑ i ∈ Finset.univ.filter (fun i => ¬ q i ≤ p i), (p i - q i)) = 0 := by
    simpa using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : α => q i ≤ p i) (fun i => p i - q i)).trans hdiff
  have hpos :
      (∑ i ∈ Finset.univ.filter (fun i => q i ≤ p i), |p i - q i|) =
        ∑ i ∈ Finset.univ.filter (fun i => q i ≤ p i), (p i - q i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : q i ≤ p i := (Finset.mem_filter.mp hi).2
    exact abs_of_nonneg (sub_nonneg.mpr hi')
  have hneg :
      (∑ i ∈ Finset.univ.filter (fun i => ¬ q i ≤ p i), |p i - q i|) =
        -(∑ i ∈ Finset.univ.filter (fun i => ¬ q i ≤ p i), (p i - q i)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : ¬ q i ≤ p i := (Finset.mem_filter.mp hi).2
    exact abs_of_neg (sub_neg.mpr (lt_of_not_ge hi'))
  unfold finiteProfileL1
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : α => q i ≤ p i) (fun i => |p i - q i|), hpos, hneg]
  linarith

end EverettianDecoherence.Metrics

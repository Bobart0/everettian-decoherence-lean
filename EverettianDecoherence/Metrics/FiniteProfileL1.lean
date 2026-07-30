import Mathlib

/-!
**FR.** Quantité purement mathématique : distance L1 entre fonctions réelles
sur un type fini. Aucune interprétation quantique ou probabiliste n'est
impliquée.

**EN.** Purely mathematical quantity: L1 distance between real-valued
functions on a finite type. No quantum or probabilistic interpretation is
involved.
-/

namespace EverettianDecoherence.Metrics

open scoped BigOperators

noncomputable def finiteProfileL1
    {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ i, |p i - q i|

theorem finiteProfileL1_nonneg
    {α : Type*} [Fintype α] (p q : α → ℝ) :
    0 ≤ finiteProfileL1 p q := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem finiteProfileL1_self
    {α : Type*} [Fintype α] (p : α → ℝ) :
    finiteProfileL1 p p = 0 := by
  simp [finiteProfileL1]

theorem finiteProfileL1_symm
    {α : Type*} [Fintype α] (p q : α → ℝ) :
    finiteProfileL1 p q = finiteProfileL1 q p := by
  simp only [finiteProfileL1, abs_sub_comm]

theorem finiteProfileL1_triangle
    {α : Type*} [Fintype α] (p q r : α → ℝ) :
    finiteProfileL1 p r ≤ finiteProfileL1 p q + finiteProfileL1 q r := by
  calc
    finiteProfileL1 p r ≤ ∑ i, (|p i - q i| + |q i - r i|) := by
      apply Finset.sum_le_sum
      intro i _
      exact abs_sub_le (p i) (q i) (r i)
    _ = finiteProfileL1 p q + finiteProfileL1 q r := by
      simp [finiteProfileL1, Finset.sum_add_distrib]

theorem abs_sub_le_finiteProfileL1
    {α : Type*} [Fintype α] (p q : α → ℝ) (i : α) :
    |p i - q i| ≤ finiteProfileL1 p q := by
  unfold finiteProfileL1
  refine Finset.single_le_sum
    (s := Finset.univ) (f := fun j => |p j - q j|) ?_ (Finset.mem_univ i)
  intro j _
  exact abs_nonneg _

theorem finiteProfileL1_eq_zero_iff
    {α : Type*} [Fintype α] (p q : α → ℝ) :
    finiteProfileL1 p q = 0 ↔ p = q := by
  constructor
  · intro h
    funext i
    have hbound := abs_sub_le_finiteProfileL1 p q i
    have habs : |p i - q i| = 0 := by
      apply le_antisymm
      · simpa [h] using hbound
      · exact abs_nonneg _
    exact sub_eq_zero.mp (abs_eq_zero.mp habs)
  · intro h
    subst q
    exact finiteProfileL1_self p

end EverettianDecoherence.Metrics

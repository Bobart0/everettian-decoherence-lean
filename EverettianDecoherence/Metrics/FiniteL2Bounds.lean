import EverettianDecoherence.Metrics.FiniteProfileL1

/-!
**FR.** Mathématiques réelles génériques sur un type fini. Ce fichier ne porte
aucune interprétation quantique ou probabiliste, ne dépend pas du dépôt amont,
et fournit seulement les briques L2 nécessaires à ED2B.

**EN.** Generic real mathematics on a finite type. This file has no quantum or
probabilistic interpretation, has no upstream-repository dependency, and
provides only the L2 ingredients needed by ED2B.
-/

namespace EverettianDecoherence.Metrics

open scoped BigOperators

noncomputable def finiteL2Sq
    {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ i, (p i) ^ 2

noncomputable def finiteL2
    {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  Real.sqrt (finiteL2Sq p)

theorem finiteL2Sq_nonneg
    {α : Type*} [Fintype α] (p : α → ℝ) :
    0 ≤ finiteL2Sq p := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem finiteL2_nonneg
    {α : Type*} [Fintype α] (p : α → ℝ) :
    0 ≤ finiteL2 p :=
  Real.sqrt_nonneg _

theorem finiteL2_sq
    {α : Type*} [Fintype α] (p : α → ℝ) :
    finiteL2 p ^ 2 = finiteL2Sq p := by
  unfold finiteL2
  exact Real.sq_sqrt (finiteL2Sq_nonneg p)

theorem finite_sum_mul_le_l2_mul_l2
    {α : Type*} [Fintype α] (p q : α → ℝ) :
    ∑ i, p i * q i ≤
      Real.sqrt (∑ i, (p i) ^ 2) * Real.sqrt (∑ i, (q i) ^ 2) := by
  simpa using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ p q

theorem finite_sq_profile_l1_le_of_difference_bound
    {α : Type*} [Fintype α] (a b d : α → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (_hd : ∀ i, 0 ≤ d i)
    (hsub : ∀ i, |a i - b i| ≤ d i) :
    finiteProfileL1 (fun i => (a i) ^ 2) (fun i => (b i) ^ 2) ≤
      Real.sqrt (∑ i, (d i) ^ 2) *
        (Real.sqrt (∑ i, (a i) ^ 2) + Real.sqrt (∑ i, (b i) ^ 2)) := by
  calc
    finiteProfileL1 (fun i => (a i) ^ 2) (fun i => (b i) ^ 2) =
        ∑ i, |a i - b i| * (a i + b i) := by
      unfold finiteProfileL1
      apply Finset.sum_congr rfl
      intro i _
      change |a i ^ 2 - b i ^ 2| = |a i - b i| * (a i + b i)
      rw [sq_sub_sq, abs_mul,
        abs_of_nonneg (add_nonneg (ha i) (hb i))]
      simp [mul_comm]
    _ ≤ ∑ i, d i * (a i + b i) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hsub i) (add_nonneg (ha i) (hb i))
    _ = (∑ i, d i * a i) + ∑ i, d i * b i := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
    _ ≤ Real.sqrt (∑ i, (d i) ^ 2) * Real.sqrt (∑ i, (a i) ^ 2) +
          Real.sqrt (∑ i, (d i) ^ 2) * Real.sqrt (∑ i, (b i) ^ 2) := by
      exact add_le_add (finite_sum_mul_le_l2_mul_l2 d a)
        (finite_sum_mul_le_l2_mul_l2 d b)
    _ = Real.sqrt (∑ i, (d i) ^ 2) *
          (Real.sqrt (∑ i, (a i) ^ 2) + Real.sqrt (∑ i, (b i) ^ 2)) := by
      ring

end EverettianDecoherence.Metrics

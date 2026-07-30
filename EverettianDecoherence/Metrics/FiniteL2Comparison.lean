import EverettianDecoherence.Metrics.FiniteL2Bounds

/-!
**FR.** Comparaisons génériques de normes L2 sur des familles réelles finies,
sans interprétation quantique ni usage de `bornRecord`.

**EN.** Generic finite-family real L2 comparisons, with no quantum
interpretation and no use of `bornRecord`.
-/

namespace EverettianDecoherence.Metrics

open scoped BigOperators

theorem finiteL2_eq_zero_iff
    {α : Type*} [Fintype α] (p : α → ℝ) (_hp : ∀ i, 0 ≤ p i) :
    finiteL2 p = 0 ↔ ∀ i, p i = 0 := by
  constructor
  · intro h i
    have hs : ∑ j, p j ^ 2 = 0 :=
      (Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => sq_nonneg _)).mp h
    have hi : p i ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hs i (Finset.mem_univ i)
    exact (sq_eq_zero_iff).mp hi
  · intro h
    simp [finiteL2, finiteL2Sq, h]

theorem finiteL2_mono_of_nonneg
    {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hpq : ∀ i, p i ≤ q i) :
    finiteL2 p ≤ finiteL2 q := by
  unfold finiteL2 finiteL2Sq
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  nlinarith [hp i, hq i, hpq i]

theorem finiteL2_le_mul_of_pointwise
    {α : Type*} [Fintype α] (p q : α → ℝ) (a : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (ha : 0 ≤ a)
    (h : ∀ i, p i ≤ q i * a) :
    finiteL2 p ≤ finiteL2 q * a := by
  have hm := finiteL2_mono_of_nonneg p (fun i => q i * a) hp
    (fun i => mul_nonneg (hq i) ha) h
  have hs : finiteL2 (fun i => q i * a) = finiteL2 q * a := by
    apply (sq_eq_sq₀ (finiteL2_nonneg _) (mul_nonneg (finiteL2_nonneg q) ha)).mp
    rw [finiteL2_sq]
    calc
      ∑ i, (q i * a) ^ 2 = (∑ i, q i ^ 2) * a ^ 2 := by
        calc
          ∑ i, (q i * a) ^ 2 = ∑ i, q i ^ 2 * a ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = (∑ i, q i ^ 2) * a ^ 2 := by rw [Finset.sum_mul]
      _ = finiteL2 q ^ 2 * a ^ 2 := by rw [finiteL2_sq]; rfl
      _ = (finiteL2 q * a) ^ 2 := by ring
  rwa [hs] at hm

end EverettianDecoherence.Metrics

import EverettianDecoherence.Metrics.FiniteL2Bounds
import EverettianDecoherence.Metrics.FiniteL2Comparison

/-!
**FR.** Inégalité triangulaire générique pour `finiteL2` sur un type fini,
sans interprétation quantique, sans `bornRecord` et sans cardinalité. Elle
fournit la sous-additivité nécessaire à la composition ED4A.

**EN.** Generic triangle inequality for `finiteL2` on a finite type, with no
quantum interpretation, no `bornRecord`, and no cardinality. It supplies the
subadditivity needed for the ED4A composition.
-/

namespace EverettianDecoherence.Metrics

open scoped BigOperators

theorem finiteL2_add_le
    {α : Type*} [Fintype α]
    (p q : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    finiteL2 (fun i => p i + q i) ≤ finiteL2 p + finiteL2 q := by
  have hcs := finite_sum_mul_le_l2_mul_l2 p q
  have expand : (∑ i, (p i + q i) ^ 2) =
      (∑ i, p i ^ 2) + (∑ i, q i ^ 2) + 2 * ∑ i, p i * q i := by
    have hterm : ∀ i, (p i + q i) ^ 2 = p i ^ 2 + q i ^ 2 + 2 * (p i * q i) := by
      intro i; ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have key : finiteL2Sq (fun i => p i + q i) ≤ (finiteL2 p + finiteL2 q) ^ 2 := by
    unfold finiteL2Sq
    rw [expand]
    have hexp2 : (finiteL2 p + finiteL2 q) ^ 2 =
        finiteL2 p ^ 2 + finiteL2 q ^ 2 + 2 * (finiteL2 p * finiteL2 q) := by ring
    rw [hexp2, finiteL2_sq, finiteL2_sq]
    unfold finiteL2 finiteL2Sq
    linarith [hcs]
  have h1 : 0 ≤ finiteL2 p + finiteL2 q := add_nonneg (finiteL2_nonneg p) (finiteL2_nonneg q)
  calc
    finiteL2 (fun i => p i + q i)
        = Real.sqrt (finiteL2 (fun i => p i + q i) ^ 2) :=
          (Real.sqrt_sq (finiteL2_nonneg _)).symm
    _ = Real.sqrt (finiteL2Sq (fun i => p i + q i)) := by rw [finiteL2_sq]
    _ ≤ Real.sqrt ((finiteL2 p + finiteL2 q) ^ 2) := Real.sqrt_le_sqrt key
    _ = finiteL2 p + finiteL2 q := Real.sqrt_sq h1

theorem finiteL2_le_add_of_pointwise_le_add
    {α : Type*} [Fintype α]
    (r p q : α → ℝ)
    (hr : ∀ i, 0 ≤ r i)
    (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i)
    (h : ∀ i, r i ≤ p i + q i) :
    finiteL2 r ≤ finiteL2 p + finiteL2 q :=
  calc
    finiteL2 r ≤ finiteL2 (fun i => p i + q i) :=
      finiteL2_mono_of_nonneg r (fun i => p i + q i) hr
        (fun i => add_nonneg (hp i) (hq i)) h
    _ ≤ finiteL2 p + finiteL2 q := finiteL2_add_le p q hp hq

end EverettianDecoherence.Metrics

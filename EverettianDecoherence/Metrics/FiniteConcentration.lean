import EverettianDecoherence.Metrics.FiniteL2Bounds

/-!
**FR.** Lemmes réels génériques de concentration sur un ensemble fini. Ils
convertissent un petit défaut quadratique
`(∑ p_i)^2 - ∑ p_i^2` en concentration sur un indice maximal. Cette couche
est purement finie et réelle : aucune interprétation quantique, bornienne ou
dynamique n'intervient.

**EN.** Generic real concentration lemmas on a finite set. They convert a
small quadratic spread `(∑ p_i)^2 - ∑ p_i^2` into concentration on one
maximal index. This layer is purely finite and real: no quantum, Born, or
dynamical interpretation is involved.
-/

namespace EverettianDecoherence.Metrics

open scoped BigOperators

noncomputable section

/-- A nonnegative finite profile admits a maximal entry whose value controls
the full sum of squares. -/
theorem exists_max_with_sum_sq_le_mul_sum
    {α : Type*} [DecidableEq α]
    (S : Finset α) (p : α → ℝ) (hS : S.Nonempty)
    (hp : ∀ i ∈ S, 0 ≤ p i) :
    ∃ i ∈ S,
      (∀ j ∈ S, p j ≤ p i) ∧
      (∑ j ∈ S, p j ^ 2) ≤ p i * (∑ j ∈ S, p j) := by
  obtain ⟨i, hi, himax⟩ := Finset.exists_max_image S p hS
  refine ⟨i, hi, himax, ?_⟩
  calc
    (∑ j ∈ S, p j ^ 2) ≤ ∑ j ∈ S, p i * p j := by
      apply Finset.sum_le_sum
      intro j hj
      have hj0 := hp j hj
      have hjmax := himax j hj
      nlinarith
    _ = p i * (∑ j ∈ S, p j) := by
      rw [Finset.mul_sum]

/-- If the quadratic spread of a nonnegative finite profile is small, then
after removing a maximal entry the remaining mass times the total mass is
small by the same amount. -/
theorem exists_tail_mul_sum_le_of_spread_le
    {α : Type*} [DecidableEq α]
    (S : Finset α) (p : α → ℝ) (E : ℝ) (hS : S.Nonempty)
    (hp : ∀ i ∈ S, 0 ≤ p i)
    (hspread :
      (∑ j ∈ S, p j) ^ 2 - (∑ j ∈ S, p j ^ 2) ≤ E) :
    ∃ i ∈ S,
      (∑ j ∈ S.erase i, p j) * (∑ j ∈ S, p j) ≤ E := by
  obtain ⟨i, hi, _himax, hsq⟩ :=
    exists_max_with_sum_sq_le_mul_sum S p hS hp
  refine ⟨i, hi, ?_⟩
  have hdecomp :
      (∑ j ∈ S, p j) =
        (∑ j ∈ S.erase i, p j) + p i := by
    simpa [add_comm] using (Finset.sum_erase_add S p hi).symm
  have hprod :
      (∑ j ∈ S.erase i, p j) * (∑ j ∈ S, p j) ≤
        (∑ j ∈ S, p j) ^ 2 - (∑ j ∈ S, p j ^ 2) := by
    calc
      (∑ j ∈ S.erase i, p j) * (∑ j ∈ S, p j) =
          (∑ j ∈ S, p j) ^ 2 -
            p i * (∑ j ∈ S, p j) := by
        rw [hdecomp]
        ring
      _ ≤ (∑ j ∈ S, p j) ^ 2 - (∑ j ∈ S, p j ^ 2) := by
        linarith
  exact hprod.trans hspread

/-- Quantitative concentration with an external positive lower bound on the
total mass. -/
theorem exists_tail_le_of_spread_le
    {α : Type*} [DecidableEq α]
    (S : Finset α) (p : α → ℝ) (E L : ℝ) (hS : S.Nonempty)
    (hp : ∀ i ∈ S, 0 ≤ p i)
    (hspread :
      (∑ j ∈ S, p j) ^ 2 - (∑ j ∈ S, p j ^ 2) ≤ E)
    (hL : L ≤ ∑ j ∈ S, p j) (hLpos : 0 < L) :
    ∃ i ∈ S, (∑ j ∈ S.erase i, p j) ≤ E / L := by
  obtain ⟨i, hi, htail⟩ :=
    exists_tail_mul_sum_le_of_spread_le S p E hS hp hspread
  refine ⟨i, hi, ?_⟩
  have htail0 : 0 ≤ ∑ j ∈ S.erase i, p j :=
    Finset.sum_nonneg fun j hj => hp j (Finset.mem_of_mem_erase hj)
  have hmul :
      L * (∑ j ∈ S.erase i, p j) ≤ E := by
    calc
      L * (∑ j ∈ S.erase i, p j) ≤
          (∑ j ∈ S, p j) * (∑ j ∈ S.erase i, p j) :=
        mul_le_mul_of_nonneg_right hL htail0
      _ = (∑ j ∈ S.erase i, p j) * (∑ j ∈ S, p j) := by
        ring
      _ ≤ E := htail
  apply (le_div_iff₀ hLpos).2
  simpa [mul_comm] using hmul


/-- The off-diagonal quadratic mass is exactly total-square minus the sum of
individual squares. -/
theorem sum_offDiagonal_mul_eq_sum_sq_sub_sum_sq
    {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, p i * p j) =
      (∑ i, p i) ^ 2 - ∑ i, p i ^ 2 := by
  have hrow : ∀ i : α,
      (∑ j ∈ Finset.univ.erase i, p i * p j) =
        p i * (∑ j, p j) - p i ^ 2 := by
    intro i
    rw [← Finset.mul_sum]
    have hi : i ∈ (Finset.univ : Finset α) := Finset.mem_univ i
    rw [← Finset.sum_erase_add _ _ hi]
    ring
  simp_rw [hrow, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  ring

end
end EverettianDecoherence.Metrics

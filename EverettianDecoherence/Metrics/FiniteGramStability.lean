import EverettianDecoherence.Metrics.FiniteConcentration
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
**FR.** Stabilité quantitative générique d'une matrice de Gram. Une famille
orthonormale `xi` sert de référence; une famille `zeta` proche dont les
recouvrements hors diagonale codent les produits `p_i p_j` force un petit
spread quadratique de `p`. La borne est indépendante du cardinal.

**EN.** Generic quantitative Gram-matrix stability. An orthonormal family
`xi` is the reference; a nearby family `zeta` whose off-diagonal overlaps
encode the products `p_i p_j` forces a small quadratic spread of `p`.
The bound is cardinality-free.
-/

namespace EverettianDecoherence.Metrics

open scoped BigOperators InnerProductSpace

noncomputable section

private theorem sq_add_three_le_three_mul_sum_sq (a b c : ℝ) :
    (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

private theorem norm_inner_sq_le_three_error_terms
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {u v u₀ v₀ : E} (huv : inner ℂ u₀ v₀ = 0) :
    ‖inner ℂ u v‖ ^ 2 ≤
      3 * (
        ‖inner ℂ (u - u₀) v₀‖ ^ 2 +
        ‖inner ℂ u₀ (v - v₀)‖ ^ 2 +
        ‖inner ℂ (u - u₀) (v - v₀)‖ ^ 2) := by
  have hinner :
      inner ℂ u v =
        inner ℂ (u - u₀) v₀ +
        inner ℂ u₀ (v - v₀) +
        inner ℂ (u - u₀) (v - v₀) := by
    calc
      inner ℂ u v =
          inner ℂ ((u - u₀) + u₀) ((v - v₀) + v₀) := by
            congr <;> abel
      _ =
          inner ℂ (u - u₀) v₀ +
          inner ℂ u₀ (v - v₀) +
          inner ℂ (u - u₀) (v - v₀) +
          inner ℂ u₀ v₀ := by
            simp only [inner_add_left, inner_add_right]
            abel
      _ =
          inner ℂ (u - u₀) v₀ +
          inner ℂ u₀ (v - v₀) +
          inner ℂ (u - u₀) (v - v₀) := by
            rw [huv, add_zero]
  have hnorm :
      ‖inner ℂ u v‖ ≤
        ‖inner ℂ (u - u₀) v₀‖ +
        ‖inner ℂ u₀ (v - v₀)‖ +
        ‖inner ℂ (u - u₀) (v - v₀)‖ := by
    rw [hinner]
    calc
      ‖inner ℂ (u - u₀) v₀ +
          inner ℂ u₀ (v - v₀) +
          inner ℂ (u - u₀) (v - v₀)‖ ≤
        ‖inner ℂ (u - u₀) v₀ + inner ℂ u₀ (v - v₀)‖ +
          ‖inner ℂ (u - u₀) (v - v₀)‖ := norm_add_le _ _
      _ ≤
        (‖inner ℂ (u - u₀) v₀‖ + ‖inner ℂ u₀ (v - v₀)‖) +
          ‖inner ℂ (u - u₀) (v - v₀)‖ := by
            gcongr
            exact norm_add_le _ _
  have hsq :
      ‖inner ℂ u v‖ ^ 2 ≤
        (‖inner ℂ (u - u₀) v₀‖ +
          ‖inner ℂ u₀ (v - v₀)‖ +
          ‖inner ℂ (u - u₀) (v - v₀)‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (by positivity)).2 hnorm
  exact hsq.trans (sq_add_three_le_three_mul_sum_sq _ _ _)

/-- Generic off-diagonal Gram stability. If the off-diagonal overlaps of
`zeta` encode `p i * p j`, then their total spread is controlled by the
squared distance from an orthonormal family `xi`.

The right-hand side is `6 q + 3 q^2`, where
`q = sum_i ||zeta_i - xi_i||^2`. -/
theorem gram_offDiagonal_spread_le
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ξ ζ : ι → E) (p : ι → ℝ)
    (hξ : Orthonormal ℂ ξ)
    (hp : ∀ i, 0 ≤ p i)
    (hgram : ∀ i j, i ≠ j →
      p i * p j = ‖inner ℂ (ζ i) (ζ j)‖ ^ 2) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, p i * p j) ≤
      6 * (∑ i, ‖ζ i - ξ i‖ ^ 2) +
        3 * (∑ i, ‖ζ i - ξ i‖ ^ 2) ^ 2 := by
  let e : ι → E := fun i => ζ i - ξ i
  let q : ℝ := ∑ i, ‖e i‖ ^ 2
  let T₁ : ℝ :=
    ∑ i, ∑ j ∈ Finset.univ.erase i, ‖inner ℂ (e i) (ξ j)‖ ^ 2
  let T₂ : ℝ :=
    ∑ i, ∑ j ∈ Finset.univ.erase i, ‖inner ℂ (ξ i) (e j)‖ ^ 2
  let T₃ : ℝ :=
    ∑ i, ∑ j ∈ Finset.univ.erase i, ‖inner ℂ (e i) (e j)‖ ^ 2
  have hpair :
      ∀ i j, i ≠ j →
        p i * p j ≤
          3 * (
            ‖inner ℂ (e i) (ξ j)‖ ^ 2 +
            ‖inner ℂ (ξ i) (e j)‖ ^ 2 +
            ‖inner ℂ (e i) (e j)‖ ^ 2) := by
    intro i j hij
    rw [hgram i j hij]
    exact norm_inner_sq_le_three_error_terms (hξ.inner_eq_zero hij)
  have hspread :
      (∑ i, ∑ j ∈ Finset.univ.erase i, p i * p j) ≤
        3 * (T₁ + T₂ + T₃) := by
    calc
      (∑ i, ∑ j ∈ Finset.univ.erase i, p i * p j) ≤
          ∑ i, ∑ j ∈ Finset.univ.erase i,
            3 * (
              ‖inner ℂ (e i) (ξ j)‖ ^ 2 +
              ‖inner ℂ (ξ i) (e j)‖ ^ 2 +
              ‖inner ℂ (e i) (e j)‖ ^ 2) := by
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j hj
            exact hpair i j (Finset.ne_of_mem_erase hj).symm
      _ = 3 * (T₁ + T₂ + T₃) := by
        simp only [T₁, T₂, T₃, Finset.mul_sum, Finset.sum_add_distrib]
        ring
  have hT₁ : T₁ ≤ q := by
    calc
      T₁ ≤ ∑ i, ∑ j, ‖inner ℂ (e i) (ξ j)‖ ^ 2 := by
        dsimp [T₁]
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.erase_subset _ _)
          (by intro j _ _; positivity)
      _ ≤ ∑ i, ‖e i‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa [norm_inner_symm] using hξ.sum_inner_products_le (e i)
      _ = q := by rfl
  have hT₂ : T₂ ≤ q := by
    calc
      T₂ ≤ ∑ i, ∑ j, ‖inner ℂ (ξ i) (e j)‖ ^ 2 := by
        dsimp [T₂]
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.erase_subset _ _)
          (by intro j _ _; positivity)
      _ = ∑ j, ∑ i, ‖inner ℂ (ξ i) (e j)‖ ^ 2 := by
        rw [Finset.sum_comm]
      _ ≤ ∑ j, ‖e j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact hξ.sum_inner_products_le (e j)
      _ = q := by rfl
  have hT₃ : T₃ ≤ q ^ 2 := by
    calc
      T₃ ≤ ∑ i, ∑ j, ‖e i‖ ^ 2 * ‖e j‖ ^ 2 := by
        dsimp [T₃]
        apply Finset.sum_le_sum
        intro i _
        calc
          (∑ j ∈ Finset.univ.erase i, ‖inner ℂ (e i) (e j)‖ ^ 2) ≤
              ∑ j ∈ Finset.univ.erase i, ‖e i‖ ^ 2 * ‖e j‖ ^ 2 := by
                apply Finset.sum_le_sum
                intro j _
                have hinner := norm_inner_le_norm (e i) (e j)
                exact (sq_le_sq₀ (norm_nonneg _)
                  (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hinner
          _ ≤ ∑ j, ‖e i‖ ^ 2 * ‖e j‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.erase_subset _ _)
              (by intro j _ _; positivity)
      _ = q ^ 2 := by
        dsimp [q]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_mul]
        ring
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hsum : T₁ + T₂ + T₃ ≤ 2 * q + q ^ 2 := by
    nlinarith
  calc
    (∑ i, ∑ j ∈ Finset.univ.erase i, p i * p j)
        ≤ 3 * (T₁ + T₂ + T₃) := hspread
    _ ≤ 3 * (2 * q + q ^ 2) := by gcongr
    _ = 6 * (∑ i, ‖ζ i - ξ i‖ ^ 2) +
        3 * (∑ i, ‖ζ i - ξ i‖ ^ 2) ^ 2 := by
      dsimp [q, e]
      ring

/-- Linearized cardinality-free Gram stability. If the total squared error is
at most `12 e` and `e ≤ 1/2`, then the off-diagonal spread is at most
`288 e`. -/
theorem gram_offDiagonal_spread_le_288
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ξ ζ : ι → E) (p : ι → ℝ) (ε : ℝ)
    (hξ : Orthonormal ℂ ξ)
    (hp : ∀ i, 0 ≤ p i)
    (hgram : ∀ i j, i ≠ j →
      p i * p j = ‖inner ℂ (ζ i) (ζ j)‖ ^ 2)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hclose : (∑ i, ‖ζ i - ξ i‖ ^ 2) ≤ 12 * ε) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, p i * p j) ≤ 288 * ε := by
  have hbase := gram_offDiagonal_spread_le ξ ζ p hξ hp hgram
  let q : ℝ := ∑ i, ‖ζ i - ξ i‖ ^ 2
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq : q ≤ 12 * ε := by simpa [q] using hclose
  have hq_sq : q ^ 2 ≤ 144 * ε ^ 2 := by
    nlinarith
  have hεsq : ε ^ 2 ≤ ε / 2 := by
    nlinarith
  have hbound : 6 * q + 3 * q ^ 2 ≤ 288 * ε := by
    nlinarith
  exact hbase.trans hbound



/-- Sharper linearized Gram stability for the residual normalization used in
the T5 application. If the total squared error is at most 2 e and e ≤ 1/2,
then the off-diagonal spread is at most 18 e. -/
theorem gram_offDiagonal_spread_le_18
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ξ ζ : ι → E) (p : ι → ℝ) (ε : ℝ)
    (hξ : Orthonormal ℂ ξ)
    (hp : ∀ i, 0 ≤ p i)
    (hgram : ∀ i j, i ≠ j →
      p i * p j = ‖inner ℂ (ζ i) (ζ j)‖ ^ 2)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hclose : (∑ i, ‖ζ i - ξ i‖ ^ 2) ≤ 2 * ε) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, p i * p j) ≤ 18 * ε := by
  have hbase := gram_offDiagonal_spread_le ξ ζ p hξ hp hgram
  let q : ℝ := ∑ i, ‖ζ i - ξ i‖ ^ 2
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq : q ≤ 2 * ε := by simpa [q] using hclose
  have hq_sq : q ^ 2 ≤ 4 * ε ^ 2 := by
    nlinarith
  have hεsq : ε ^ 2 ≤ ε / 2 := by
    nlinarith
  have hbound : 6 * q + 3 * q ^ 2 ≤ 18 * ε := by
    nlinarith
  exact hbase.trans hbound


/-- Dominant-index inverse theorem for the sharper T5 normalization. If the
total squared error is at most 2 e, e ≤ 1/2, and the total p-mass is at least
L > 0, then one index leaves tail mass at most 18 e / L. -/
theorem exists_dominant_of_gram_close_18
    {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ξ ζ : ι → E) (p : ι → ℝ) (ε L : ℝ)
    (hξ : Orthonormal ℂ ξ)
    (hp : ∀ i, 0 ≤ p i)
    (hgram : ∀ i j, i ≠ j →
      p i * p j = ‖inner ℂ (ζ i) (ζ j)‖ ^ 2)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hclose : (∑ i, ‖ζ i - ξ i‖ ^ 2) ≤ 2 * ε)
    (hL : L ≤ ∑ i, p i) (hLpos : 0 < L) :
    ∃ i : ι, (∑ j ∈ Finset.univ.erase i, p j) ≤ (18 * ε) / L := by
  have hgramSpread :=
    gram_offDiagonal_spread_le_18 ξ ζ p ε hξ hp hgram hε0 hεhalf hclose
  have hspread :
      (∑ i, p i) ^ 2 - (∑ i, p i ^ 2) ≤ 18 * ε := by
    rw [← sum_offDiagonal_mul_eq_sum_sq_sub_sum_sq p]
    exact hgramSpread
  obtain ⟨i, _hi, htail⟩ :=
    exists_tail_le_of_spread_le
      (Finset.univ : Finset ι) p (18 * ε) L
      Finset.univ_nonempty
      (by intro j _; exact hp j)
      (by simpa using hspread)
      (by simpa using hL) hLpos
  exact ⟨i, by simpa using htail⟩

/-- Cardinality-free inverse theorem obtained by composing Gram stability with
the finite concentration lemma. -/
theorem exists_dominant_of_gram_close
    {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ξ ζ : ι → E) (p : ι → ℝ) (ε L : ℝ)
    (hξ : Orthonormal ℂ ξ)
    (hp : ∀ i, 0 ≤ p i)
    (hgram : ∀ i j, i ≠ j →
      p i * p j = ‖inner ℂ (ζ i) (ζ j)‖ ^ 2)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hclose : (∑ i, ‖ζ i - ξ i‖ ^ 2) ≤ 12 * ε)
    (hL : L ≤ ∑ i, p i) (hLpos : 0 < L) :
    ∃ i : ι, (∑ j ∈ Finset.univ.erase i, p j) ≤ (288 * ε) / L := by
  have hgramSpread :=
    gram_offDiagonal_spread_le_288 ξ ζ p ε hξ hp hgram hε0 hεhalf hclose
  have hspread :
      (∑ i, p i) ^ 2 - (∑ i, p i ^ 2) ≤ 288 * ε := by
    rw [← sum_offDiagonal_mul_eq_sum_sq_sub_sum_sq p]
    exact hgramSpread
  obtain ⟨i, _hi, htail⟩ :=
    exists_tail_le_of_spread_le
      (Finset.univ : Finset ι) p (288 * ε) L
      Finset.univ_nonempty
      (by intro j _; exact hp j)
      (by simpa using hspread)
      (by simpa using hL) hLpos
  exact ⟨i, by simpa using htail⟩

end
end EverettianDecoherence.Metrics

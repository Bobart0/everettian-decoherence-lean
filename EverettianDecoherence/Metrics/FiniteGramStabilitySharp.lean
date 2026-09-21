import EverettianDecoherence.Metrics.FiniteGramStability

/-!
**FR.** Raffinement cardinalité-indépendant de la stabilité de Gram utilisé
par le front v12. Le regroupement des deux termes linéaires avant l'inégalité
de Young donne
  spread <= (28/5) q + (7/2) q^2.
Combiné au contrôle q <= (47/40) e sur les bonnes cellules, cela donne la
constante linéaire 9.

**EN.** Cardinality-free refinement of the Gram stability estimate used by
the v12 front. Grouping the two linear terms before applying Young's
inequality gives
  spread <= (28/5) q + (7/2) q^2.
Combined with q <= (47/40) e on good cells, this yields the linear constant 9.
-/

namespace EverettianDecoherence.Metrics

open scoped BigOperators InnerProductSpace

noncomputable section

private theorem sq_add_three_le_weighted (a b c : ℝ) :
    (a + b + c) ^ 2 ≤
      (14 / 5 : ℝ) * (a ^ 2 + b ^ 2) + (7 / 2 : ℝ) * c ^ 2 := by
  have hab : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (a - b)]
  have habc :
      ((a + b) + c) ^ 2 ≤
        (7 / 5 : ℝ) * (a + b) ^ 2 + (7 / 2 : ℝ) * c ^ 2 := by
    nlinarith [sq_nonneg (2 * (a + b) - 5 * c)]
  nlinarith

private theorem norm_inner_sq_le_weighted_error_terms
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {u v u₀ v₀ : E} (huv : inner ℂ u₀ v₀ = 0) :
    ‖inner ℂ u v‖ ^ 2 ≤
      (14 / 5 : ℝ) *
        (‖inner ℂ (u - u₀) v₀‖ ^ 2 +
          ‖inner ℂ u₀ (v - v₀)‖ ^ 2) +
      (7 / 2 : ℝ) * ‖inner ℂ (u - u₀) (v - v₀)‖ ^ 2 := by
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
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
  exact hsq.trans (sq_add_three_le_weighted _ _ _)

/-- Weighted off-diagonal Gram stability. -/
theorem gram_offDiagonal_spread_le_weighted
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ξ ζ : ι → E) (p : ι → ℝ)
    (hξ : Orthonormal ℂ ξ)
    (hp : ∀ i, 0 ≤ p i)
    (hgram : ∀ i j, i ≠ j →
      p i * p j = ‖inner ℂ (ζ i) (ζ j)‖ ^ 2) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, p i * p j) ≤
      (28 / 5 : ℝ) * (∑ i, ‖ζ i - ξ i‖ ^ 2) +
        (7 / 2 : ℝ) * (∑ i, ‖ζ i - ξ i‖ ^ 2) ^ 2 := by
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
          (14 / 5 : ℝ) *
            (‖inner ℂ (e i) (ξ j)‖ ^ 2 +
              ‖inner ℂ (ξ i) (e j)‖ ^ 2) +
          (7 / 2 : ℝ) * ‖inner ℂ (e i) (e j)‖ ^ 2 := by
    intro i j hij
    rw [hgram i j hij]
    exact norm_inner_sq_le_weighted_error_terms (hξ.inner_eq_zero hij)
  have hspread :
      (∑ i, ∑ j ∈ Finset.univ.erase i, p i * p j) ≤
        (14 / 5 : ℝ) * (T₁ + T₂) + (7 / 2 : ℝ) * T₃ := by
    calc
      (∑ i, ∑ j ∈ Finset.univ.erase i, p i * p j) ≤
          ∑ i, ∑ j ∈ Finset.univ.erase i,
            ((14 / 5 : ℝ) *
              (‖inner ℂ (e i) (ξ j)‖ ^ 2 +
                ‖inner ℂ (ξ i) (e j)‖ ^ 2) +
              (7 / 2 : ℝ) * ‖inner ℂ (e i) (e j)‖ ^ 2) := by
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j hj
            exact hpair i j (Finset.ne_of_mem_erase hj).symm
      _ = (14 / 5 : ℝ) * (T₁ + T₂) + (7 / 2 : ℝ) * T₃ := by
        dsimp [T₁, T₂, T₃]
        simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
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
                have hinner :
                    ‖inner ℂ (e i) (e j)‖ ≤ ‖e i‖ * ‖e j‖ :=
                  norm_inner_le_norm (𝕜 := ℂ) (e i) (e j)
                calc
                  ‖inner ℂ (e i) (e j)‖ ^ 2 ≤
                      (‖e i‖ * ‖e j‖) ^ 2 :=
                    (sq_le_sq₀ (norm_nonneg _)
                      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hinner
                  _ = ‖e i‖ ^ 2 * ‖e j‖ ^ 2 := by ring
          _ ≤ ∑ j, ‖e i‖ ^ 2 * ‖e j‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.erase_subset _ _)
              (by intro j _ _; positivity)
      _ = q ^ 2 := by
        dsimp [q]
        have hinnerSum (i : ι) :
            (∑ j : ι, ‖e i‖ ^ 2 * ‖e j‖ ^ 2) =
              ‖e i‖ ^ 2 * (∑ j : ι, ‖e j‖ ^ 2) := by
          simpa using
            (Finset.mul_sum (Finset.univ : Finset ι)
              (fun j => ‖e j‖ ^ 2) (‖e i‖ ^ 2)).symm
        calc
          (∑ i : ι, ∑ j : ι, ‖e i‖ ^ 2 * ‖e j‖ ^ 2) =
              ∑ i : ι, ‖e i‖ ^ 2 * (∑ j : ι, ‖e j‖ ^ 2) := by
                apply Finset.sum_congr rfl
                intro i hi
                exact hinnerSum i
          _ = (∑ i : ι, ‖e i‖ ^ 2) *
                (∑ j : ι, ‖e j‖ ^ 2) := by
                simpa using
                  (Finset.sum_mul (Finset.univ : Finset ι)
                    (fun i => ‖e i‖ ^ 2)
                    (∑ j : ι, ‖e j‖ ^ 2)).symm
          _ = (∑ i : ι, ‖e i‖ ^ 2) ^ 2 := by ring
  have hsum :
      (14 / 5 : ℝ) * (T₁ + T₂) + (7 / 2 : ℝ) * T₃ ≤
        (28 / 5 : ℝ) * q + (7 / 2 : ℝ) * q ^ 2 := by
    nlinarith
  calc
    (∑ i, ∑ j ∈ Finset.univ.erase i, p i * p j)
        ≤ (14 / 5 : ℝ) * (T₁ + T₂) + (7 / 2 : ℝ) * T₃ := hspread
    _ ≤ (28 / 5 : ℝ) * q + (7 / 2 : ℝ) * q ^ 2 := hsum
    _ = (28 / 5 : ℝ) * (∑ i, ‖ζ i - ξ i‖ ^ 2) +
        (7 / 2 : ℝ) * (∑ i, ‖ζ i - ξ i‖ ^ 2) ^ 2 := by
      rfl

/-- Rational linearization for the v12 finite stability theorem. -/
theorem gram_offDiagonal_spread_le_9
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ξ ζ : ι → E) (p : ι → ℝ) (ε : ℝ)
    (hξ : Orthonormal ℂ ξ)
    (hp : ∀ i, 0 ≤ p i)
    (hgram : ∀ i j, i ≠ j →
      p i * p j = ‖inner ℂ (ζ i) (ζ j)‖ ^ 2)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hclose :
      (∑ i, ‖ζ i - ξ i‖ ^ 2) ≤ (47 / 40 : ℝ) * ε) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, p i * p j) ≤ 9 * ε := by
  have hbase := gram_offDiagonal_spread_le_weighted ξ ζ p hξ hp hgram
  let q : ℝ := ∑ i, ‖ζ i - ξ i‖ ^ 2
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq : q ≤ (47 / 40 : ℝ) * ε := by
    simpa [q] using hclose
  have hcoef0 : 0 ≤ (47 / 40 : ℝ) * ε :=
    mul_nonneg (by norm_num) hε0
  have hq_sq :
      q ^ 2 ≤ ((47 / 40 : ℝ) * ε) ^ 2 :=
    (sq_le_sq₀ hq0 hcoef0).2 hq
  have hεsq : ε ^ 2 ≤ ε / 2 := by
    nlinarith
  have hbound :
      (28 / 5 : ℝ) * q + (7 / 2 : ℝ) * q ^ 2 ≤ 9 * ε := by
    nlinarith
  exact hbase.trans hbound

/-- Dominant-index inverse theorem with tail constant 9. -/
theorem exists_dominant_of_gram_close_9
    {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ξ ζ : ι → E) (p : ι → ℝ) (ε L : ℝ)
    (hξ : Orthonormal ℂ ξ)
    (hp : ∀ i, 0 ≤ p i)
    (hgram : ∀ i j, i ≠ j →
      p i * p j = ‖inner ℂ (ζ i) (ζ j)‖ ^ 2)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hclose :
      (∑ i, ‖ζ i - ξ i‖ ^ 2) ≤ (47 / 40 : ℝ) * ε)
    (hL : L ≤ ∑ i, p i) (hLpos : 0 < L) :
    ∃ i : ι, (∑ j ∈ Finset.univ.erase i, p j) ≤ (9 * ε) / L := by
  have hgramSpread :=
    gram_offDiagonal_spread_le_9 ξ ζ p ε hξ hp hgram
      hε0 hεhalf hclose
  have hspread :
      (∑ i, p i) ^ 2 - (∑ i, p i ^ 2) ≤ 9 * ε := by
    rw [← sum_offDiagonal_mul_eq_sum_sq_sub_sum_sq p]
    exact hgramSpread
  obtain ⟨i, _hi, htail⟩ :=
    exists_tail_le_of_spread_le
      (Finset.univ : Finset ι) p (9 * ε) L
      Finset.univ_nonempty
      (by intro j _; exact hp j)
      (by simpa using hspread)
      (by simpa using hL) hLpos
  exact ⟨i, by simpa using htail⟩

end
end EverettianDecoherence.Metrics

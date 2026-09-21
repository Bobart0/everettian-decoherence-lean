import EverettianDecoherence.Metrics.FiniteGramStability

/-!
**FR.** Version paramétrique de la stabilité de Gram pour les limites v12.
Pour tout t>0,
  spread <= 4(1+t) q + (1+1/t) q^2.
En faisant tendre simultanément t et q vers zéro, le coefficient linéaire
tend vers la constante optimale 4.

**EN.** Parametric Gram stability for the v12 limit arguments. For every
t>0,
  spread <= 4(1+t) q + (1+1/t) q^2.
Letting t and q tend to zero together makes the linear coefficient converge
to the optimal constant 4.
-/

namespace EverettianDecoherence.Metrics

open scoped BigOperators InnerProductSpace

noncomputable section

private theorem sq_add_three_le_param
    (a b c t : ℝ) (ht : 0 < t) :
    (a + b + c) ^ 2 ≤
      2 * (1 + t) * (a ^ 2 + b ^ 2) +
        (1 + 1 / t) * c ^ 2 := by
  have hab : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (a - b)]
  have hcross :
      2 * (a + b) * c - t * (a + b) ^ 2 ≤ c ^ 2 / t := by
    apply (le_div_iff₀ ht).2
    nlinarith [sq_nonneg (t * (a + b) - c)]
  have hcross' :
      2 * (a + b) * c ≤ t * (a + b) ^ 2 + c ^ 2 / t := by
    linarith
  have hyoung :
      ((a + b) + c) ^ 2 ≤
        (1 + t) * (a + b) ^ 2 + (1 + 1 / t) * c ^ 2 := by
    calc
      ((a + b) + c) ^ 2 =
          (a + b) ^ 2 + 2 * (a + b) * c + c ^ 2 := by ring
      _ ≤ (a + b) ^ 2 +
          (t * (a + b) ^ 2 + c ^ 2 / t) + c ^ 2 := by
            linarith
      _ = (1 + t) * (a + b) ^ 2 +
          (1 + 1 / t) * c ^ 2 := by ring
  have hcoef : 0 ≤ 1 + t := by linarith
  calc
    (a + b + c) ^ 2 = ((a + b) + c) ^ 2 := by ring
    _ ≤ (1 + t) * (a + b) ^ 2 + (1 + 1 / t) * c ^ 2 := hyoung
    _ ≤ (1 + t) * (2 * (a ^ 2 + b ^ 2)) +
          (1 + 1 / t) * c ^ 2 := by
      gcongr
    _ = 2 * (1 + t) * (a ^ 2 + b ^ 2) +
          (1 + 1 / t) * c ^ 2 := by ring

private theorem norm_inner_sq_le_param_error_terms
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {u v u₀ v₀ : E} (huv : inner ℂ u₀ v₀ = 0)
    (t : ℝ) (ht : 0 < t) :
    ‖inner ℂ u v‖ ^ 2 ≤
      2 * (1 + t) *
        (‖inner ℂ (u - u₀) v₀‖ ^ 2 +
          ‖inner ℂ u₀ (v - v₀)‖ ^ 2) +
      (1 + 1 / t) *
        ‖inner ℂ (u - u₀) (v - v₀)‖ ^ 2 := by
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
  exact hsq.trans
    (sq_add_three_le_param _ _ _ t ht)

/-- Parametric cardinality-free off-diagonal Gram estimate. -/
theorem gram_offDiagonal_spread_le_param
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ξ ζ : ι → E) (p : ι → ℝ) (t : ℝ)
    (ht : 0 < t)
    (hξ : Orthonormal ℂ ξ)
    (hp : ∀ i, 0 ≤ p i)
    (hgram : ∀ i j, i ≠ j →
      p i * p j = ‖inner ℂ (ζ i) (ζ j)‖ ^ 2) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, p i * p j) ≤
      4 * (1 + t) * (∑ i, ‖ζ i - ξ i‖ ^ 2) +
        (1 + 1 / t) * (∑ i, ‖ζ i - ξ i‖ ^ 2) ^ 2 := by
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
          2 * (1 + t) *
            (‖inner ℂ (e i) (ξ j)‖ ^ 2 +
              ‖inner ℂ (ξ i) (e j)‖ ^ 2) +
          (1 + 1 / t) *
            ‖inner ℂ (e i) (e j)‖ ^ 2 := by
    intro i j hij
    rw [hgram i j hij]
    exact norm_inner_sq_le_param_error_terms
      (hξ.inner_eq_zero hij) t ht
  have hspread :
      (∑ i, ∑ j ∈ Finset.univ.erase i, p i * p j) ≤
        2 * (1 + t) * (T₁ + T₂) + (1 + 1 / t) * T₃ := by
    calc
      (∑ i, ∑ j ∈ Finset.univ.erase i, p i * p j) ≤
          ∑ i, ∑ j ∈ Finset.univ.erase i,
            (2 * (1 + t) *
              (‖inner ℂ (e i) (ξ j)‖ ^ 2 +
                ‖inner ℂ (ξ i) (e j)‖ ^ 2) +
              (1 + 1 / t) *
                ‖inner ℂ (e i) (e j)‖ ^ 2) := by
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j hj
            exact hpair i j (Finset.ne_of_mem_erase hj).symm
      _ = 2 * (1 + t) * (T₁ + T₂) + (1 + 1 / t) * T₃ := by
        dsimp [T₁, T₂, T₃]
        simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
        ring_nf
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
  have hcoef : 0 ≤ 2 * (1 + t) := by
    positivity
  have hcoef3 : 0 ≤ 1 + 1 / t := by
    have : 0 < 1 / t := one_div_pos.mpr ht
    linarith
  calc
    (∑ i, ∑ j ∈ Finset.univ.erase i, p i * p j)
        ≤ 2 * (1 + t) * (T₁ + T₂) + (1 + 1 / t) * T₃ := hspread
    _ ≤ 2 * (1 + t) * (q + q) + (1 + 1 / t) * q ^ 2 := by
      gcongr
    _ = 4 * (1 + t) * q + (1 + 1 / t) * q ^ 2 := by ring
    _ = 4 * (1 + t) * (∑ i, ‖ζ i - ξ i‖ ^ 2) +
        (1 + 1 / t) * (∑ i, ‖ζ i - ξ i‖ ^ 2) ^ 2 := by
      rfl

end
end EverettianDecoherence.Metrics

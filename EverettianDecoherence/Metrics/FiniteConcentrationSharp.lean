import EverettianDecoherence.Metrics.FiniteConcentration

/-!
**FR.** Raffinement de la concentration finie dans le régime de petit spread.
Pour un profil positif de masse M, le spread quadratique contrôle d'abord la
queue T par K/M. En réinjectant ce contrôle dans l'identité
  spread >= 2 (M-T) T,
on gagne asymptotiquement un facteur deux :
  T <= K / (2 (L - K/L)).
Cette brique est purement réelle et cardinalité-indépendante.

**EN.** Refined finite concentration in the small-spread regime. For a
nonnegative profile of mass M, the quadratic spread first controls the tail
T by K/M. Feeding this back into
  spread >= 2 (M-T) T
gains an asymptotic factor two:
  T <= K / (2 (L - K/L)).
This layer is purely real and cardinality-free.
-/

namespace EverettianDecoherence.Metrics

open scoped BigOperators

noncomputable section

private theorem sum_sq_le_sq_sum_of_nonneg
    {α : Type*} [DecidableEq α]
    (S : Finset α) (p : α → ℝ)
    (hp : ∀ i ∈ S, 0 ≤ p i) :
    (∑ i ∈ S, p i ^ 2) ≤ (∑ i ∈ S, p i) ^ 2 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      have hpa : 0 ≤ p a := hp a (by simp)
      have hpS : ∀ i ∈ S, 0 ≤ p i := by
        intro i hi
        exact hp i (by simp [hi])
      have hsum0 : 0 ≤ ∑ i ∈ S, p i :=
        Finset.sum_nonneg fun i hi => hpS i hi
      have hih := ih hpS
      simp only [Finset.sum_insert, ha, Finset.mem_insert]
      nlinarith

/-- Small-spread refinement of the dominant-index tail estimate. -/
theorem exists_tail_le_of_spread_le_sharp
    {α : Type*} [DecidableEq α]
    (S : Finset α) (p : α → ℝ) (K L : ℝ) (hS : S.Nonempty)
    (hp : ∀ i ∈ S, 0 ≤ p i)
    (hspread :
      (∑ j ∈ S, p j) ^ 2 - (∑ j ∈ S, p j ^ 2) ≤ K)
    (hL : L ≤ ∑ j ∈ S, p j) (hLpos : 0 < L)
    (hK0 : 0 ≤ K) (hKlt : K < L ^ 2) :
    ∃ i ∈ S,
      (∑ j ∈ S.erase i, p j) ≤
        K / (2 * (L - K / L)) := by
  obtain ⟨i, hi, himax, hsq⟩ :=
    exists_max_with_sum_sq_le_mul_sum S p hS hp
  let M : ℝ := ∑ j ∈ S, p j
  let T : ℝ := ∑ j ∈ S.erase i, p j
  have hMpos : 0 < M := lt_of_lt_of_le hLpos hL
  have hM0 : 0 ≤ M := hMpos.le
  have hT0 : 0 ≤ T := by
    dsimp [T]
    exact Finset.sum_nonneg fun j hj =>
      hp j (Finset.mem_of_mem_erase hj)
  have hdecomp : M = T + p i := by
    dsimp [M, T]
    simpa [add_comm] using (Finset.sum_erase_add S p hi).symm
  have hroughMul : T * M ≤ K := by
    have hprod :
        T * M ≤
          M ^ 2 - (∑ j ∈ S, p j ^ 2) := by
      calc
        T * M = M ^ 2 - p i * M := by
          rw [hdecomp]
          ring
        _ ≤ M ^ 2 - (∑ j ∈ S, p j ^ 2) := by
          linarith
    exact hprod.trans (by simpa [M] using hspread)
  have hrough : T ≤ K / L := by
    apply (le_div_iff₀ hLpos).2
    calc
      T * L ≤ T * M := by
        exact mul_le_mul_of_nonneg_left hL hT0
      _ ≤ K := hroughMul
  have hothersSq :
      (∑ j ∈ S.erase i, p j ^ 2) ≤ T ^ 2 := by
    simpa [T] using
      sum_sq_le_sq_sum_of_nonneg (S.erase i) p
        (by
          intro j hj
          exact hp j (Finset.mem_of_mem_erase hj))
  have hsumSqDecomp :
      (∑ j ∈ S, p j ^ 2) =
        p i ^ 2 + ∑ j ∈ S.erase i, p j ^ 2 := by
    have h :=
      Finset.sum_erase_add S (fun j => p j ^ 2) hi
    linarith
  have hspreadLower :
      2 * (M - T) * T ≤
        M ^ 2 - (∑ j ∈ S, p j ^ 2) := by
    have hpi : p i = M - T := by linarith [hdecomp]
    rw [hsumSqDecomp, hpi]
    nlinarith
  have hLT : L - K / L ≤ M - T := by
    linarith
  have hbasepos : 0 < L - K / L := by
    apply (sub_pos_iff_lt).2
    apply (div_lt_iff₀ hLpos).2
    simpa [pow_two, mul_comm] using hKlt
  have hcoefpos : 0 < 2 * (L - K / L) := by positivity
  have hmul :
      2 * (L - K / L) * T ≤ K := by
    calc
      2 * (L - K / L) * T ≤ 2 * (M - T) * T := by
        have := mul_le_mul_of_nonneg_right hLT hT0
        nlinarith
      _ ≤ M ^ 2 - (∑ j ∈ S, p j ^ 2) := hspreadLower
      _ ≤ K := by simpa [M] using hspread
  refine ⟨i, hi, ?_⟩
  apply (le_div_iff₀ hcoefpos).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

end
end EverettianDecoherence.Metrics

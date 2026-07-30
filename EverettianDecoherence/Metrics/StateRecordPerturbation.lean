import EverettianDecoherence.Metrics.FiniteProfileBounds
import EverettianDecoherence.Metrics.NormSquarePerturbation
import EverettianDecoherence.Metrics.RecordProfileL1

/-!
**FR.** Couche cinématique BORN-SENSITIVE utilisant `bornRecord`. Elle ne
définit aucune décohérence ni dynamique. La constante globale dépend du nombre
de cellules et n'est pas revendiquée optimale.

**EN.** BORN-SENSITIVE kinematic layer using `bornRecord`. It defines no
decoherence or dynamics. Its global constant depends on cell count and is not
claimed optimal.
-/

namespace EverettianDecoherence.Metrics

noncomputable def recordCellCount
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) : ℕ :=
  Fintype.card ((EverettianProbability.Abstract.Projective.interface n).Cell D)

noncomputable def recordProfilePerturbationBudget
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (x y : Gleason.H n) : ℝ :=
  (recordCellCount D : ℝ) * ((‖x‖ + ‖y‖) * ‖x - y‖)

theorem recordCellCount_nonneg_cast
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) :
    0 ≤ (recordCellCount D : ℝ) :=
  Nat.cast_nonneg _

theorem recordProfilePerturbationBudget_nonneg
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (x y : Gleason.H n) :
    0 ≤ recordProfilePerturbationBudget D x y :=
  mul_nonneg (recordCellCount_nonneg_cast D)
    (mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))

private theorem projL_norm_le
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D)
    (x : Gleason.H n) :
    ‖Gleason.projL c.val x‖ ≤ ‖x‖ :=
  c.val.norm_starProjection_apply_le x

theorem abs_bornRecord_sub_le_norm_sum_mul_norm_sub
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (x y : Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    |EverettianProbability.Abstract.bornRecord D x c -
        EverettianProbability.Abstract.bornRecord D y c| ≤
      (‖x‖ + ‖y‖) * ‖x - y‖ := by
  change |‖Gleason.projL c.val x‖ ^ 2 - ‖Gleason.projL c.val y‖ ^ 2| ≤ _
  refine (abs_norm_sq_sub_norm_sq_le (Gleason.projL c.val x)
    (Gleason.projL c.val y)).trans ?_
  have hsum : ‖Gleason.projL c.val x‖ + ‖Gleason.projL c.val y‖ ≤ ‖x‖ + ‖y‖ :=
    add_le_add (projL_norm_le D c x) (projL_norm_le D c y)
  have hsub : ‖Gleason.projL c.val x - Gleason.projL c.val y‖ ≤ ‖x - y‖ := by
    rw [← (Gleason.projL c.val).map_sub]
    exact projL_norm_le D c (x - y)
  exact mul_le_mul hsum hsub (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))

theorem recordProfileL1_le_card_mul_norm_sum_mul_norm_sub
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (x y : Gleason.H n) :
    recordProfileL1 D x y ≤ (recordCellCount D : ℝ) * ((‖x‖ + ‖y‖) * ‖x - y‖) := by
  simpa [recordProfileL1, recordProfile, recordCellCount] using
    (finiteProfileL1_le_card_mul_of_pointwise (recordProfile D x)
      (recordProfile D y) ((‖x‖ + ‖y‖) * ‖x - y‖)
      (fun c => abs_bornRecord_sub_le_norm_sum_mul_norm_sub D x y c))

theorem recordProfileL1_le_recordProfilePerturbationBudget
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (x y : Gleason.H n) :
    recordProfileL1 D x y ≤ recordProfilePerturbationBudget D x y :=
  recordProfileL1_le_card_mul_norm_sum_mul_norm_sub D x y

theorem recordProfileL1_le_two_mul_recordCellCount_mul_norm_sub
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (x y : Gleason.H n) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    recordProfileL1 D x y ≤ (2 * (recordCellCount D : ℝ)) * ‖x - y‖ := by
  calc
    recordProfileL1 D x y ≤ (recordCellCount D : ℝ) * ((‖x‖ + ‖y‖) * ‖x - y‖) :=
      recordProfileL1_le_card_mul_norm_sum_mul_norm_sub D x y
    _ = (2 * (recordCellCount D : ℝ)) * ‖x - y‖ := by rw [hx, hy]; ring

theorem recordProfileWithin_of_norm_sub_le
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (x y : Gleason.H n) (δ : ℝ) (hxy : ‖x - y‖ ≤ δ) :
    recordProfileWithin D ((recordCellCount D : ℝ) * ((‖x‖ + ‖y‖) * δ)) x y := by
  unfold recordProfileWithin
  calc
    recordProfileL1 D x y ≤ (recordCellCount D : ℝ) * ((‖x‖ + ‖y‖) * ‖x - y‖) :=
      recordProfileL1_le_card_mul_norm_sum_mul_norm_sub D x y
    _ ≤ (recordCellCount D : ℝ) * ((‖x‖ + ‖y‖) * δ) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hxy (add_nonneg (norm_nonneg _) (norm_nonneg _)))
        (recordCellCount_nonneg_cast D)

theorem recordProfileWithin_of_normalized_norm_sub_le
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (x y : Gleason.H n) (δ : ℝ)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ‖x - y‖ ≤ δ) :
    recordProfileWithin D ((2 * (recordCellCount D : ℝ)) * δ) x y := by
  unfold recordProfileWithin
  calc
    recordProfileL1 D x y ≤ (2 * (recordCellCount D : ℝ)) * ‖x - y‖ :=
      recordProfileL1_le_two_mul_recordCellCount_mul_norm_sub D x y hx hy
    _ ≤ (2 * (recordCellCount D : ℝ)) * δ := by
      apply mul_le_mul_of_nonneg_left hxy
      positivity

end EverettianDecoherence.Metrics

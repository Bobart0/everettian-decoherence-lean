import EverettianDecoherence.Approximation.IncomingWitnessThreshold
import EverettianDecoherence.Metrics.NormalizedResidualStabilityRatio
import EverettianDecoherence.Metrics.FiniteGramStabilityAsymptotic

/-!
**FR.** Familles normalisées pour un seuil variable beta. Sur les cellules
bonnes et actives, la famille xi_beta est orthonormale, la famille zeta_beta
encode exactement les produits p_i p_j hors diagonale, et
  q <= e / (1 - beta).
Cette borne tend vers e lorsque beta tend vers zéro.

**EN.** Normalized families for a variable threshold beta. On active good
cells, xi_beta is orthonormal, zeta_beta has off-diagonal Gram products
p_i p_j, and
  q <= e / (1 - beta).
This bound tends to e as beta tends to zero.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical InnerProductSpace

noncomputable section

noncomputable def incomingWitnessXiAt
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (β : ℝ)
    (i : ↥(incomingWitnessActiveGoodCellsAt D U S v β)) : H n :=
  (((Real.sqrt (incomingWitnessR D U i.1 v) : ℝ) : ℂ)⁻¹) •
    incomingWitnessCellVector D U i.1 v

noncomputable def incomingWitnessZetaAt
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (β : ℝ)
    (i : ↥(incomingWitnessActiveGoodCellsAt D U S v β)) : H n :=
  (((Real.sqrt (incomingWitnessR D U i.1 v) : ℝ) : ℂ)⁻¹) •
      Gleason.projL i.1.val (incomingWitnessCellVector D U i.1 v) +
    (((Real.sqrt (incomingWitnessP D U i.1) : ℝ) : ℂ)) • v

theorem incomingWitnessXiAt_norm
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (β : ℝ) (hβone : β < 1)
    (i : ↥(incomingWitnessActiveGoodCellsAt D U S v β)) :
    ‖incomingWitnessXiAt D U S v β i‖ = 1 := by
  have hrpos :=
    incomingWitnessR_pos_of_activeGoodAt D U S v β hβone i.1 i.2
  have hsqrt :
      Real.sqrt (incomingWitnessR D U i.1 v) =
        ‖incomingWitnessCellVector D U i.1 v‖ := by
    unfold incomingWitnessR
    exact Real.sqrt_sq (norm_nonneg _)
  have hnormpos :
      0 < ‖incomingWitnessCellVector D U i.1 v‖ := by
    unfold incomingWitnessR at hrpos
    nlinarith [norm_nonneg (incomingWitnessCellVector D U i.1 v)]
  unfold incomingWitnessXiAt
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hsqrt.symm ▸ hnormpos), hsqrt]
  field_simp [ne_of_gt hnormpos]

theorem incomingWitnessXiAt_inner_eq_zero_of_ne
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (β : ℝ)
    {i j : ↥(incomingWitnessActiveGoodCellsAt D U S v β)}
    (hij : i ≠ j) :
    inner ℂ (incomingWitnessXiAt D U S v β i)
      (incomingWitnessXiAt D U S v β j) = 0 := by
  have hval : i.1 ≠ j.1 := by
    intro h
    exact hij (Subtype.ext h)
  unfold incomingWitnessXiAt
  rw [inner_smul_left, inner_smul_right,
    incomingWitnessCellVector_inner_eq_zero_of_ne D U hval v]
  simp

theorem incomingWitnessXiAt_orthonormal
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (β : ℝ) (hβone : β < 1) :
    Orthonormal ℂ (incomingWitnessXiAt D U S v β) := by
  refine ⟨?_, ?_⟩
  · intro i
    exact incomingWitnessXiAt_norm D U S v β hβone i
  · intro i j hij
    exact incomingWitnessXiAt_inner_eq_zero_of_ne D U S v β hij

private theorem cellProjector_complWitness_eq_zero_at
    {n : ℕ} (D : Perspective n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : (Projective.interface n).Cell D) (hc : c ∈ S)
    (v : H n)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v) :
    Gleason.projL c.val v = 0 := by
  have h :=
    recordCellProjector_compl_apply_eq_zero_of_mem D S c hc v
  rw [hvcompl] at h
  exact h

private theorem projectedWitness_inner_projectedWitness_eq_zero_of_ne_at
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    {c d : (Projective.interface n).Cell D} (hcd : c ≠ d)
    (v : H n) :
    inner ℂ
      (Gleason.projL c.val (incomingWitnessCellVector D U c v))
      (Gleason.projL d.val (incomingWitnessCellVector D U d v)) = 0 := by
  have hcc : c.val ⟂ d.val :=
    D.ortho c.val c.property d.val d.property
      (fun hval => hcd (Subtype.ext hval))
  have hc_mem :
      Gleason.projL c.val (incomingWitnessCellVector D U c v) ∈ c.val :=
    Submodule.starProjection_apply_mem c.val _
  have hd_mem :
      Gleason.projL d.val (incomingWitnessCellVector D U d v) ∈ d.val :=
    Submodule.starProjection_apply_mem d.val _
  have hc_perp :
      Gleason.projL c.val (incomingWitnessCellVector D U c v) ∈ d.valᗮ :=
    hcc hc_mem
  have hz :
      inner ℂ
        (Gleason.projL d.val (incomingWitnessCellVector D U d v))
        (Gleason.projL c.val (incomingWitnessCellVector D U c v)) = 0 :=
    (Submodule.mem_orthogonal d.val _).mp hc_perp _ hd_mem
  rw [← inner_conj_symm
    (Gleason.projL c.val (incomingWitnessCellVector D U c v))
    (Gleason.projL d.val (incomingWitnessCellVector D U d v)), hz]
  simp

private theorem projectedWitness_inner_complWitness_eq_zero_at
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : (Projective.interface n).Cell D) (hc : c ∈ S)
    (v : H n)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v) :
    inner ℂ
      (Gleason.projL c.val (incomingWitnessCellVector D U c v)) v = 0 := by
  have hzero :=
    cellProjector_complWitness_eq_zero_at D S c hc v hvcompl
  change c.val.starProjection v = 0 at hzero
  change
    inner ℂ
      (c.val.starProjection (incomingWitnessCellVector D U c v)) v = 0
  rw [Submodule.inner_starProjection_left_eq_right c.val, hzero,
    inner_zero_right]

private theorem complWitness_inner_projectedWitness_eq_zero_at
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : (Projective.interface n).Cell D) (hc : c ∈ S)
    (v : H n)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v) :
    inner ℂ v
      (Gleason.projL c.val (incomingWitnessCellVector D U c v)) = 0 := by
  rw [← inner_conj_symm,
    projectedWitness_inner_complWitness_eq_zero_at
      D U S c hc v hvcompl]
  simp

theorem incomingWitnessZetaAt_gram
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (hv : ‖v‖ = 1)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v)
    (β : ℝ)
    (i j : ↥(incomingWitnessActiveGoodCellsAt D U S v β))
    (hij : i ≠ j) :
    incomingWitnessP D U i.1 * incomingWitnessP D U j.1 =
      ‖inner ℂ (incomingWitnessZetaAt D U S v β i)
        (incomingWitnessZetaAt D U S v β j)‖ ^ 2 := by
  have hi :=
    (mem_incomingWitnessActiveGoodCellsAt D U S v β i.1).mp i.2
  have hj :=
    (mem_incomingWitnessActiveGoodCellsAt D U S v β j.1).mp j.2
  have hval : i.1 ≠ j.1 := by
    intro h
    exact hij (Subtype.ext h)
  have hpp :=
    projectedWitness_inner_projectedWitness_eq_zero_of_ne_at
      D U hval v
  have hipv :=
    projectedWitness_inner_complWitness_eq_zero_at
      D U S i.1 hi.1 v hvcompl
  have hvpj :=
    complWitness_inner_projectedWitness_eq_zero_at
      D U S j.1 hj.1 v hvcompl
  have hpi0 : 0 ≤ incomingWitnessP D U i.1 :=
    incomingWitnessP_nonneg D U i.1
  have hpj0 : 0 ≤ incomingWitnessP D U j.1 :=
    incomingWitnessP_nonneg D U j.1
  unfold incomingWitnessZetaAt
  simp only [inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, hpp, hipv, hvpj, mul_zero, zero_mul, add_zero,
    zero_add, inner_self_eq_norm_sq, hv, one_pow, mul_one]
  simp [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt hpi0, Real.sq_sqrt hpj0, mul_pow]
  rw [hv]
  norm_num
  ring

theorem incomingWitnessXiAt_sub_ZetaAt_norm_sq_le
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (hv : ‖v‖ = 1)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v)
    (β : ℝ) (hβ0 : 0 < β) (hβone : β < 1)
    (i : ↥(incomingWitnessActiveGoodCellsAt D U S v β)) :
    ‖incomingWitnessXiAt D U S v β i -
        incomingWitnessZetaAt D U S v β i‖ ^ 2 ≤
      incomingWitnessAlpha D U i.1 v / (1 - β) := by
  have hi :=
    (mem_incomingWitnessActiveGoodCellsAt D U S v β i.1).mp i.2
  have hrpos :=
    incomingWitnessR_pos_of_activeGoodAt D U S v β hβone i.1 i.2
  have halpha0 :=
    incomingWitnessAlpha_nonneg_of_mem
      D U S i.1 hi.1 v hv hvcompl
  have hp0 := incomingWitnessP_nonneg D U i.1
  have hrp :
      incomingWitnessR D U i.1 v ≤ incomingWitnessP D U i.1 := by
    unfold incomingWitnessAlpha at halpha0
    linarith
  have hrLower :
      (1 - β) * incomingWitnessP D U i.1 ≤
        incomingWitnessR D U i.1 v := by
    have hgood := hi.2.1
    unfold incomingWitnessAlpha at hgood
    nlinarith
  have hq :=
    incomingWitnessCellResidual_norm_sq_le D U i.1 v
  have hinner :=
    re_inner_incomingWitnessCellResidual_eq_norm_sq
      D U S i.1 hi.1 v hvcompl
  have hbase :=
    normalized_residual_close_ratio
      v (incomingWitnessCellResidual D U i.1 v)
      (incomingWitnessP D U i.1)
      (incomingWitnessR D U i.1 v)
      hv hrpos hrp hq hinner
  have hden : 0 < 1 - β := sub_pos.mpr hβone
  have hcoef :
      incomingWitnessP D U i.1 / incomingWitnessR D U i.1 v ≤
        1 / (1 - β) := by
    apply (div_le_iff₀ hrpos).2
    have htmp :
        incomingWitnessP D U i.1 ≤
          incomingWitnessR D U i.1 v / (1 - β) :=
      (le_div_iff₀ hden).2 (by
        simpa [mul_comm] using hrLower)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using htmp
  have hratio :
      (incomingWitnessP D U i.1 / incomingWitnessR D U i.1 v) *
          incomingWitnessAlpha D U i.1 v ≤
        incomingWitnessAlpha D U i.1 v / (1 - β) := by
    calc
      (incomingWitnessP D U i.1 / incomingWitnessR D U i.1 v) *
          incomingWitnessAlpha D U i.1 v ≤
        (1 / (1 - β)) * incomingWitnessAlpha D U i.1 v :=
          mul_le_mul_of_nonneg_right hcoef halpha0
      _ = incomingWitnessAlpha D U i.1 v / (1 - β) := by ring
  have hdiff :
      incomingWitnessXiAt D U S v β i -
          incomingWitnessZetaAt D U S v β i =
        (((Real.sqrt (incomingWitnessR D U i.1 v) : ℝ) : ℂ)⁻¹) •
            incomingWitnessCellResidual D U i.1 v -
          (((Real.sqrt (incomingWitnessP D U i.1) : ℝ) : ℂ)) • v := by
    unfold incomingWitnessXiAt incomingWitnessZetaAt
    unfold incomingWitnessCellResidual
    module
  rw [hdiff]
  have hbase' :
      ‖(((Real.sqrt (incomingWitnessR D U i.1 v) : ℝ) : ℂ)⁻¹) •
            incomingWitnessCellResidual D U i.1 v -
          (((Real.sqrt (incomingWitnessP D U i.1) : ℝ) : ℂ)) • v‖ ^ 2 ≤
        (incomingWitnessP D U i.1 / incomingWitnessR D U i.1 v) *
          (incomingWitnessP D U i.1 - incomingWitnessR D U i.1 v) :=
    hbase
  exact hbase'.trans (by
    simpa [incomingWitnessAlpha] using hratio)

theorem sum_incomingWitnessXiAt_sub_ZetaAt_norm_sq_le
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (hv : ‖v‖ = 1)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v)
    (β : ℝ) (hβ0 : 0 < β) (hβone : β < 1) :
    (∑ i : ↥(incomingWitnessActiveGoodCellsAt D U S v β),
        ‖incomingWitnessZetaAt D U S v β i -
          incomingWitnessXiAt D U S v β i‖ ^ 2) ≤
      (∑ c ∈ S, incomingWitnessAlpha D U c v) / (1 - β) := by
  have hden : 0 < 1 - β := sub_pos.mpr hβone
  calc
    (∑ i : ↥(incomingWitnessActiveGoodCellsAt D U S v β),
        ‖incomingWitnessZetaAt D U S v β i -
          incomingWitnessXiAt D U S v β i‖ ^ 2) ≤
      ∑ i : ↥(incomingWitnessActiveGoodCellsAt D U S v β),
        incomingWitnessAlpha D U i.1 v / (1 - β) := by
      apply Finset.sum_le_sum
      intro i _
      simpa [norm_sub_rev] using
        incomingWitnessXiAt_sub_ZetaAt_norm_sq_le
          D U S v hv hvcompl β hβ0 hβone i
    _ =
      (∑ i : ↥(incomingWitnessActiveGoodCellsAt D U S v β),
        incomingWitnessAlpha D U i.1 v) / (1 - β) := by
      rw [Finset.sum_div]
    _ ≤
      (∑ c ∈ S, incomingWitnessAlpha D U c v) / (1 - β) := by
      apply div_le_div_of_nonneg_right _ hden.le
      calc
        (∑ i : ↥(incomingWitnessActiveGoodCellsAt D U S v β),
            incomingWitnessAlpha D U i.1 v) =
          ∑ c ∈ incomingWitnessActiveGoodCellsAt D U S v β,
            incomingWitnessAlpha D U c v := by
              exact Finset.sum_coe_sort
                (incomingWitnessActiveGoodCellsAt D U S v β)
                (fun c => incomingWitnessAlpha D U c v)
        _ ≤ ∑ c ∈ S, incomingWitnessAlpha D U c v := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro c hc
            exact
              ((mem_incomingWitnessActiveGoodCellsAt
                D U S v β c).mp hc).1
          · intro c hcS _hcnot
            exact incomingWitnessAlpha_nonneg_of_mem
              D U S c hcS v hv hvcompl

end
end EverettianDecoherence.Approximation

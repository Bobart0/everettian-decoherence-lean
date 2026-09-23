import EverettianDecoherence.Approximation.IncomingWitnessBudget
import EverettianDecoherence.Metrics.FiniteGramStability

/-!
**FR.** Familles normalisées associées aux cellules bonnes et actives d'un
témoin entrant. La famille xi est orthonormale, la famille zeta a des
recouvrements hors diagonale dont les carrés sont exactement p_i p_j, et
l'erreur quadratique totale est contrôlée par deux fois le déficit local.

**EN.** Normalized families attached to the good active cells of an incoming
witness. The family xi is orthonormal, zeta has off-diagonal overlaps whose
squared norms are exactly p_i p_j, and the total squared error is bounded by
twice the total local deficit.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical InnerProductSpace

noncomputable section

noncomputable def incomingWitnessActiveGoodCells
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) :
    Finset ((Projective.interface n).Cell D) :=
  (incomingWitnessGoodCells D U S v).filter fun c =>
    0 < incomingWitnessP D U c

theorem mem_incomingWitnessActiveGoodCells
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (c : (Projective.interface n).Cell D) :
    c ∈ incomingWitnessActiveGoodCells D U S v ↔
      c ∈ S ∧
      incomingWitnessAlpha D U c v ≤ incomingWitnessP D U c / 2 ∧
      0 < incomingWitnessP D U c := by
  simp [incomingWitnessActiveGoodCells, incomingWitnessGoodCells,
    and_assoc]

theorem incomingWitnessR_pos_of_activeGood
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n)
    (c : (Projective.interface n).Cell D)
    (hc : c ∈ incomingWitnessActiveGoodCells D U S v) :
    0 < incomingWitnessR D U c v := by
  have h := (mem_incomingWitnessActiveGoodCells D U S v c).mp hc
  unfold incomingWitnessAlpha at h
  linarith

noncomputable def incomingWitnessXi
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n)
    (i : ↥(incomingWitnessActiveGoodCells D U S v)) : H n :=
  (((Real.sqrt (incomingWitnessR D U i.1 v) : ℝ) : ℂ)⁻¹) •
    incomingWitnessCellVector D U i.1 v

noncomputable def incomingWitnessZeta
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n)
    (i : ↥(incomingWitnessActiveGoodCells D U S v)) : H n :=
  (((Real.sqrt (incomingWitnessR D U i.1 v) : ℝ) : ℂ)⁻¹) •
      Gleason.projL i.1.val (incomingWitnessCellVector D U i.1 v) +
    (((Real.sqrt (incomingWitnessP D U i.1) : ℝ) : ℂ)) • v

theorem incomingWitnessXi_norm
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n)
    (i : ↥(incomingWitnessActiveGoodCells D U S v)) :
    ‖incomingWitnessXi D U S v i‖ = 1 := by
  have hrpos :=
    incomingWitnessR_pos_of_activeGood D U S v i.1 i.2
  have hsqrt :
      Real.sqrt (incomingWitnessR D U i.1 v) =
        ‖incomingWitnessCellVector D U i.1 v‖ := by
    unfold incomingWitnessR
    exact Real.sqrt_sq (norm_nonneg _)
  have hnormpos :
      0 < ‖incomingWitnessCellVector D U i.1 v‖ := by
    unfold incomingWitnessR at hrpos
    nlinarith [norm_nonneg (incomingWitnessCellVector D U i.1 v)]
  unfold incomingWitnessXi
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hsqrt.symm ▸ hnormpos), hsqrt]
  field_simp [ne_of_gt hnormpos]

theorem incomingWitnessXi_inner_eq_zero_of_ne
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n)
    {i j : ↥(incomingWitnessActiveGoodCells D U S v)}
    (hij : i ≠ j) :
    inner ℂ (incomingWitnessXi D U S v i)
      (incomingWitnessXi D U S v j) = 0 := by
  have hval : i.1 ≠ j.1 := by
    intro h
    exact hij (Subtype.ext h)
  unfold incomingWitnessXi
  rw [inner_smul_left, inner_smul_right,
    incomingWitnessCellVector_inner_eq_zero_of_ne D U hval v]
  simp

theorem incomingWitnessXi_orthonormal
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) :
    Orthonormal ℂ (incomingWitnessXi D U S v) := by
  refine ⟨?_, ?_⟩
  · intro i
    exact incomingWitnessXi_norm D U S v i
  · intro i j hij
    exact incomingWitnessXi_inner_eq_zero_of_ne D U S v hij

private theorem cellProjector_complWitness_eq_zero
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

private theorem projectedWitness_inner_projectedWitness_eq_zero_of_ne
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

private theorem projectedWitness_inner_complWitness_eq_zero
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
    cellProjector_complWitness_eq_zero D S c hc v hvcompl
  change c.val.starProjection v = 0 at hzero
  change
    inner ℂ
      (c.val.starProjection (incomingWitnessCellVector D U c v)) v = 0
  rw [Submodule.inner_starProjection_left_eq_right c.val, hzero,
    inner_zero_right]

private theorem complWitness_inner_projectedWitness_eq_zero
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : (Projective.interface n).Cell D) (hc : c ∈ S)
    (v : H n)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v) :
    inner ℂ v
      (Gleason.projL c.val (incomingWitnessCellVector D U c v)) = 0 := by
  rw [← inner_conj_symm, projectedWitness_inner_complWitness_eq_zero
    D U S c hc v hvcompl]
  simp

theorem incomingWitnessZeta_gram
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (hv : ‖v‖ = 1)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v)
    (i j : ↥(incomingWitnessActiveGoodCells D U S v))
    (hij : i ≠ j) :
    incomingWitnessP D U i.1 * incomingWitnessP D U j.1 =
      ‖inner ℂ (incomingWitnessZeta D U S v i)
        (incomingWitnessZeta D U S v j)‖ ^ 2 := by
  have hi :=
    (mem_incomingWitnessActiveGoodCells D U S v i.1).mp i.2
  have hj :=
    (mem_incomingWitnessActiveGoodCells D U S v j.1).mp j.2
  have hval : i.1 ≠ j.1 := by
    intro h
    exact hij (Subtype.ext h)
  have hpp :=
    projectedWitness_inner_projectedWitness_eq_zero_of_ne
      D U hval v
  have hipv :=
    projectedWitness_inner_complWitness_eq_zero
      D U S i.1 hi.1 v hvcompl
  have hvpj :=
    complWitness_inner_projectedWitness_eq_zero
      D U S j.1 hj.1 v hvcompl
  have hpi0 : 0 ≤ incomingWitnessP D U i.1 :=
    incomingWitnessP_nonneg D U i.1
  have hpj0 : 0 ≤ incomingWitnessP D U j.1 :=
    incomingWitnessP_nonneg D U j.1
  unfold incomingWitnessZeta
  simp only [inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, hpp, hipv, hvpj, mul_zero, zero_mul, add_zero,
    zero_add, inner_self_eq_norm_sq, hv, one_pow, mul_one]
  simp [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt hpi0, Real.sq_sqrt hpj0, mul_pow]
  rw [hv]
  norm_num
  ring

theorem incomingWitnessXi_sub_Zeta_norm_sq_le
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (hv : ‖v‖ = 1)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v)
    (i : ↥(incomingWitnessActiveGoodCells D U S v)) :
    ‖incomingWitnessXi D U S v i -
        incomingWitnessZeta D U S v i‖ ^ 2 ≤
      2 * incomingWitnessAlpha D U i.1 v := by
  have hi :=
    (mem_incomingWitnessActiveGoodCells D U S v i.1).mp i.2
  have hrpos :=
    incomingWitnessR_pos_of_activeGood D U S v i.1 i.2
  have halpha0 :=
    incomingWitnessAlpha_nonneg_of_mem
      D U S i.1 hi.1 v hv hvcompl
  have hrp :
      incomingWitnessR D U i.1 v ≤ incomingWitnessP D U i.1 := by
    unfold incomingWitnessAlpha at halpha0
    linarith
  have hq :=
    incomingWitnessCellResidual_norm_sq_le D U i.1 v
  have hinner :=
    re_inner_incomingWitnessCellResidual_eq_norm_sq
      D U S i.1 hi.1 v hvcompl
  have hbase :=
    normalized_residual_close
      v (incomingWitnessCellResidual D U i.1 v)
      (incomingWitnessP D U i.1)
      (incomingWitnessR D U i.1 v)
      hv hrpos hrp hq hinner
  have hdiff :
      incomingWitnessXi D U S v i -
          incomingWitnessZeta D U S v i =
        (((Real.sqrt (incomingWitnessR D U i.1 v) : ℝ) : ℂ)⁻¹) •
            incomingWitnessCellResidual D U i.1 v -
          (((Real.sqrt (incomingWitnessP D U i.1) : ℝ) : ℂ)) • v := by
    unfold incomingWitnessXi incomingWitnessZeta
    unfold incomingWitnessCellResidual
    module
  rw [hdiff]
  simpa [incomingWitnessAlpha] using hbase

theorem sum_incomingWitnessXi_sub_Zeta_norm_sq_le
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (hv : ‖v‖ = 1)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v) :
    (∑ i : ↥(incomingWitnessActiveGoodCells D U S v),
        ‖incomingWitnessXi D U S v i -
          incomingWitnessZeta D U S v i‖ ^ 2) ≤
      2 * (∑ c ∈ S, incomingWitnessAlpha D U c v) := by
  calc
    (∑ i : ↥(incomingWitnessActiveGoodCells D U S v),
        ‖incomingWitnessXi D U S v i -
          incomingWitnessZeta D U S v i‖ ^ 2) ≤
      ∑ i : ↥(incomingWitnessActiveGoodCells D U S v),
        2 * incomingWitnessAlpha D U i.1 v := by
      apply Finset.sum_le_sum
      intro i _
      exact incomingWitnessXi_sub_Zeta_norm_sq_le
        D U S v hv hvcompl i
    _ = 2 * ∑ i : ↥(incomingWitnessActiveGoodCells D U S v),
        incomingWitnessAlpha D U i.1 v := by
      rw [Finset.mul_sum]
    _ ≤ 2 * (∑ c ∈ S, incomingWitnessAlpha D U c v) := by
      have hactive :
          (∑ i : ↥(incomingWitnessActiveGoodCells D U S v),
              incomingWitnessAlpha D U i.1 v) ≤
            ∑ c ∈ S, incomingWitnessAlpha D U c v := by
        calc
          (∑ i : ↥(incomingWitnessActiveGoodCells D U S v),
              incomingWitnessAlpha D U i.1 v) =
              ∑ c ∈ incomingWitnessActiveGoodCells D U S v,
                incomingWitnessAlpha D U c v := by
            exact Finset.sum_coe_sort
              (incomingWitnessActiveGoodCells D U S v)
              (fun c => incomingWitnessAlpha D U c v)
          _ ≤ ∑ c ∈ S, incomingWitnessAlpha D U c v := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro c hc
              exact
                ((mem_incomingWitnessActiveGoodCells D U S v c).mp hc).1
            · intro c hcS _hcnot
              exact incomingWitnessAlpha_nonneg_of_mem
                D U S c hcS v hv hvcompl
      exact mul_le_mul_of_nonneg_left hactive (by norm_num)

end
end EverettianDecoherence.Approximation

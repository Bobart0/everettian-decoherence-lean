import EverettianDecoherence.Approximation.StabilitySharpness.V12TwoParameterGeometry
import EverettianDecoherence.Approximation.StabilitySharpness.GlobalBudget
import EverettianDecoherence.Approximation.MaxCutThresholdStability

/-!
**FR.** Invariants globaux de la réalisation géométrique v12 à deux
paramètres. Pour 0 ≤ d ≤ 1 et 0 ≤ x ≤ 1, le budget global vaut A(d,x),
le carré du max-cut vaut f_d(1), le défaut d'enveloppe vaut E(d,x), et la
queue top-two absolue est f_d(min(x,1-x)).

**EN.** Global invariants of the geometric v12 two-parameter realization.
For 0 ≤ d ≤ 1 and 0 ≤ x ≤ 1, the global budget is A(d,x), the squared
max-cut is f_d(1), the envelope defect is E(d,x), and the absolute top-two
tail is f_d(min(x,1-x)).
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped Classical BigOperators

noncomputable section

theorem v12TwoParamGap_nonneg
    (d y : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ v12TwoParamGap d y := by
  unfold v12TwoParamGap
  have hdy : d * y ≤ 1 := by
    calc
      d * y ≤ 1 * y := mul_le_mul_of_nonneg_right hd1 hy0
      _ = y := by ring
      _ ≤ 1 := hy1
  have hfac : 0 ≤ 2 - d * y := by linarith
  have hprod : 0 ≤ d * y * (2 - d * y) := by positivity
  nlinarith

theorem v12TwoParamGap_le_gap_one
    (d y : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    v12TwoParamGap d y ≤ v12TwoParamGap d 1 := by
  have hdy : d * y ≤ 1 := by
    calc
      d * y ≤ 1 * y := mul_le_mul_of_nonneg_right hd1 hy0
      _ = y := by ring
      _ ≤ 1 := hy1
  have hsecond : 0 ≤ 2 - d * (1 + y) := by
    have h1d : 0 ≤ 1 - d := sub_nonneg.mpr hd1
    have h1dy : 0 ≤ 1 - d * y := sub_nonneg.mpr hdy
    nlinarith
  have hfactor :
      0 ≤ d * (1 - y) * (2 - d * (1 + y)) := by
    positivity
  unfold v12TwoParamGap
  nlinarith

theorem v12TwoParam_globalSq
    (d x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    operatorNormProjectorCommutatorL2 stabilitySharpnessPerspective3
        (v12TwoParamRotation d x hx0 hx1 hd0 (hd1.trans (by norm_num))) ^ 2 =
      v12TwoParamGlobal d x := by
  rw [← sum_cellCommutatorOpNormSq_eq_globalSq]
  rw [sum_stabilitySharpnessCells]
  rw [Fin.sum_univ_three]
  rw [v12TwoParamCell0_budget_sq,
    v12TwoParamCell1_budget_sq,
    v12TwoParamCell2_budget_sq]
  exact v12TwoParam_gap_sum_eq_global d x

private theorem v12TwoParam_cell_budget_le_gap_one
    (d x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (c :
      (Projective.interface 3).Cell stabilitySharpnessPerspective3) :
    cellCommutatorOpNormSq stabilitySharpnessPerspective3
        (v12TwoParamRotation d x hx0 hx1 hd0 (hd1.trans (by norm_num))) c ≤
      v12TwoParamGap d 1 := by
  obtain ⟨i, hi⟩ := stabilitySharpnessCell3_bijective.2 c
  rw [← hi]
  fin_cases i
  · rw [v12TwoParamCell0_budget_sq]
    exact v12TwoParamGap_le_gap_one d (1 - x) hd0 hd1
      (sub_nonneg.mpr hx1) (by linarith)
  · rw [v12TwoParamCell1_budget_sq]
    exact v12TwoParamGap_le_gap_one d x hd0 hd1 hx0 hx1
  · rw [v12TwoParamCell2_budget_sq]

private theorem v12TwoParam_subset_opNorm_sq_le_gap_one_of_card_le_one
    (d x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (S :
      Finset ((Projective.interface 3).Cell stabilitySharpnessPerspective3))
    (hcard : S.card ≤ 1) :
    ‖recordSubsetProjectorCommutatorCLM stabilitySharpnessPerspective3
        (v12TwoParamRotation d x hx0 hx1 hd0 (hd1.trans (by norm_num))) S‖ ^ 2 ≤
      v12TwoParamGap d 1 := by
  by_cases hzero : S.card = 0
  · have hS : S = ∅ := Finset.card_eq_zero.mp hzero
    subst S
    have hsq :=
      recordSubsetProjectorCommutatorCLM_opNorm_sq_le_subsetSq
        stabilitySharpnessPerspective3
        (v12TwoParamRotation d x hx0 hx1 hd0 (hd1.trans (by norm_num))) ∅
    have hgap0 :=
      v12TwoParamGap_nonneg d 1 hd0 hd1 (by norm_num) (by norm_num)
    unfold subsetProjectorCommutatorOpNormSq at hsq
    simp at hsq
    exact hsq.trans hgap0
  · have hone : S.card = 1 := by omega
    obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp hone
    calc
      ‖recordSubsetProjectorCommutatorCLM stabilitySharpnessPerspective3
          (v12TwoParamRotation d x hx0 hx1 hd0 (hd1.trans (by norm_num))) {c}‖ ^ 2
          ≤ subsetProjectorCommutatorOpNormSq stabilitySharpnessPerspective3
              (v12TwoParamRotation d x hx0 hx1 hd0 (hd1.trans (by norm_num))) {c} :=
        recordSubsetProjectorCommutatorCLM_opNorm_sq_le_subsetSq
          stabilitySharpnessPerspective3
          (v12TwoParamRotation d x hx0 hx1 hd0 (hd1.trans (by norm_num))) {c}
      _ = cellCommutatorOpNormSq stabilitySharpnessPerspective3
              (v12TwoParamRotation d x hx0 hx1 hd0 (hd1.trans (by norm_num))) c := by
        rw [singletonSubsetCommutatorOpNormSq_eq_cell]
      _ ≤ v12TwoParamGap d 1 :=
        v12TwoParam_cell_budget_le_gap_one d x hx0 hx1 hd0 hd1 c

theorem v12TwoParam_subset_opNorm_sq_le_gap_one
    (d x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (S :
      Finset ((Projective.interface 3).Cell stabilitySharpnessPerspective3)) :
    ‖recordSubsetProjectorCommutatorCLM stabilitySharpnessPerspective3
        (v12TwoParamRotation d x hx0 hx1 hd0 (hd1.trans (by norm_num))) S‖ ^ 2 ≤
      v12TwoParamGap d 1 := by
  by_cases hsmall : S.card ≤ 1
  · exact v12TwoParam_subset_opNorm_sq_le_gap_one_of_card_le_one
      d x hx0 hx1 hd0 hd1 S hsmall
  · have htype :
        Fintype.card
          ((Projective.interface 3).Cell stabilitySharpnessPerspective3) = 3 := by
      calc
        Fintype.card
            ((Projective.interface 3).Cell stabilitySharpnessPerspective3) =
          Fintype.card (Fin 3) :=
            Fintype.card_congr stabilitySharpnessCellEquiv3.symm
        _ = 3 := Fintype.card_fin 3
    have hcompl : Sᶜ.card ≤ 1 := by
      rw [Finset.card_compl, htype]
      have hle : S.card ≤ 3 := by
        have := S.card_le_univ
        rwa [htype] at this
      omega
    have h :=
      v12TwoParam_subset_opNorm_sq_le_gap_one_of_card_le_one
        d x hx0 hx1 hd0 hd1 Sᶜ hcompl
    rw [recordSubsetProjectorCommutatorCLM_opNorm_compl
      stabilitySharpnessPerspective3
      (v12TwoParamRotation d x hx0 hx1 hd0 (hd1.trans (by norm_num))) S] at h
    exact h

theorem v12TwoParam_maxCut_sq_eq_gap_one
    (d x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    maxSubsetCommutatorOpNorm stabilitySharpnessPerspective3
        (v12TwoParamRotation d x hx0 hx1 hd0 (hd1.trans (by norm_num))) ^ 2 =
      v12TwoParamGap d 1 := by
  apply le_antisymm
  · obtain ⟨S, hS⟩ :=
      exists_subsetCommutatorOpNorm_eq_max
        stabilitySharpnessPerspective3
        (v12TwoParamRotation d x hx0 hx1 hd0 (hd1.trans (by norm_num)))
    rw [← hS]
    exact v12TwoParam_subset_opNorm_sq_le_gap_one
      d x hx0 hx1 hd0 hd1 S
  · let U :=
      v12TwoParamRotation d x hx0 hx1 hd0 (hd1.trans (by norm_num))
    let c := stabilitySharpnessCell3 (2 : Fin 3)
    have hle :
        ‖recordSubsetProjectorCommutatorCLM stabilitySharpnessPerspective3
            U {c}‖ ≤
          maxSubsetCommutatorOpNorm stabilitySharpnessPerspective3 U :=
      subsetCommutatorOpNorm_le_max
        stabilitySharpnessPerspective3 U {c}
    have hsq :
        ‖recordSubsetProjectorCommutatorCLM stabilitySharpnessPerspective3
            U {c}‖ ^ 2 ≤
          maxSubsetCommutatorOpNorm stabilitySharpnessPerspective3 U ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (maxSubsetCommutatorOpNorm_nonneg
          stabilitySharpnessPerspective3 U)).2 hle
    have hcell :
        ‖recordSubsetProjectorCommutatorCLM stabilitySharpnessPerspective3
            U {c}‖ ^ 2 =
          v12TwoParamGap d 1 := by
      rw [singletonSubsetCommutatorOpNormSq_eq_cell]
      exact v12TwoParamCell2_budget_sq
        d x hx0 hx1 hd0 (hd1.trans (by norm_num))
    rw [hcell] at hsq
    exact hsq

theorem v12TwoParam_envelopeDefect
    (d x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    maxCutEnvelopeDefect stabilitySharpnessPerspective3
        (v12TwoParamRotation d x hx0 hx1 hd0 (hd1.trans (by norm_num))) =
      v12TwoParamDefect d x := by
  unfold maxCutEnvelopeDefect
  rw [v12TwoParam_globalSq d x hx0 hx1 hd0 hd1]
  rw [v12TwoParam_maxCut_sq_eq_gap_one d x hx0 hx1 hd0 hd1]
  exact v12TwoParam_global_sub_two_gap_one_eq_defect d x

theorem v12TwoParam_min_cell_budget_eq_tail
    (d x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    min
      (cellCommutatorOpNormSq stabilitySharpnessPerspective3
        (v12TwoParamRotation d x hx0 hx1 hd0 (hd1.trans (by norm_num)))
        (stabilitySharpnessCell3 (0 : Fin 3)))
      (min
        (cellCommutatorOpNormSq stabilitySharpnessPerspective3
          (v12TwoParamRotation d x hx0 hx1 hd0 (hd1.trans (by norm_num)))
          (stabilitySharpnessCell3 (1 : Fin 3)))
        (cellCommutatorOpNormSq stabilitySharpnessPerspective3
          (v12TwoParamRotation d x hx0 hx1 hd0 (hd1.trans (by norm_num)))
          (stabilitySharpnessCell3 (2 : Fin 3)))) =
      v12TwoParamTail d x := by
  rw [v12TwoParamCell0_budget_sq,
    v12TwoParamCell1_budget_sq,
    v12TwoParamCell2_budget_sq]
  unfold v12TwoParamTail
  have hxcomp0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hxcomp1 : 1 - x ≤ 1 := by linarith
  have hx_le_one :=
    v12TwoParamGap_le_gap_one d x hd0 hd1 hx0 hx1
  have hxc_le_one :=
    v12TwoParamGap_le_gap_one d (1 - x) hd0 hd1 hxcomp0 hxcomp1
  rw [min_eq_left hx_le_one]
  by_cases h : x ≤ 1 - x
  · rw [min_eq_left h]
    have hmono :
        v12TwoParamGap d x ≤ v12TwoParamGap d (1 - x) := by
      have hfac : 0 ≤ d * ((1 - x) - x) *
          (2 - d * ((1 - x) + x)) := by
        have htwo : 0 ≤ 2 - d * ((1 - x) + x) := by
          simp
          linarith
        positivity
      unfold v12TwoParamGap
      nlinarith
    rw [min_eq_right hmono]
  · have h' : 1 - x ≤ x := le_of_not_ge h
    rw [min_eq_right h']
    have hmono :
        v12TwoParamGap d (1 - x) ≤ v12TwoParamGap d x := by
      have hfac : 0 ≤ d * (x - (1 - x)) *
          (2 - d * (x + (1 - x))) := by
        have htwo : 0 ≤ 2 - d * (x + (1 - x)) := by
          simp
          linarith
        positivity
      unfold v12TwoParamGap
      nlinarith
    rw [min_eq_left hmono]

noncomputable def v12TwoParamTopTwoTailFraction
    (d x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) : ℝ :=
  v12TwoParamTail d x /
    operatorNormProjectorCommutatorL2 stabilitySharpnessPerspective3
      (v12TwoParamRotation d x hx0 hx1 hd0 (hd1.trans (by norm_num))) ^ 2

theorem v12TwoParamTopTwoTailFraction_eq
    (d x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    v12TwoParamTopTwoTailFraction d x hx0 hx1 hd0 hd1 =
      v12TwoParamTail d x / v12TwoParamGlobal d x := by
  unfold v12TwoParamTopTwoTailFraction
  rw [v12TwoParam_globalSq d x hx0 hx1 hd0 hd1]

end
end EverettianDecoherence.Approximation

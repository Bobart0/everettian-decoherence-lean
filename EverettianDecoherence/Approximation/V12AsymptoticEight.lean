import EverettianDecoherence.Approximation.MaxCutThresholdStability

/-!
**FR.** Passage asymptotique v12 vers la constante universelle 8. Pour un
seuil fixe eps dans (0,1), le lemme de cut donne une constante scalaire
explicite. Lorsque le budget global A et le défaut relatif eta tendent vers
zéro, cette constante tend vers 8(1+eps)/(1-eps). Un choix explicite de eps
pour tout c>8 donne donc éventuellement une queue absolue <= c eta,
uniformément en dimension et en cardinalité.

**EN.** v12 asymptotic passage to the universal constant 8. For a fixed
threshold eps in (0,1), the cut lemma yields an explicit scalar coefficient.
As the global budget A and relative defect eta tend to zero, this coefficient
converges to 8(1+eps)/(1-eps). An explicit choice of eps for every c>8
therefore gives an eventual absolute tail <= c eta, uniformly in dimension
and cardinality.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open Filter
open scoped BigOperators Classical Topology

noncomputable section

/-- Scalar coefficient obtained from the thresholded maximal-cut estimate
after dividing the absolute two-cell tail by the exact relative defect eta. -/
noncomputable def v12GeneralSharpCoefficient
    (eps A eta : ℝ) : ℝ :=
  A / eps +
    (4 * (1 + eps) / (1 - eps) +
      (1 + 1 / eps) * eta * A / (1 - eps) ^ 2) /
      ((1 - eta) / 2 - eta / eps)

theorem v12GeneralSharpCoefficient_tendsto
    {α : Type*} {l : Filter α}
    (eps : ℝ) (heps0 : 0 < eps) (heps1 : eps < 1)
    (A eta : α → ℝ)
    (hA : Tendsto A l (𝓝 0))
    (heta : Tendsto eta l (𝓝 0)) :
    Tendsto
      (fun k => v12GeneralSharpCoefficient eps (A k) (eta k))
      l (𝓝 (8 * (1 + eps) / (1 - eps))) := by
  have hepsne : eps ≠ 0 := ne_of_gt heps0
  have h1eps : 1 - eps ≠ 0 := ne_of_gt (sub_pos.mpr heps1)
  have hAeps :
      Tendsto (fun k => A k / eps) l (𝓝 0) := by
    simpa using hA.div_const eps
  have hetaA :
      Tendsto (fun k => eta k * A k) l (𝓝 0) := by
    simpa using heta.mul hA
  have hquad :
      Tendsto
        (fun k =>
          (1 + 1 / eps) * eta k * A k / (1 - eps) ^ 2)
        l (𝓝 0) := by
    have hmul :=
      (tendsto_const_nhds :
        Tendsto (fun _ : α => (1 + 1 / eps : ℝ)) l
          (𝓝 (1 + 1 / eps))).mul hetaA
    have hdiv := hmul.div_const ((1 - eps) ^ 2)
    simpa [mul_assoc] using hdiv
  have hnum :
      Tendsto
        (fun k =>
          4 * (1 + eps) / (1 - eps) +
            (1 + 1 / eps) * eta k * A k / (1 - eps) ^ 2)
        l (𝓝 (4 * (1 + eps) / (1 - eps))) := by
    simpa using
      (tendsto_const_nhds :
        Tendsto
          (fun _ : α => (4 * (1 + eps) / (1 - eps) : ℝ)) l
          (𝓝 (4 * (1 + eps) / (1 - eps)))).add hquad
  have hden :
      Tendsto
        (fun k => (1 - eta k) / 2 - eta k / eps)
        l (𝓝 (1 / 2 : ℝ)) := by
    have honeMinus :=
      (tendsto_const_nhds :
        Tendsto (fun _ : α => (1 : ℝ)) l (𝓝 1)).sub heta
    have hhalf := honeMinus.div_const 2
    have hetaeps := heta.div_const eps
    convert hhalf.sub hetaeps using 1 <;> norm_num
  have hratio :=
    hnum.div hden (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have hsum := hAeps.add hratio
  convert hsum using 1
  · funext k
    rfl
  · field_simp [h1eps]
    ring

/-- Finite exact-defect form behind the asymptotic coefficient. -/
theorem exists_two_cell_of_exact_maxCut_defect
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (eps eta : ℝ)
    (heps0 : 0 < eps) (heps1 : eps < 1)
    (hdelta : 0 < operatorNormProjectorCommutatorL2 D U)
    (heta0 : 0 < eta)
    (hexact :
      maxCutEnvelopeDefect D U =
        eta * operatorNormProjectorCommutatorL2 D U ^ 2)
    (hdenpos :
      0 < (1 - eta) / 2 - eta / eps) :
    ∃ i j : (Projective.interface n).Cell D,
      i ≠ j ∧
      operatorNormProjectorCommutatorL2 D U ^ 2 -
          cellCommutatorOpNormSq D U i -
          cellCommutatorOpNormSq D U j ≤
        eta * v12GeneralSharpCoefficient eps
          (operatorNormProjectorCommutatorL2 D U ^ 2) eta := by
  let A : ℝ := operatorNormProjectorCommutatorL2 D U ^ 2
  let g : ℝ := maxSubsetCommutatorOpNorm D U ^ 2
  have hApos : 0 < A := by
    dsimp [A]
    exact sq_pos_of_pos hdelta
  have hgEq : g = A * (1 - eta) / 2 := by
    have hdef :
        A - 2 * g = eta * A := by
      simpa [A, g, maxCutEnvelopeDefect] using hexact
    linarith
  have honeeta : 0 < 1 - eta := by
    have hpos :
        0 < (1 - eta) / 2 := by
      have hetaeps : 0 < eta / eps := div_pos heta0 heps0
      linarith
    linarith
  have hgposSq : 0 < g := by
    rw [hgEq]
    positivity
  have hGnonneg : 0 ≤ maxSubsetCommutatorOpNorm D U :=
    maxSubsetCommutatorOpNorm_nonneg D U
  have hGpos : 0 < maxSubsetCommutatorOpNorm D U := by
    have hsquare :
        0 < maxSubsetCommutatorOpNorm D U ^ 2 := by
      simpa [g] using hgposSq
    nlinarith
  have hLpos :
      0 <
        maxSubsetCommutatorOpNorm D U ^ 2 -
          maxCutEnvelopeDefect D U / eps := by
    have hcalc :
        maxSubsetCommutatorOpNorm D U ^ 2 -
            maxCutEnvelopeDefect D U / eps =
          A * ((1 - eta) / 2 - eta / eps) := by
      rw [hexact]
      rw [show maxSubsetCommutatorOpNorm D U ^ 2 = g by rfl, hgEq]
      field_simp [ne_of_gt heps0]
      ring
    rw [hcalc]
    positivity
  obtain ⟨i, j, hij, htail⟩ :=
    exists_two_cell_concentration_of_maxCut_threshold
      D U eps eps heps0 heps1 heps0 hGpos hLpos
  refine ⟨i, j, hij, ?_⟩
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hepsne : eps ≠ 0 := ne_of_gt heps0
  have h1eps : 1 - eps ≠ 0 := ne_of_gt (sub_pos.mpr heps1)
  have hdenne :
      (1 - eta) / 2 - eta / eps ≠ 0 :=
    ne_of_gt hdenpos
  have hLidentity :
      maxSubsetCommutatorOpNorm D U ^ 2 -
          maxCutEnvelopeDefect D U / eps =
        A * ((1 - eta) / 2 - eta / eps) := by
    rw [hexact]
    rw [show maxSubsetCommutatorOpNorm D U ^ 2 = g by rfl, hgEq]
    field_simp [hepsne]
    ring
  rw [hLidentity] at htail
  rw [hexact] at htail
  change
    A - cellCommutatorOpNormSq D U i -
          cellCommutatorOpNormSq D U j ≤
      eta * v12GeneralSharpCoefficient eps A eta
  have hidentity :
      eta * A / eps +
          (4 * (1 + eps) * (eta * A / (1 - eps)) +
            (1 + 1 / eps) * (eta * A / (1 - eps)) ^ 2) /
            (A * ((1 - eta) / 2 - eta / eps)) =
        eta * v12GeneralSharpCoefficient eps A eta := by
    unfold v12GeneralSharpCoefficient
    field_simp [hAne, hepsne, h1eps, hdenne] <;> ring
  rw [← hidentity]
  simpa [A] using htail

/-- For every c>8, choose a fixed threshold whose limiting coefficient is
strictly below c. -/
theorem exists_threshold_limit_lt_of_eight_lt
    {c : ℝ} (hc : 8 < c) :
    ∃ eps : ℝ, 0 < eps ∧ eps < 1 ∧
      8 * (1 + eps) / (1 - eps) < c := by
  let eps : ℝ := (c - 8) / (2 * (c + 8))
  have hc8 : 0 < c + 8 := by linarith
  have heps0 : 0 < eps := by
    dsimp [eps]
    positivity
  have heps1 : eps < 1 := by
    dsimp [eps]
    apply (div_lt_one (by positivity)).2
    linarith
  refine ⟨eps, heps0, heps1, ?_⟩
  have hc24 : 0 < c + 24 := by linarith
  have hc24' : (24 + c : ℝ) ≠ 0 := by linarith
  have hc8' : (8 + c : ℝ) ≠ 0 := by linarith
  have heq :
      8 * (1 + eps) / (1 - eps) =
        8 * (3 * c + 8) / (c + 24) := by
    dsimp [eps]
    field_simp [ne_of_gt hc8, ne_of_gt hc24, hc24', hc8'] <;> ring
  rw [heq]
  apply (div_lt_iff₀ hc24).2
  have hprod : 0 < (c - 8) * (c + 8) :=
    mul_pos (sub_pos.mpr hc) hc8
  nlinarith

/-- General sharp coefficient 8, in an eventual form robust under varying
finite dimensions and varying cell cardinalities. -/
theorem eventually_two_cell_tail_le_of_small_defect
    (dim : ℕ → ℕ)
    (D : (k : ℕ) → Perspective (dim k))
    (U : (k : ℕ) → H (dim k) ≃ₗᵢ[ℂ] H (dim k))
    (eta : ℕ → ℝ)
    (hdelta : ∀ k, 0 < operatorNormProjectorCommutatorL2 (D k) (U k))
    (hetaPos : ∀ k, 0 < eta k)
    (hexact : ∀ k,
      maxCutEnvelopeDefect (D k) (U k) =
        eta k * operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2)
    (hA :
      Tendsto
        (fun k =>
          operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2)
        atTop (𝓝 0))
    (heta : Tendsto eta atTop (𝓝 0))
    (c : ℝ) (hc : 8 < c) :
    ∀ᶠ k in atTop,
      ∃ i j : (Projective.interface (dim k)).Cell (D k),
        i ≠ j ∧
        operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2 -
            cellCommutatorOpNormSq (D k) (U k) i -
            cellCommutatorOpNormSq (D k) (U k) j ≤
          c * eta k := by
  obtain ⟨eps, heps0, heps1, hlimc⟩ :=
    exists_threshold_limit_lt_of_eight_lt hc
  let A : ℕ → ℝ := fun k =>
    operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2
  let coeff : ℕ → ℝ := fun k =>
    v12GeneralSharpCoefficient eps (A k) (eta k)
  let den : ℕ → ℝ := fun k =>
    (1 - eta k) / 2 - eta k / eps
  have hcoeff :
      Tendsto coeff atTop
        (𝓝 (8 * (1 + eps) / (1 - eps))) := by
    exact v12GeneralSharpCoefficient_tendsto
      eps heps0 heps1 A eta (by simpa [A] using hA) heta
  have hden :
      Tendsto den atTop (𝓝 (1 / 2 : ℝ)) := by
    have honeMinus :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub heta
    have hhalf := honeMinus.div_const 2
    have hetaeps := heta.div_const eps
    simpa [den] using hhalf.sub hetaeps
  have hcoefflt : ∀ᶠ k in atTop, coeff k < c :=
    hcoeff.eventually (Iio_mem_nhds hlimc)
  have hdenpos : ∀ᶠ k in atTop, 0 < den k :=
    hden.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hcoefflt, hdenpos] with k hkcoeff hkden
  obtain ⟨i, j, hij, htail⟩ :=
    exists_two_cell_of_exact_maxCut_defect
      (D k) (U k) eps (eta k)
      heps0 heps1 (hdelta k) (hetaPos k) (hexact k)
      (by simpa [den] using hkden)
  refine ⟨i, j, hij, htail.trans ?_⟩
  have heta0 : 0 ≤ eta k := (hetaPos k).le
  have hmul :=
    mul_le_mul_of_nonneg_left hkcoeff.le heta0
  simpa [coeff, A, mul_comm] using hmul

end
end EverettianDecoherence.Approximation

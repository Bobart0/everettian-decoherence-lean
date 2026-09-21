import EverettianDecoherence.Approximation.MaxCutThresholdStabilitySharp

/-!
**FR.** Upper bound v12 dans le régime ultra-near. Lorsque le défaut relatif
eta tend vers zéro, le budget global A = delta^2 tend vers zéro et
eta/A tend vers zéro, le raffinement small-spread améliore la constante
universelle de 8 à 4. Le résultat est uniforme en dimension et en cardinalité.

**EN.** v12 upper bound in the ultra-near regime. When the relative defect eta
tends to zero, the global budget A = delta^2 tends to zero, and eta/A tends to
zero, the small-spread refinement improves the universal constant from 8 to 4.
The result is uniform in dimension and cardinality.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open Filter
open scoped BigOperators Classical Topology

noncomputable section

noncomputable def v12UltraNearNumerator
    (eps A eta : ℝ) : ℝ :=
  4 * (1 + eps) / (1 - eps) +
    (1 + 1 / eps) * eta * A / (1 - eps) ^ 2

noncomputable def v12UltraNearBaseDen
    (eps eta : ℝ) : ℝ :=
  (1 - eta) / 2 - eta / eps

noncomputable def v12UltraNearSharpDen
    (eps A eta : ℝ) : ℝ :=
  v12UltraNearBaseDen eps eta -
    (eta / A) * v12UltraNearNumerator eps A eta /
      v12UltraNearBaseDen eps eta

noncomputable def v12UltraNearSharpCoefficient
    (eps A eta : ℝ) : ℝ :=
  A / eps +
    v12UltraNearNumerator eps A eta /
      (2 * v12UltraNearSharpDen eps A eta)

theorem v12UltraNearNumerator_tendsto
    {α : Type*} {l : Filter α}
    (eps : ℝ) (heps0 : 0 < eps) (heps1 : eps < 1)
    (A eta : α → ℝ)
    (hA : Tendsto A l (𝓝 0))
    (heta : Tendsto eta l (𝓝 0)) :
    Tendsto
      (fun k => v12UltraNearNumerator eps (A k) (eta k))
      l (𝓝 (4 * (1 + eps) / (1 - eps))) := by
  have hetaA : Tendsto (fun k => eta k * A k) l (𝓝 0) := by
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
    simpa [mul_assoc] using hmul.div_const ((1 - eps) ^ 2)
  unfold v12UltraNearNumerator
  simpa using
    (tendsto_const_nhds :
      Tendsto
        (fun _ : α => (4 * (1 + eps) / (1 - eps) : ℝ))
        l (𝓝 (4 * (1 + eps) / (1 - eps)))).add hquad

theorem v12UltraNearBaseDen_tendsto
    {α : Type*} {l : Filter α}
    (eps : ℝ)
    (eta : α → ℝ)
    (heta : Tendsto eta l (𝓝 0)) :
    Tendsto
      (fun k => v12UltraNearBaseDen eps (eta k))
      l (𝓝 (1 / 2 : ℝ)) := by
  have honeMinus :=
    (tendsto_const_nhds :
      Tendsto (fun _ : α => (1 : ℝ)) l (𝓝 1)).sub heta
  have hhalf := honeMinus.div_const 2
  have hetaeps := heta.div_const eps
  simpa [v12UltraNearBaseDen] using hhalf.sub hetaeps

theorem v12UltraNearSharpDen_tendsto
    {α : Type*} {l : Filter α}
    (eps : ℝ) (heps0 : 0 < eps) (heps1 : eps < 1)
    (A eta : α → ℝ)
    (hA : Tendsto A l (𝓝 0))
    (heta : Tendsto eta l (𝓝 0))
    (hratio : Tendsto (fun k => eta k / A k) l (𝓝 0)) :
    Tendsto
      (fun k => v12UltraNearSharpDen eps (A k) (eta k))
      l (𝓝 (1 / 2 : ℝ)) := by
  have hnum :=
    v12UltraNearNumerator_tendsto eps heps0 heps1 A eta hA heta
  have hbase := v12UltraNearBaseDen_tendsto eps eta heta
  have hprod :
      Tendsto
        (fun k =>
          (eta k / A k) *
            v12UltraNearNumerator eps (A k) (eta k))
        l (𝓝 0) := by
    simpa using hratio.mul hnum
  have hfrac :
      Tendsto
        (fun k =>
          ((eta k / A k) *
            v12UltraNearNumerator eps (A k) (eta k)) /
              v12UltraNearBaseDen eps (eta k))
        l (𝓝 0) := by
    have hraw :=
      hprod.div hbase (by norm_num : (1 / 2 : ℝ) ≠ 0)
    change
      Tendsto
        (fun k =>
          ((eta k / A k) *
            v12UltraNearNumerator eps (A k) (eta k)) /
              v12UltraNearBaseDen eps (eta k))
        l (𝓝 (0 / (1 / 2 : ℝ))) at hraw
    norm_num at hraw
    exact hraw
  unfold v12UltraNearSharpDen
  simpa using hbase.sub hfrac

theorem v12UltraNearSharpCoefficient_tendsto
    {α : Type*} {l : Filter α}
    (eps : ℝ) (heps0 : 0 < eps) (heps1 : eps < 1)
    (A eta : α → ℝ)
    (hA : Tendsto A l (𝓝 0))
    (heta : Tendsto eta l (𝓝 0))
    (hratio : Tendsto (fun k => eta k / A k) l (𝓝 0)) :
    Tendsto
      (fun k => v12UltraNearSharpCoefficient eps (A k) (eta k))
      l (𝓝 (4 * (1 + eps) / (1 - eps))) := by
  have hAeps :
      Tendsto (fun k => A k / eps) l (𝓝 0) := by
    simpa using hA.div_const eps
  have hnum :=
    v12UltraNearNumerator_tendsto eps heps0 heps1 A eta hA heta
  have hden :=
    v12UltraNearSharpDen_tendsto
      eps heps0 heps1 A eta hA heta hratio
  have htwoDen :
      Tendsto
        (fun k => 2 * v12UltraNearSharpDen eps (A k) (eta k))
        l (𝓝 1) := by
    have htwo :=
      (tendsto_const_nhds :
        Tendsto (fun _ : α => (2 : ℝ)) l (𝓝 2)).mul hden
    convert htwo using 1 <;> norm_num
  have hquot :=
    hnum.div htwoDen (by norm_num : (1 : ℝ) ≠ 0)
  unfold v12UltraNearSharpCoefficient
  simpa using hAeps.add hquot

theorem exists_two_cell_of_exact_maxCut_defect_sharp
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (eps eta : ℝ)
    (heps0 : 0 < eps) (heps1 : eps < 1)
    (hdelta : 0 < operatorNormProjectorCommutatorL2 D U)
    (heta0 : 0 < eta)
    (hexact :
      maxCutEnvelopeDefect D U =
        eta * operatorNormProjectorCommutatorL2 D U ^ 2)
    (hbaseDen :
      0 < v12UltraNearBaseDen eps eta)
    (hsharpDen :
      0 < v12UltraNearSharpDen eps
        (operatorNormProjectorCommutatorL2 D U ^ 2) eta) :
    ∃ i j : (Projective.interface n).Cell D,
      i ≠ j ∧
      operatorNormProjectorCommutatorL2 D U ^ 2 -
          cellCommutatorOpNormSq D U i -
          cellCommutatorOpNormSq D U j ≤
        eta * v12UltraNearSharpCoefficient eps
          (operatorNormProjectorCommutatorL2 D U ^ 2) eta := by
  let A : ℝ := operatorNormProjectorCommutatorL2 D U ^ 2
  let g : ℝ := maxSubsetCommutatorOpNorm D U ^ 2
  let d : ℝ := v12UltraNearBaseDen eps eta
  let N : ℝ := v12UltraNearNumerator eps A eta
  let s : ℝ := v12UltraNearSharpDen eps A eta
  have hApos : 0 < A := by
    dsimp [A]
    exact sq_pos_of_pos hdelta
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hepsne : eps ≠ 0 := ne_of_gt heps0
  have h1eps : 1 - eps ≠ 0 := ne_of_gt (sub_pos.mpr heps1)
  have hdpos : 0 < d := by simpa [d] using hbaseDen
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hspos : 0 < s := by simpa [s, A] using hsharpDen
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hgEq : g = A * (1 - eta) / 2 := by
    have hdef :
        A - 2 * g = eta * A := by
      simpa [A, g, maxCutEnvelopeDefect] using hexact
    linarith
  have honeeta : 0 < 1 - eta := by
    have hpos : 0 < (1 - eta) / 2 := by
      have hetaeps : 0 < eta / eps := div_pos heta0 heps0
      have : 0 < d := hdpos
      dsimp [d, v12UltraNearBaseDen] at this
      linarith
    linarith
  have hgposSq : 0 < g := by
    rw [hgEq]
    positivity
  have hGpos : 0 < maxSubsetCommutatorOpNorm D U := by
    have hG0 := maxSubsetCommutatorOpNorm_nonneg D U
    have hsquare :
        0 < maxSubsetCommutatorOpNorm D U ^ 2 := by
      simpa [g] using hgposSq
    nlinarith
  have hLidentity :
      maxSubsetCommutatorOpNorm D U ^ 2 -
          maxCutEnvelopeDefect D U / eps =
        A * d := by
    rw [hexact]
    rw [show maxSubsetCommutatorOpNorm D U ^ 2 = g by rfl, hgEq]
    dsimp [d, v12UltraNearBaseDen]
    field_simp [hepsne]
    ring
  have hLpos :
      0 <
        maxSubsetCommutatorOpNorm D U ^ 2 -
          maxCutEnvelopeDefect D U / eps := by
    rw [hLidentity]
    positivity
  have hKidentity :
      4 * (1 + eps) *
          (maxCutEnvelopeDefect D U / (1 - eps)) +
        (1 + 1 / eps) *
          (maxCutEnvelopeDefect D U / (1 - eps)) ^ 2 =
        eta * A * N := by
    rw [hexact]
    dsimp [N, v12UltraNearNumerator]
    field_simp [hepsne, h1eps]
    ring
  have hsharpExpanded :
      0 < d - (eta / A) * N / d := by
    simpa [s, v12UltraNearSharpDen, d, N] using hspos
  have hratioLt :
      (eta / A) * N < d ^ 2 := by
    have hlt : (eta / A) * N / d < d := by linarith
    calc
      (eta / A) * N =
          ((eta / A) * N / d) * d := by
            field_simp [hdne]
      _ < d * d := mul_lt_mul_of_pos_right hlt hdpos
      _ = d ^ 2 := by ring
  have hA2pos : 0 < A ^ 2 := sq_pos_of_pos hApos
  have hscaled :=
    mul_lt_mul_of_pos_left hratioLt hA2pos
  have hscaled' :
      eta * A * N < (A * d) ^ 2 := by
    calc
      eta * A * N =
          A ^ 2 * ((eta / A) * N) := by
            field_simp [hAne]
      _ < A ^ 2 * d ^ 2 := hscaled
      _ = (A * d) ^ 2 := by ring
  have hKlt :
      4 * (1 + eps) *
          (maxCutEnvelopeDefect D U / (1 - eps)) +
        (1 + 1 / eps) *
          (maxCutEnvelopeDefect D U / (1 - eps)) ^ 2 <
        (maxSubsetCommutatorOpNorm D U ^ 2 -
          maxCutEnvelopeDefect D U / eps) ^ 2 := by
    rw [hKidentity, hLidentity]
    exact hscaled'
  obtain ⟨i, j, hij, htail⟩ :=
    exists_two_cell_concentration_of_maxCut_threshold_sharp
      D U eps eps heps0 heps1 heps0 hGpos hLpos hKlt
  refine ⟨i, j, hij, ?_⟩
  rw [hLidentity, hKidentity] at htail
  rw [hexact] at htail
  change
    A - cellCommutatorOpNormSq D U i -
          cellCommutatorOpNormSq D U j ≤
      eta * v12UltraNearSharpCoefficient eps A eta
  have hdenIdentity :
      2 * ((A * d) - (eta * A * N) / (A * d)) =
        2 * A * s := by
    dsimp [s, v12UltraNearSharpDen]
    field_simp [hAne, hdne]
    ring
  have hidentity :
      eta * A / eps +
          (eta * A * N) /
            (2 * ((A * d) - (eta * A * N) / (A * d))) =
        eta * v12UltraNearSharpCoefficient eps A eta := by
    unfold v12UltraNearSharpCoefficient
    rw [hdenIdentity]
    field_simp [hAne, hepsne, hsne]
    ring
  rw [← hidentity]
  simpa [A, d, N] using htail

theorem exists_threshold_limit_lt_of_four_lt
    {c : ℝ} (hc : 4 < c) :
    ∃ eps : ℝ, 0 < eps ∧ eps < 1 ∧
      4 * (1 + eps) / (1 - eps) < c := by
  let eps : ℝ := (c - 4) / (2 * (c + 4))
  have hc4 : 0 < c + 4 := by linarith
  have heps0 : 0 < eps := by
    dsimp [eps]
    positivity
  have heps1 : eps < 1 := by
    dsimp [eps]
    apply (div_lt_one (by positivity)).2
    linarith
  refine ⟨eps, heps0, heps1, ?_⟩
  have hc12 : 0 < c + 12 := by linarith
  have heq :
      4 * (1 + eps) / (1 - eps) =
        4 * (3 * c + 4) / (c + 12) := by
    dsimp [eps]
    field_simp [ne_of_gt hc4, ne_of_gt hc12]
    ring
  rw [heq]
  apply (div_lt_iff₀ hc12).2
  have hprod : 0 < (c - 4) * (c + 4) :=
    mul_pos (sub_pos.mpr hc) hc4
  nlinarith

/-- Ultra-near upper coefficient 4, uniform under varying finite dimensions
and varying cell cardinalities. -/
theorem eventually_two_cell_tail_le_of_ultra_near
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
    (hultra :
      Tendsto
        (fun k =>
          eta k /
            operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2)
        atTop (𝓝 0))
    (c : ℝ) (hc : 4 < c) :
    ∀ᶠ k in atTop,
      ∃ i j : (Projective.interface (dim k)).Cell (D k),
        i ≠ j ∧
        operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2 -
            cellCommutatorOpNormSq (D k) (U k) i -
            cellCommutatorOpNormSq (D k) (U k) j ≤
          c * eta k := by
  obtain ⟨eps, heps0, heps1, hlimc⟩ :=
    exists_threshold_limit_lt_of_four_lt hc
  let A : ℕ → ℝ := fun k =>
    operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2
  let coeff : ℕ → ℝ := fun k =>
    v12UltraNearSharpCoefficient eps (A k) (eta k)
  let baseDen : ℕ → ℝ := fun k =>
    v12UltraNearBaseDen eps (eta k)
  let sharpDen : ℕ → ℝ := fun k =>
    v12UltraNearSharpDen eps (A k) (eta k)
  have hcoeff :
      Tendsto coeff atTop
        (𝓝 (4 * (1 + eps) / (1 - eps))) := by
    exact v12UltraNearSharpCoefficient_tendsto
      eps heps0 heps1 A eta
      (by simpa [A] using hA) heta (by simpa [A] using hultra)
  have hbase :
      Tendsto baseDen atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa [baseDen] using
      v12UltraNearBaseDen_tendsto eps eta heta
  have hsharp :
      Tendsto sharpDen atTop (𝓝 (1 / 2 : ℝ)) := by
    exact v12UltraNearSharpDen_tendsto
      eps heps0 heps1 A eta
      (by simpa [A] using hA) heta (by simpa [A] using hultra)
  have hcoefflt : ∀ᶠ k in atTop, coeff k < c :=
    hcoeff.eventually (Iio_mem_nhds hlimc)
  have hbasepos : ∀ᶠ k in atTop, 0 < baseDen k :=
    hbase.eventually
      (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hsharppos : ∀ᶠ k in atTop, 0 < sharpDen k :=
    hsharp.eventually
      (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hcoefflt, hbasepos, hsharppos] with
      k hkcoeff hkbase hksharp
  obtain ⟨i, j, hij, htail⟩ :=
    exists_two_cell_of_exact_maxCut_defect_sharp
      (D k) (U k) eps (eta k)
      heps0 heps1 (hdelta k) (hetaPos k) (hexact k)
      (by simpa [baseDen] using hkbase)
      (by simpa [sharpDen, A] using hksharp)
  refine ⟨i, j, hij, htail.trans ?_⟩
  have heta0 : 0 ≤ eta k := (hetaPos k).le
  have hmul :=
    mul_le_mul_of_nonneg_left hkcoeff.le heta0
  simpa [coeff, A, mul_comm] using hmul

end
end EverettianDecoherence.Approximation

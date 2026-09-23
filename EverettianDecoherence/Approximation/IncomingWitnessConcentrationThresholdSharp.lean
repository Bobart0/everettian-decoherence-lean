import EverettianDecoherence.Approximation.IncomingWitnessNormalizedThreshold
import EverettianDecoherence.Metrics.FiniteConcentrationSharp

/-!
**FR.** Version sharp du lemme de concentration au seuil variable. La
conversion du spread de Gram utilise un plafond commun Kbar dans le
dénominateur, ce qui préserve le facteur deux lors de l'agrégation bilatérale.

**EN.** Sharp variable-threshold concentration. The Gram-spread conversion
uses a common cap Kbar in the denominator, preserving the factor two under
bilateral aggregation.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical InnerProductSpace

noncomputable section

theorem exists_dominant_activeGoodAt_incomingWitness_sharp
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (hv : ‖v‖ = 1)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v)
    (β t L Kbar : ℝ)
    (hβ0 : 0 < β) (hβone : β < 1)
    (ht : 0 < t)
    (hL :
      L ≤ ∑ c ∈ incomingWitnessActiveGoodCellsAt D U S v β,
        incomingWitnessP D U c)
    (hLpos : 0 < L)
    (hKbar0 : 0 ≤ Kbar)
    (hKbarlt : Kbar < L ^ 2)
    (hKcap :
      4 * (1 + t) *
          ((∑ c ∈ S, incomingWitnessAlpha D U c v) / (1 - β)) +
        (1 + 1 / t) *
          ((∑ c ∈ S, incomingWitnessAlpha D U c v) / (1 - β)) ^ 2 ≤
        Kbar) :
    ∃ i : ↥(incomingWitnessActiveGoodCellsAt D U S v β),
      (∑ j ∈ Finset.univ.erase i, incomingWitnessP D U j.1) ≤
        (4 * (1 + t) *
            ((∑ c ∈ S, incomingWitnessAlpha D U c v) / (1 - β)) +
          (1 + 1 / t) *
            ((∑ c ∈ S, incomingWitnessAlpha D U c v) / (1 - β)) ^ 2) /
          (2 * (L - Kbar / L)) := by
  let e : ℝ := ∑ c ∈ S, incomingWitnessAlpha D U c v
  let qB : ℝ := e / (1 - β)
  let K : ℝ := 4 * (1 + t) * qB + (1 + 1 / t) * qB ^ 2
  have he0 : 0 ≤ e := by
    dsimp [e]
    exact Finset.sum_nonneg fun c hc =>
      incomingWitnessAlpha_nonneg_of_mem D U S c hc v hv hvcompl
  have hden : 0 < 1 - β := sub_pos.mpr hβone
  have hqB0 : 0 ≤ qB := by
    dsimp [qB]
    positivity
  have hK0 : 0 ≤ K := by
    dsimp [K]
    have hcoef1 : 0 ≤ 4 * (1 + t) := by positivity
    have hcoef2 : 0 ≤ 1 + 1 / t := by
      have : 0 < 1 / t := one_div_pos.mpr ht
      linarith
    positivity
  have hmasspos :
      0 < ∑ c ∈ incomingWitnessActiveGoodCellsAt D U S v β,
        incomingWitnessP D U c :=
    lt_of_lt_of_le hLpos hL
  have hactive :
      (incomingWitnessActiveGoodCellsAt D U S v β).Nonempty := by
    by_contra hne
    have hempty : incomingWitnessActiveGoodCellsAt D U S v β = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty] at hmasspos
    simp at hmasspos
  letI : Nonempty ↥(incomingWitnessActiveGoodCellsAt D U S v β) :=
    Finset.nonempty_coe_sort.mpr hactive
  have hp :
      ∀ i : ↥(incomingWitnessActiveGoodCellsAt D U S v β),
        0 ≤ incomingWitnessP D U i.1 :=
    fun i => incomingWitnessP_nonneg D U i.1
  let q : ℝ :=
    ∑ i : ↥(incomingWitnessActiveGoodCellsAt D U S v β),
      ‖incomingWitnessZetaAt D U S v β i -
        incomingWitnessXiAt D U S v β i‖ ^ 2
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hq : q ≤ qB := by
    dsimp [q, qB, e]
    exact sum_incomingWitnessXiAt_sub_ZetaAt_norm_sq_le
      D U S v hv hvcompl β hβ0 hβone
  have hq_sq : q ^ 2 ≤ qB ^ 2 :=
    (sq_le_sq₀ hq0 hqB0).2 hq
  have hgram :=
    gram_offDiagonal_spread_le_param
      (incomingWitnessXiAt D U S v β)
      (incomingWitnessZetaAt D U S v β)
      (fun i : ↥(incomingWitnessActiveGoodCellsAt D U S v β) =>
        incomingWitnessP D U i.1)
      t ht
      (incomingWitnessXiAt_orthonormal D U S v β hβone)
      hp
      (fun i j hij =>
        incomingWitnessZetaAt_gram
          D U S v hv hvcompl β i j hij)
  have hcoef1 : 0 ≤ 4 * (1 + t) := by positivity
  have hcoef2 : 0 ≤ 1 + 1 / t := by
    have : 0 < 1 / t := one_div_pos.mpr ht
    linarith
  have hspread :
      (∑ i : ↥(incomingWitnessActiveGoodCellsAt D U S v β),
        ∑ j ∈ Finset.univ.erase i,
          incomingWitnessP D U i.1 * incomingWitnessP D U j.1) ≤ K := by
    have hbound :
        4 * (1 + t) * q + (1 + 1 / t) * q ^ 2 ≤ K := by
      dsimp [K]
      exact add_le_add
        (mul_le_mul_of_nonneg_left hq hcoef1)
        (mul_le_mul_of_nonneg_left hq_sq hcoef2)
    exact hgram.trans (by simpa [q] using hbound)
  have hspread' :
      (∑ i, (fun k : ↥(incomingWitnessActiveGoodCellsAt D U S v β) =>
          incomingWitnessP D U k.1) i) ^ 2 -
        (∑ i, (fun k : ↥(incomingWitnessActiveGoodCellsAt D U S v β) =>
          incomingWitnessP D U k.1) i ^ 2) ≤ K := by
    rw [← sum_offDiagonal_mul_eq_sum_sq_sub_sum_sq
      (fun k : ↥(incomingWitnessActiveGoodCellsAt D U S v β) =>
        incomingWitnessP D U k.1)]
    exact hspread
  have hmass :
      L ≤ ∑ i : ↥(incomingWitnessActiveGoodCellsAt D U S v β),
        incomingWitnessP D U i.1 := by
    calc
      L ≤ ∑ c ∈ incomingWitnessActiveGoodCellsAt D U S v β,
          incomingWitnessP D U c := hL
      _ = ∑ i : ↥(incomingWitnessActiveGoodCellsAt D U S v β),
          incomingWitnessP D U i.1 := by
        exact
          (Finset.sum_coe_sort
            (incomingWitnessActiveGoodCellsAt D U S v β)
            (fun c => incomingWitnessP D U c)).symm
  have hKcap' : K ≤ Kbar := by
    simpa [K, qB, e] using hKcap
  obtain ⟨i, _hi, htail⟩ :=
    exists_tail_le_of_spread_le_sharp_with_cap
      (Finset.univ :
        Finset ↥(incomingWitnessActiveGoodCellsAt D U S v β))
      (fun k => incomingWitnessP D U k.1)
      K Kbar L Finset.univ_nonempty
      (by intro j _; exact hp j)
      (by simpa using hspread')
      (by simpa using hmass)
      hLpos hK0 hKbar0 hKcap' hKbarlt
  refine ⟨i, ?_⟩
  simpa [K, qB, e] using htail

end
end EverettianDecoherence.Approximation

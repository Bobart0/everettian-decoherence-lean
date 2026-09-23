import EverettianDecoherence.Approximation.IncomingWitnessConcentration
import EverettianDecoherence.Approximation.IncomingWitnessNormalizedSharp

/-!
**FR.** Version v12 de la concentration d'un témoin entrant. Le raffinement
de l'erreur normalisée et de la stabilité de Gram remplace la constante 18
par 9 dans la queue de la cellule dominante.

**EN.** v12 incoming-witness concentration. The refined normalized error and
Gram stability replace the dominant-cell tail constant 18 by 9.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical InnerProductSpace

noncomputable section

theorem exists_dominant_activeGood_incomingWitness_9
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (hv : ‖v‖ = 1)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v)
    (L : ℝ)
    (hehalf :
      (∑ c ∈ S, incomingWitnessAlpha D U c v) ≤ 1 / 2)
    (hL :
      L ≤ ∑ c ∈ incomingWitnessActiveGoodCells D U S v,
        incomingWitnessP D U c)
    (hLpos : 0 < L) :
    ∃ i : ↥(incomingWitnessActiveGoodCells D U S v),
      (∑ j ∈ Finset.univ.erase i, incomingWitnessP D U j.1) ≤
        (9 * (∑ c ∈ S, incomingWitnessAlpha D U c v)) / L := by
  let e : ℝ := ∑ c ∈ S, incomingWitnessAlpha D U c v
  have he0 : 0 ≤ e := by
    dsimp [e]
    exact Finset.sum_nonneg fun c hc =>
      incomingWitnessAlpha_nonneg_of_mem D U S c hc v hv hvcompl
  have hmasspos :
      0 < ∑ c ∈ incomingWitnessActiveGoodCells D U S v,
        incomingWitnessP D U c :=
    lt_of_lt_of_le hLpos hL
  have hactive :
      (incomingWitnessActiveGoodCells D U S v).Nonempty := by
    by_contra hne
    have hempty : incomingWitnessActiveGoodCells D U S v = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty] at hmasspos
    simp at hmasspos
  letI : Nonempty ↥(incomingWitnessActiveGoodCells D U S v) :=
    Finset.nonempty_coe_sort.mpr hactive
  have hp :
      ∀ i : ↥(incomingWitnessActiveGoodCells D U S v),
        0 ≤ incomingWitnessP D U i.1 :=
    fun i => incomingWitnessP_nonneg D U i.1
  have hclose :
      (∑ i : ↥(incomingWitnessActiveGoodCells D U S v),
        ‖incomingWitnessZeta D U S v i -
          incomingWitnessXi D U S v i‖ ^ 2) ≤
        (47 / 40 : ℝ) * e := by
    have h0 :=
      sum_incomingWitnessXi_sub_Zeta_norm_sq_le_47_40
        D U S v hv hvcompl
    simpa [e, norm_sub_rev] using h0
  have hmass :
      L ≤ ∑ i : ↥(incomingWitnessActiveGoodCells D U S v),
        incomingWitnessP D U i.1 := by
    calc
      L ≤ ∑ c ∈ incomingWitnessActiveGoodCells D U S v,
          incomingWitnessP D U c := hL
      _ = ∑ i : ↥(incomingWitnessActiveGoodCells D U S v),
          incomingWitnessP D U i.1 := by
        exact
          (Finset.sum_coe_sort
            (incomingWitnessActiveGoodCells D U S v)
            (fun c => incomingWitnessP D U c)).symm
  have hdom :=
    exists_dominant_of_gram_close_9
      (incomingWitnessXi D U S v)
      (incomingWitnessZeta D U S v)
      (fun i : ↥(incomingWitnessActiveGoodCells D U S v) =>
        incomingWitnessP D U i.1)
      e L
      (incomingWitnessXi_orthonormal D U S v)
      hp
      (fun i j hij =>
        incomingWitnessZeta_gram D U S v hv hvcompl i j hij)
      he0
      (by simpa [e] using hehalf)
      hclose
      hmass
      hLpos
  simpa [e] using hdom

end
end EverettianDecoherence.Approximation

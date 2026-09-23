import EverettianDecoherence.Approximation.IncomingWitnessNormalized

/-!
**FR.** Théorème inverse unilatéral sur un témoin entrant. La masse des
cellules bonnes et actives est inchangée par l'élimination des cellules de
budget nul. La stabilité de Gram donne alors une cellule dominante avec queue
au plus 18 e / L, où e est le déficit total du témoin et L une borne
inférieure positive sur la masse bonne-active.

**EN.** One-sided inverse theorem for an incoming witness. Removing zero-budget
cells does not change the good-cell mass. Gram stability then yields a
dominant cell whose tail is at most 18 e / L, where e is the total witness
deficit and L is a positive lower bound on the active-good mass.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical InnerProductSpace

noncomputable section

theorem sum_activeGood_incomingWitnessP_eq_good
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) :
    (∑ c ∈ incomingWitnessActiveGoodCells D U S v,
        incomingWitnessP D U c) =
      ∑ c ∈ incomingWitnessGoodCells D U S v,
        incomingWitnessP D U c := by
  apply Finset.sum_subset
  · exact Finset.filter_subset _ _
  · intro c hcGood hcNotActive
    have hnotpos : ¬ 0 < incomingWitnessP D U c := by
      intro hp
      apply hcNotActive
      exact Finset.mem_filter.mpr ⟨hcGood, hp⟩
    have hp0 := incomingWitnessP_nonneg D U c
    have hple : incomingWitnessP D U c ≤ 0 := le_of_not_gt hnotpos
    exact le_antisymm hple hp0

theorem activeGood_incomingWitnessP_mass_lower
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (hv : ‖v‖ = 1)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v) :
    subsetProjectorCommutatorOpNormSq D U S -
        2 * (∑ c ∈ S, incomingWitnessAlpha D U c v) ≤
      ∑ c ∈ incomingWitnessActiveGoodCells D U S v,
        incomingWitnessP D U c := by
  rw [sum_activeGood_incomingWitnessP_eq_good D U S v]
  exact good_incomingWitnessP_mass_lower D U S v hv hvcompl

theorem exists_dominant_activeGood_incomingWitness
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
        (18 * (∑ c ∈ S, incomingWitnessAlpha D U c v)) / L := by
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
          incomingWitnessXi D U S v i‖ ^ 2) ≤ 2 * e := by
    have h0 :=
      sum_incomingWitnessXi_sub_Zeta_norm_sq_le
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
    exists_dominant_of_gram_close_18
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

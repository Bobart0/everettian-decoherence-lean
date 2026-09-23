import EverettianDecoherence.Approximation.IncomingWitnessConcentrationThreshold
import EverettianDecoherence.Approximation.IncomingBlockNormWitness

/-!
**FR.** Lemme de cut entrant à seuil variable. Si L>0 minore la masse
bonne-active, la queue totale est la somme de la masse mauvaise e/beta et de
la queue de Gram contrôlée par L.

**EN.** Variable-threshold incoming-cut lemma. If L>0 is a lower bound on the
active-good mass, the total tail is the sum of the bad mass e/beta and the
Gram-controlled good tail divided by L.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

theorem exists_cell_concentration_of_incoming_max_threshold
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (β t L : ℝ)
    (hβ0 : 0 < β) (hβone : β < 1) (ht : 0 < t)
    (hmax :
      ‖recordSubsetIncomingCLM D U S‖ =
        ‖recordSubsetProjectorCommutatorCLM D U S‖)
    (hcpos : 0 < ‖recordSubsetProjectorCommutatorCLM D U S‖)
    (hLpos : 0 < L)
    (hL :
      L ≤ subsetProjectorCommutatorOpNormSq D U S -
        (subsetProjectorCommutatorOpNormSq D U S -
          ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) / β) :
    ∃ c ∈ S,
      subsetProjectorCommutatorOpNormSq D U S -
          incomingWitnessP D U c ≤
        (subsetProjectorCommutatorOpNormSq D U S -
          ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) / β +
        (4 * (1 + t) *
            ((subsetProjectorCommutatorOpNormSq D U S -
              ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) /
              (1 - β)) +
          (1 + 1 / t) *
            ((subsetProjectorCommutatorOpNormSq D U S -
              ‖recordSubsetProjectorCommutatorCLM D U S‖ ^ 2) /
              (1 - β)) ^ 2) / L := by
  let C : ℝ := ‖recordSubsetProjectorCommutatorCLM D U S‖
  let A : ℝ := subsetProjectorCommutatorOpNormSq D U S
  let e : ℝ := A - C ^ 2
  have hinpos : 0 < ‖recordSubsetIncomingCLM D U S‖ := by
    rw [hmax]
    exact hcpos
  obtain ⟨v, hv, hvcompl, hvnorm⟩ :=
    exists_unit_complWitness_norm_incoming D U S hinpos
  have heq :
      (∑ c ∈ S, incomingWitnessAlpha D U c v) = e := by
    rw [sum_incomingWitnessAlpha_eq_budget_sub_incoming
      D U S v hvcompl]
    dsimp [e, A, C]
    rw [hvnorm, hmax]
  have hmass0 :=
    activeGoodAt_incomingWitnessP_mass_lower
      D U S v hv hvcompl β hβ0
  have hmass :
      L ≤ ∑ c ∈ incomingWitnessActiveGoodCellsAt D U S v β,
        incomingWitnessP D U c := by
    apply hL.trans
    simpa [e, A, C, heq] using hmass0
  obtain ⟨i, hitail⟩ :=
    exists_dominant_activeGoodAt_incomingWitness
      D U S v hv hvcompl β t L
      hβ0 hβone ht hmass hLpos
  have hiActive : i.1 ∈ incomingWitnessActiveGoodCellsAt D U S v β := i.2
  have hiS :
      i.1 ∈ S :=
    ((mem_incomingWitnessActiveGoodCellsAt D U S v β i.1).mp hiActive).1
  have hbad :=
    sum_bad_incomingWitnessP_le_alpha_div
      D U S v hv hvcompl β hβ0
  have hbad' :
      (∑ c ∈ incomingWitnessBadCellsAt D U S v β,
        incomingWitnessP D U c) ≤ e / β := by
    simpa [heq] using hbad
  have hsplit :=
    goodAt_add_badAt_incomingWitnessP_eq_budget D U S v β
  have hactiveGood :=
    sum_activeGoodAt_incomingWitnessP_eq_goodAt D U S v β
  have hidecomp :
      (∑ j : ↥(incomingWitnessActiveGoodCellsAt D U S v β),
          incomingWitnessP D U j.1) =
        incomingWitnessP D U i.1 +
          ∑ j ∈ Finset.univ.erase i, incomingWitnessP D U j.1 := by
    have hiuniv :
        i ∈ (Finset.univ :
          Finset ↥(incomingWitnessActiveGoodCellsAt D U S v β)) :=
      Finset.mem_univ i
    have hsum :=
      Finset.sum_erase_add
        (Finset.univ :
          Finset ↥(incomingWitnessActiveGoodCellsAt D U S v β))
        (fun j => incomingWitnessP D U j.1) hiuniv
    simpa [add_comm] using hsum.symm
  have hactiveGood' :
      (∑ c ∈ incomingWitnessGoodCellsAt D U S v β,
          incomingWitnessP D U c) =
        incomingWitnessP D U i.1 +
          ∑ j ∈ Finset.univ.erase i, incomingWitnessP D U j.1 := by
    rw [← hactiveGood]
    rw [← Finset.sum_attach, Finset.attach_eq_univ]
    exact hidecomp
  have hbudgetDecomp :
      A - incomingWitnessP D U i.1 =
        (∑ c ∈ incomingWitnessBadCellsAt D U S v β,
            incomingWitnessP D U c) +
          (∑ j ∈ Finset.univ.erase i,
            incomingWitnessP D U j.1) := by
    dsimp [A]
    rw [← hsplit, hactiveGood']
    simp only [Finset.attach_eq_univ]
    abel
  refine ⟨i.1, hiS, ?_⟩
  rw [show subsetProjectorCommutatorOpNormSq D U S = A by rfl]
  rw [hbudgetDecomp]
  have htail :
      (∑ j ∈ Finset.univ.erase i,
        incomingWitnessP D U j.1) ≤
        (4 * (1 + t) * (e / (1 - β)) +
          (1 + 1 / t) * (e / (1 - β)) ^ 2) / L := by
    simpa [heq, e] using hitail
  have hsumBound :
      (∑ c ∈ incomingWitnessBadCellsAt D U S v β,
          incomingWitnessP D U c) +
        (∑ j ∈ Finset.univ.erase i,
          incomingWitnessP D U j.1) ≤
        e / β +
          (4 * (1 + t) * (e / (1 - β)) +
            (1 + 1 / t) * (e / (1 - β)) ^ 2) / L :=
    add_le_add hbad' htail
  simpa [e, A, C] using hsumBound

end
end EverettianDecoherence.Approximation

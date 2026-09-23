import EverettianDecoherence.Approximation.IncomingWitnessBudget

/-!
**FR.** Comptabilité du seuil variable beta utilisée par les théorèmes
asymptotiques v12. Une cellule est bonne si alpha <= beta p et mauvaise
sinon. Pour beta>0, la masse mauvaise est au plus e/beta. Pour beta<1, une
cellule bonne et active possède un budget témoin r strictement positif.

**EN.** Variable-threshold bookkeeping used by the v12 asymptotic theorems.
A cell is good when alpha <= beta p and bad otherwise. For beta>0 the bad
mass is at most e/beta. For beta<1 an active good cell has strictly positive
witness budget r.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

noncomputable def incomingWitnessBadCellsAt
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (β : ℝ) :
    Finset ((Projective.interface n).Cell D) :=
  S.filter fun c =>
    β * incomingWitnessP D U c < incomingWitnessAlpha D U c v

noncomputable def incomingWitnessGoodCellsAt
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (β : ℝ) :
    Finset ((Projective.interface n).Cell D) :=
  S.filter fun c =>
    incomingWitnessAlpha D U c v ≤ β * incomingWitnessP D U c

noncomputable def incomingWitnessActiveGoodCellsAt
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (β : ℝ) :
    Finset ((Projective.interface n).Cell D) :=
  (incomingWitnessGoodCellsAt D U S v β).filter fun c =>
    0 < incomingWitnessP D U c

theorem mem_incomingWitnessBadCellsAt
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (β : ℝ)
    (c : (Projective.interface n).Cell D) :
    c ∈ incomingWitnessBadCellsAt D U S v β ↔
      c ∈ S ∧
        β * incomingWitnessP D U c <
          incomingWitnessAlpha D U c v := by
  simp [incomingWitnessBadCellsAt]

theorem mem_incomingWitnessGoodCellsAt
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (β : ℝ)
    (c : (Projective.interface n).Cell D) :
    c ∈ incomingWitnessGoodCellsAt D U S v β ↔
      c ∈ S ∧
        incomingWitnessAlpha D U c v ≤
          β * incomingWitnessP D U c := by
  simp [incomingWitnessGoodCellsAt]

theorem mem_incomingWitnessActiveGoodCellsAt
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (β : ℝ)
    (c : (Projective.interface n).Cell D) :
    c ∈ incomingWitnessActiveGoodCellsAt D U S v β ↔
      c ∈ S ∧
      incomingWitnessAlpha D U c v ≤ β * incomingWitnessP D U c ∧
      0 < incomingWitnessP D U c := by
  simp [incomingWitnessActiveGoodCellsAt, incomingWitnessGoodCellsAt,
    and_assoc]

theorem sum_bad_incomingWitnessP_le_alpha_div
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (hv : ‖v‖ = 1)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v)
    (β : ℝ) (hβ : 0 < β) :
    (∑ c ∈ incomingWitnessBadCellsAt D U S v β,
        incomingWitnessP D U c) ≤
      (∑ c ∈ S, incomingWitnessAlpha D U c v) / β := by
  have hpoint :
      ∀ c ∈ incomingWitnessBadCellsAt D U S v β,
        incomingWitnessP D U c ≤
          incomingWitnessAlpha D U c v / β := by
    intro c hc
    have hbad := (mem_incomingWitnessBadCellsAt D U S v β c).mp hc
    have hlt :
        incomingWitnessP D U c <
          incomingWitnessAlpha D U c v / β := by
      apply (lt_div_iff₀ hβ).2
      simpa [mul_comm] using hbad.2
    exact hlt.le
  calc
    (∑ c ∈ incomingWitnessBadCellsAt D U S v β,
        incomingWitnessP D U c) ≤
      ∑ c ∈ incomingWitnessBadCellsAt D U S v β,
        incomingWitnessAlpha D U c v / β :=
      Finset.sum_le_sum hpoint
    _ = (∑ c ∈ incomingWitnessBadCellsAt D U S v β,
          incomingWitnessAlpha D U c v) / β := by
      rw [Finset.sum_div]
    _ ≤ (∑ c ∈ S, incomingWitnessAlpha D U c v) / β := by
      apply div_le_div_of_nonneg_right _ hβ.le
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro c hcS _hcnot
        exact incomingWitnessAlpha_nonneg_of_mem
          D U S c hcS v hv hvcompl

theorem goodAt_add_badAt_incomingWitnessP_eq_budget
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (β : ℝ) :
    (∑ c ∈ incomingWitnessGoodCellsAt D U S v β,
        incomingWitnessP D U c) +
      (∑ c ∈ incomingWitnessBadCellsAt D U S v β,
        incomingWitnessP D U c) =
      subsetProjectorCommutatorOpNormSq D U S := by
  unfold incomingWitnessGoodCellsAt incomingWitnessBadCellsAt
  unfold subsetProjectorCommutatorOpNormSq incomingWitnessP
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      S
      (fun c =>
        incomingWitnessAlpha D U c v ≤
          β * perspectiveProjectorCommutatorOpNormProfile D U c ^ 2)
      (fun c => perspectiveProjectorCommutatorOpNormProfile D U c ^ 2)
  simpa [not_le] using hsplit

theorem sum_activeGoodAt_incomingWitnessP_eq_goodAt
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (β : ℝ) :
    (∑ c ∈ incomingWitnessActiveGoodCellsAt D U S v β,
        incomingWitnessP D U c) =
      ∑ c ∈ incomingWitnessGoodCellsAt D U S v β,
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

theorem activeGoodAt_incomingWitnessP_mass_lower
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (hv : ‖v‖ = 1)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v)
    (β : ℝ) (hβ : 0 < β) :
    subsetProjectorCommutatorOpNormSq D U S -
        (∑ c ∈ S, incomingWitnessAlpha D U c v) / β ≤
      ∑ c ∈ incomingWitnessActiveGoodCellsAt D U S v β,
        incomingWitnessP D U c := by
  rw [sum_activeGoodAt_incomingWitnessP_eq_goodAt D U S v β]
  have hsplit := goodAt_add_badAt_incomingWitnessP_eq_budget D U S v β
  have hbad :=
    sum_bad_incomingWitnessP_le_alpha_div
      D U S v hv hvcompl β hβ
  linarith

theorem incomingWitnessR_pos_of_activeGoodAt
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (β : ℝ)
    (hβone : β < 1)
    (c : (Projective.interface n).Cell D)
    (hc : c ∈ incomingWitnessActiveGoodCellsAt D U S v β) :
    0 < incomingWitnessR D U c v := by
  have h := (mem_incomingWitnessActiveGoodCellsAt D U S v β c).mp hc
  unfold incomingWitnessAlpha at h
  nlinarith [mul_pos (sub_pos.mpr hβone) h.2.2]

end
end EverettianDecoherence.Approximation

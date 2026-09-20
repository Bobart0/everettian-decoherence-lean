import EverettianDecoherence.Approximation.IncomingWitnessGeometry
import EverettianDecoherence.Approximation.SubsetCommutatorBudget

/-!
**FR.** Comptabilité scalaire associée au témoin entrant d'un cut. Pour chaque
cellule sélectionnée, p_c est le carré de la norme opératorielle du
commutateur, r_c le carré de la norme du vecteur témoin transporté, et
alpha_c = p_c - r_c. Sur un témoin unitaire situé dans le complément,
alpha_c ≥ 0; leur somme est exactement le déficit du budget du cut par
rapport à la norme du bloc entrant. Les cellules où alpha_c > p_c / 2
portent au plus deux fois ce déficit total.

**EN.** Scalar bookkeeping for an incoming-cut witness. For every selected
cell, p_c is the squared cellwise commutator operator norm, r_c is the
squared norm of the transported witness vector, and alpha_c = p_c - r_c.
For a unit witness in the complementary subspace, alpha_c ≥ 0; their sum is
exactly the cut-budget deficit relative to the incoming block norm. Cells with
alpha_c > p_c / 2 carry at most twice the total deficit.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

noncomputable def incomingWitnessP
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (c : (Projective.interface n).Cell D) : ℝ :=
  perspectiveProjectorCommutatorOpNormProfile D U c ^ 2

noncomputable def incomingWitnessR
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (c : (Projective.interface n).Cell D) (v : H n) : ℝ :=
  ‖incomingWitnessCellVector D U c v‖ ^ 2

noncomputable def incomingWitnessAlpha
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (c : (Projective.interface n).Cell D) (v : H n) : ℝ :=
  incomingWitnessP D U c - incomingWitnessR D U c v

theorem incomingWitnessP_nonneg
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (c : (Projective.interface n).Cell D) :
    0 ≤ incomingWitnessP D U c := by
  unfold incomingWitnessP
  positivity

theorem incomingWitnessR_nonneg
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (c : (Projective.interface n).Cell D) (v : H n) :
    0 ≤ incomingWitnessR D U c v := by
  unfold incomingWitnessR
  positivity

theorem incomingWitnessAlpha_nonneg_of_mem
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : (Projective.interface n).Cell D) (hc : c ∈ S)
    (v : H n) (hv : ‖v‖ = 1)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v) :
    0 ≤ incomingWitnessAlpha D U c v := by
  unfold incomingWitnessAlpha incomingWitnessP incomingWitnessR
  exact sub_nonneg.mpr
    (incomingWitnessCellVector_norm_sq_le_commutator_sq
      D U S c hc v hv hvcompl)

theorem sum_incomingWitnessAlpha_eq_budget_sub_incoming
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v) :
    (∑ c ∈ S, incomingWitnessAlpha D U c v) =
      subsetProjectorCommutatorOpNormSq D U S -
        ‖recordSubsetIncoming D U S v‖ ^ 2 := by
  unfold incomingWitnessAlpha incomingWitnessP incomingWitnessR
  rw [Finset.sum_sub_distrib]
  change
    (∑ c ∈ S,
        perspectiveProjectorCommutatorOpNormProfile D U c ^ 2) -
      (∑ c ∈ S, ‖incomingWitnessCellVector D U c v‖ ^ 2) =
      subsetProjectorCommutatorOpNormSq D U S -
        ‖recordSubsetIncoming D U S v‖ ^ 2
  rw [sum_sq_norm_incomingWitnessCellVector_eq_incoming
    D U S v hvcompl]
  rfl

noncomputable def incomingWitnessBadCells
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) :
    Finset ((Projective.interface n).Cell D) :=
  S.filter fun c =>
    incomingWitnessP D U c / 2 < incomingWitnessAlpha D U c v

noncomputable def incomingWitnessGoodCells
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) :
    Finset ((Projective.interface n).Cell D) :=
  S.filter fun c =>
    incomingWitnessAlpha D U c v ≤ incomingWitnessP D U c / 2

theorem mem_incomingWitnessBadCells
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (c : (Projective.interface n).Cell D) :
    c ∈ incomingWitnessBadCells D U S v ↔
      c ∈ S ∧
        incomingWitnessP D U c / 2 <
          incomingWitnessAlpha D U c v := by
  simp [incomingWitnessBadCells]

theorem mem_incomingWitnessGoodCells
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (c : (Projective.interface n).Cell D) :
    c ∈ incomingWitnessGoodCells D U S v ↔
      c ∈ S ∧
        incomingWitnessAlpha D U c v ≤
          incomingWitnessP D U c / 2 := by
  simp [incomingWitnessGoodCells]

theorem sum_bad_incomingWitnessP_le_two_mul_alpha_sum
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (hv : ‖v‖ = 1)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v) :
    (∑ c ∈ incomingWitnessBadCells D U S v, incomingWitnessP D U c) ≤
      2 * (∑ c ∈ S, incomingWitnessAlpha D U c v) := by
  have hpoint :
      ∀ c ∈ incomingWitnessBadCells D U S v,
        incomingWitnessP D U c ≤
          2 * incomingWitnessAlpha D U c v := by
    intro c hc
    have hbad :=
      (mem_incomingWitnessBadCells D U S v c).mp hc
    linarith
  calc
    (∑ c ∈ incomingWitnessBadCells D U S v, incomingWitnessP D U c) ≤
        ∑ c ∈ incomingWitnessBadCells D U S v,
          2 * incomingWitnessAlpha D U c v :=
      Finset.sum_le_sum hpoint
    _ = 2 * ∑ c ∈ incomingWitnessBadCells D U S v,
          incomingWitnessAlpha D U c v := by
      rw [Finset.mul_sum]
    _ ≤ 2 * ∑ c ∈ S, incomingWitnessAlpha D U c v := by
      have hsum :
          (∑ c ∈ incomingWitnessBadCells D U S v,
              incomingWitnessAlpha D U c v) ≤
            ∑ c ∈ S, incomingWitnessAlpha D U c v := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro c hcS _hcnot
          exact incomingWitnessAlpha_nonneg_of_mem
            D U S c hcS v hv hvcompl
      exact mul_le_mul_of_nonneg_left hsum (by norm_num)


/-- The good and bad cells partition the full subset p-budget. -/
theorem good_add_bad_incomingWitnessP_eq_budget
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) :
    (∑ c ∈ incomingWitnessGoodCells D U S v,
        incomingWitnessP D U c) +
      (∑ c ∈ incomingWitnessBadCells D U S v,
        incomingWitnessP D U c) =
      subsetProjectorCommutatorOpNormSq D U S := by
  unfold incomingWitnessGoodCells incomingWitnessBadCells
  unfold subsetProjectorCommutatorOpNormSq incomingWitnessP
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      S
      (fun c =>
        incomingWitnessAlpha D U c v ≤
          (perspectiveProjectorCommutatorOpNormProfile D U c ^ 2) / 2)
      (fun c => perspectiveProjectorCommutatorOpNormProfile D U c ^ 2)
  simpa [not_le] using hsplit

theorem good_incomingWitnessP_mass_lower
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (v : H n) (hv : ‖v‖ = 1)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v) :
    subsetProjectorCommutatorOpNormSq D U S -
        2 * (∑ c ∈ S, incomingWitnessAlpha D U c v) ≤
      ∑ c ∈ incomingWitnessGoodCells D U S v,
        incomingWitnessP D U c := by
  have hsplitP :=
    good_add_bad_incomingWitnessP_eq_budget D U S v
  have hbad :=
    sum_bad_incomingWitnessP_le_two_mul_alpha_sum
      D U S v hv hvcompl
  linarith

end
end EverettianDecoherence.Approximation

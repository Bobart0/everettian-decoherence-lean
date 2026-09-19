import EverettianDecoherence.Approximation.TwoCellStabilityModulus
import EverettianDecoherence.Approximation.UniformTransferOptimality

/-!
**FR.** Passage opérationnel de la quasi-saturation T5 à la concentration sur
deux cellules. Pour un état normalisé concret, son sous-ensemble positif
contrôle exactement le profil L1 et son commutateur agrégé contrôle cet excès.
Ainsi une quasi-saturation de la borne sqrt(2) force ce cut positif dans le
régime du modulus eta-rho.

**EN.** Operational passage from near saturation of T5 to two-cell
concentration. For a concrete normalized state, its positive subset exactly
controls the L1 profile and its aggregate commutator controls that excess.
Hence near saturation of the sqrt(2) bound forces this positive cut into the
eta-rho modulus regime.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical

noncomputable section

/-- For a normalized state, its L1 record-profile variation is bounded by twice
the operator norm of the aggregate commutator on its positive subset. -/
theorem recordProfileL1_unitary_le_two_mul_positiveSubsetCommutatorOpNorm
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (x : H n) (hx : ‖x‖ = 1) :
    recordProfileL1 D (U x) x ≤
      2 * ‖recordSubsetProjectorCommutatorCLM D U
        (positiveRecordSubset D (U x) x)‖ := by
  let S := positiveRecordSubset D (U x) x
  have hdiff :
      ‖Gleason.projL (recordSubsetSubspace D S) (U x)‖ ^ 2 -
          ‖Gleason.projL (recordSubsetSubspace D S) x‖ ^ 2 ≤
        ‖recordSubsetProjectorCommutator D U S x‖ * ‖x‖ := by
    exact (le_abs_self _).trans
      (abs_recordSubsetProjector_norm_sq_sub_le_commutator D U S x)
  have hcomm :
      ‖recordSubsetProjectorCommutator D U S x‖ ≤
        ‖recordSubsetProjectorCommutatorCLM D U S‖ := by
    calc
      ‖recordSubsetProjectorCommutator D U S x‖ =
          ‖recordSubsetProjectorCommutatorCLM D U S x‖ := by rfl
      _ ≤ ‖recordSubsetProjectorCommutatorCLM D U S‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖recordSubsetProjectorCommutatorCLM D U S‖ := by rw [hx, mul_one]
  rw [recordProfileL1_unitary_eq_two_mul_recordSubsetProjector_excess]
  change
    2 * (
      ‖Gleason.projL (recordSubsetSubspace D S) (U x)‖ ^ 2 -
      ‖Gleason.projL (recordSubsetSubspace D S) x‖ ^ 2) ≤
      2 * ‖recordSubsetProjectorCommutatorCLM D U S‖
  calc
    2 * (
        ‖Gleason.projL (recordSubsetSubspace D S) (U x)‖ ^ 2 -
        ‖Gleason.projL (recordSubsetSubspace D S) x‖ ^ 2) ≤
      2 * (‖recordSubsetProjectorCommutator D U S x‖ * ‖x‖) := by
        gcongr
    _ = 2 * ‖recordSubsetProjectorCommutator D U S x‖ := by
      rw [hx, mul_one]
    _ ≤ 2 * ‖recordSubsetProjectorCommutatorCLM D U S‖ := by
      gcongr

/-- A concrete normalized state that nearly saturates the sharp T5 bound
forces two-cell concentration of the full squared commutator budget. -/
theorem exists_two_cell_concentration_of_near_saturated_state
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (x : H n) (hx : ‖x‖ = 1)
    (η ρ : ℝ)
    (hη0 : 0 ≤ η)
    (hηfive : η ≤ 1 / 5)
    (hρpos : 0 < ρ)
    (hρdelta : ρ ≤ operatorNormProjectorCommutatorL2 D U)
    (hnear :
      2 * (1 - η) * operatorNormProjectorCommutatorL2 D U ^ 2 ≤
        recordProfileL1 D (U x) x ^ 2) :
    ∃ i ∈ positiveRecordSubset D (U x) x,
      ∃ j ∈ (positiveRecordSubset D (U x) x)ᶜ,
        operatorNormProjectorCommutatorL2 D U ^ 2 -
            incomingWitnessP D U i - incomingWitnessP D U j ≤
          operatorNormProjectorCommutatorL2 D U ^ 2 *
            (2 * η +
              (36 * η / (1 - 3 * η)) / ρ ^ 2) := by
  let S := positiveRecordSubset D (U x) x
  let δ : ℝ := operatorNormProjectorCommutatorL2 D U
  let L : ℝ := recordProfileL1 D (U x) x
  let C : ℝ := ‖recordSubsetProjectorCommutatorCLM D U S‖
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact recordProfileL1_nonneg D (U x) x
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact norm_nonneg _
  have hLC : L ≤ 2 * C := by
    dsimp [L, C, S]
    exact recordProfileL1_unitary_le_two_mul_positiveSubsetCommutatorOpNorm
      D U x hx
  have hsq : L ^ 2 ≤ (2 * C) ^ 2 :=
    (sq_le_sq₀ hL0 (mul_nonneg (by norm_num) hC0)).2 hLC
  have hEη :
      δ ^ 2 - 2 * C ^ 2 ≤ η * δ ^ 2 := by
    have hnear' :
        2 * (1 - η) * δ ^ 2 ≤ L ^ 2 := by
      simpa [δ, L] using hnear
    nlinarith
  obtain ⟨i, hi, j, hj, htail⟩ :=
    exists_two_cell_concentration_of_cut_eta_rho
      D U S η ρ hη0 hηfive hρpos hρdelta
      (by simpa [δ, C, S] using hEη)
  exact ⟨i, hi, j, hj, by simpa [S] using htail⟩

end
end EverettianDecoherence.Approximation

import EverettianDecoherence.Approximation.RankOneCellCommutatorFormula
import EverettianDecoherence.Approximation.StabilitySharpness.Rotation3Entries

/-!
**FR.** Budgets cellulaires exacts de la famille tridimensionnelle de
sharpness. La formule rang-un réduit chaque carré de norme de commutateur à
un coefficient diagonal de l'unitaire explicite.

**EN.** Exact cellwise budgets of the three-dimensional sharpness family. The
rank-one formula reduces every squared commutator norm to one diagonal entry
of the explicit unitary.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped Classical InnerProductSpace Matrix BigOperators

noncomputable section

/-- Diagonal matrix entry as a Hilbert-space matrix coefficient. -/
theorem stabilitySharpnessRotation_inner_basis
    (n m : ℕ) (i : Fin 3) :
    inner ℂ (stabilitySharpnessBasis3 i : H 3)
      (stabilitySharpnessRotation n m
        (stabilitySharpnessBasis3 i : H 3)) =
      stabilitySharpnessRotationMatrix n m i i := by
  unfold stabilitySharpnessRotation
  change inner ℂ (EuclideanSpace.basisFun (Fin 3) ℂ i)
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ)
      (stabilitySharpnessRotationMatrix n m)
      (EuclideanSpace.basisFun (Fin 3) ℂ i)) = _
  rw [EuclideanSpace.basisFun_inner]
  change
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ)
      (stabilitySharpnessRotationMatrix n m)
      (EuclideanSpace.basisFun (Fin 3) ℂ i)).ofLp i = _
  rw [Matrix.ofLp_toEuclideanCLM]
  simp [Matrix.mulVec, dotProduct, EuclideanSpace.basisFun_apply,
    PiLp.ofLp_single]

theorem stabilitySharpnessCell0_budget_sq (n m : ℕ) :
    cellCommutatorOpNormSq stabilitySharpnessPerspective3
      (stabilitySharpnessRotation n m)
      (stabilitySharpnessCell3 (0 : Fin 3)) =
      2 * stabilitySharpnessD m * stabilitySharpnessA n ^ 2 -
        stabilitySharpnessD m ^ 2 * stabilitySharpnessA n ^ 4 := by
  change
    perspectiveProjectorCommutatorOpNormProfile
      stabilitySharpnessPerspective3 (stabilitySharpnessRotation n m)
        (stabilitySharpnessCell3 (0 : Fin 3)) ^ 2 = _
  rw [perspectiveProjectorCommutatorOpNormProfile_sq_rankOne
    stabilitySharpnessPerspective3 (stabilitySharpnessRotation n m)
    (stabilitySharpnessCell3 (0 : Fin 3))
    (stabilitySharpnessBasis3 (0 : Fin 3))
    (stabilitySharpnessBasis3_norm (0 : Fin 3))
    (stabilitySharpnessCell3_val (0 : Fin 3))]
  rw [stabilitySharpnessRotation_inner_basis,
    stabilitySharpnessRotationMatrix_00]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

theorem stabilitySharpnessCell1_budget_sq (n m : ℕ) :
    cellCommutatorOpNormSq stabilitySharpnessPerspective3
      (stabilitySharpnessRotation n m)
      (stabilitySharpnessCell3 (1 : Fin 3)) =
      2 * stabilitySharpnessD m * stabilitySharpnessB n ^ 2 -
        stabilitySharpnessD m ^ 2 * stabilitySharpnessB n ^ 4 := by
  change
    perspectiveProjectorCommutatorOpNormProfile
      stabilitySharpnessPerspective3 (stabilitySharpnessRotation n m)
        (stabilitySharpnessCell3 (1 : Fin 3)) ^ 2 = _
  rw [perspectiveProjectorCommutatorOpNormProfile_sq_rankOne
    stabilitySharpnessPerspective3 (stabilitySharpnessRotation n m)
    (stabilitySharpnessCell3 (1 : Fin 3))
    (stabilitySharpnessBasis3 (1 : Fin 3))
    (stabilitySharpnessBasis3_norm (1 : Fin 3))
    (stabilitySharpnessCell3_val (1 : Fin 3))]
  rw [stabilitySharpnessRotation_inner_basis,
    stabilitySharpnessRotationMatrix_11]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

theorem stabilitySharpnessCell2_budget_sq (n m : ℕ) :
    cellCommutatorOpNormSq stabilitySharpnessPerspective3
      (stabilitySharpnessRotation n m)
      (stabilitySharpnessCell3 (2 : Fin 3)) =
      iterationSharpnessS m ^ 2 := by
  change
    perspectiveProjectorCommutatorOpNormProfile
      stabilitySharpnessPerspective3 (stabilitySharpnessRotation n m)
        (stabilitySharpnessCell3 (2 : Fin 3)) ^ 2 = _
  rw [perspectiveProjectorCommutatorOpNormProfile_sq_rankOne
    stabilitySharpnessPerspective3 (stabilitySharpnessRotation n m)
    (stabilitySharpnessCell3 (2 : Fin 3))
    (stabilitySharpnessBasis3 (2 : Fin 3))
    (stabilitySharpnessBasis3_norm (2 : Fin 3))
    (stabilitySharpnessCell3_val (2 : Fin 3))]
  rw [stabilitySharpnessRotation_inner_basis,
    stabilitySharpnessRotationMatrix_22]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  nlinarith [iterationSharpnessC_sq_add_S_sq m]

end
end EverettianDecoherence.Approximation

import EverettianDecoherence.Approximation.OperatorNormProjectorCommutator

/-!
**FR.** Stabilité de structure projective **NON BORN-SENSITIVE**. Pour une
perspective fournie `D` et une isométrie linéaire surjective `U`, on transporte
le projecteur de chaque cellule par conjugaison `U P_c U⁻¹` et on compare
directement ce projecteur transporté au projecteur original. Aucune quantité
de record, aucun `bornRecord`, aucun poids et aucune interprétation de
décohérence n'interviennent.

**EN.** **NON BORN-SENSITIVE** projector-structure stability. For a supplied
perspective `D` and a surjective linear isometry `U`, each cell projector is
transported by conjugation `U P_c U⁻¹` and compared directly with the original
projector. No record quantity, `bornRecord`, weight, or decoherence
interpretation is involved.
-/

namespace EverettianDecoherence.Approximation

noncomputable def transportedCellProjector
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    Gleason.H n →ₗ[ℂ] Gleason.H n :=
  U.toLinearEquiv.toLinearMap.comp
    ((Gleason.projL c.val).comp U.symm.toLinearEquiv.toLinearMap)

noncomputable def projectorStructureDifference
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    Gleason.H n →ₗ[ℂ] Gleason.H n :=
  transportedCellProjector D U c - Gleason.projL c.val

noncomputable def projectorStructureDifferenceCLM
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    Gleason.H n →L[ℂ] Gleason.H n :=
  (projectorStructureDifference D U c).toContinuousLinearMap

theorem projectorStructureDifference_apply_transformed
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D)
    (x : Gleason.H n) :
    projectorStructureDifference D U c (U x) =
      -perspectiveProjectorCommutator D U c x := by
  change
    U (Gleason.projL c.val (U.symm (U x))) - Gleason.projL c.val (U x) =
      -(Gleason.projL c.val (U x) - U (Gleason.projL c.val x))
  rw [U.symm_apply_apply]
  abel

theorem projectorStructureDifferenceCLM_apply_transformed
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D)
    (x : Gleason.H n) :
    projectorStructureDifferenceCLM D U c (U x) =
      -perspectiveProjectorCommutator D U c x :=
  projectorStructureDifference_apply_transformed D U c x

noncomputable def projectorStructureOpNormProfile
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) :
    (EverettianProbability.Abstract.Projective.interface n).Cell D → ℝ :=
  fun c => ‖projectorStructureDifferenceCLM D U c‖

theorem projectorStructureOpNormProfile_nonneg
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    0 ≤ projectorStructureOpNormProfile D U c :=
  norm_nonneg _

theorem projectorStructureOpNormProfile_le_commutator
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    projectorStructureOpNormProfile D U c ≤
      perspectiveProjectorCommutatorOpNormProfile D U c := by
  unfold projectorStructureOpNormProfile perspectiveProjectorCommutatorOpNormProfile
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro y
  let x : Gleason.H n := U.symm y
  have hy : U x = y := by
    simp [x]
  calc
    ‖projectorStructureDifferenceCLM D U c y‖ =
        ‖projectorStructureDifferenceCLM D U c (U x)‖ := by rw [hy]
    _ = ‖perspectiveProjectorCommutator D U c x‖ := by
      rw [projectorStructureDifferenceCLM_apply_transformed]
      exact norm_neg _
    _ = ‖perspectiveProjectorCommutatorCLM D U c x‖ := rfl
    _ ≤ ‖perspectiveProjectorCommutatorCLM D U c‖ * ‖x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖perspectiveProjectorCommutatorCLM D U c‖ * ‖y‖ := by
      dsimp [x]
      rw [U.symm.norm_map]

noncomputable def projectorStructureDisplacementL2
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) : ℝ :=
  EverettianDecoherence.Metrics.finiteL2 (projectorStructureOpNormProfile D U)

theorem projectorStructureDisplacementL2_nonneg
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) :
    0 ≤ projectorStructureDisplacementL2 D U :=
  EverettianDecoherence.Metrics.finiteL2_nonneg _

theorem projectorStructureDisplacementL2_le_operatorNormProjectorCommutatorL2
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) :
    projectorStructureDisplacementL2 D U ≤ operatorNormProjectorCommutatorL2 D U := by
  unfold projectorStructureDisplacementL2 operatorNormProjectorCommutatorL2
  exact EverettianDecoherence.Metrics.finiteL2_mono_of_nonneg
    (projectorStructureOpNormProfile D U)
    (perspectiveProjectorCommutatorOpNormProfile D U)
    (projectorStructureOpNormProfile_nonneg D U)
    (perspectiveProjectorCommutatorOpNormProfile_nonneg D U)
    (projectorStructureOpNormProfile_le_commutator D U)

end EverettianDecoherence.Approximation

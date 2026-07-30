import EverettianDecoherence.Metrics.FiniteL2Triangle
import EverettianDecoherence.Approximation.OperatorNormProjectorCommutator

/-!
**FR.** Composition finie de deux transformations pour une perspective `D`
fixée. L'ordre de composition est explicite :
`linearIsometryEquivComp U V x = U (V x)`. Cette couche est algébrique,
n'utilise aucun `bornRecord` et ne porte aucune interprétation temporelle ni
aucune décohérence.

**EN.** Finite composition of two transformations for a fixed perspective
`D`. The composition order is explicit:
`linearIsometryEquivComp U V x = U (V x)`. This layer is algebraic, uses no
`bornRecord`, and carries no temporal interpretation or decoherence.
-/

namespace EverettianDecoherence.Approximation

noncomputable def linearIsometryEquivComp
    {n : ℕ} (U V : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) :
    Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n :=
  V.trans U

theorem linearIsometryEquivComp_apply
    {n : ℕ} (U V : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) :
    linearIsometryEquivComp U V x = U (V x) :=
  LinearIsometryEquiv.trans_apply V U x

theorem perspectiveProjectorCommutator_comp_apply
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U V : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D)
    (x : Gleason.H n) :
    perspectiveProjectorCommutator D (linearIsometryEquivComp U V) c x =
      perspectiveProjectorCommutator D U c (V x) +
        U (perspectiveProjectorCommutator D V c x) := by
  simp only [perspectiveProjectorCommutator_apply, linearIsometryEquivComp_apply, map_sub]
  abel

theorem perspectiveProjectorCommutator_comp
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U V : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    perspectiveProjectorCommutator D (linearIsometryEquivComp U V) c =
      (perspectiveProjectorCommutator D U c).comp V.toLinearEquiv.toLinearMap +
        U.toLinearEquiv.toLinearMap.comp (perspectiveProjectorCommutator D V c) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.add_apply, LinearMap.comp_apply]
  exact perspectiveProjectorCommutator_comp_apply D U V c x

theorem perspectiveProjectorCommutatorOpNormProfile_comp_le
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U V : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    perspectiveProjectorCommutatorOpNormProfile D (linearIsometryEquivComp U V) c ≤
      perspectiveProjectorCommutatorOpNormProfile D U c +
        perspectiveProjectorCommutatorOpNormProfile D V c := by
  unfold perspectiveProjectorCommutatorOpNormProfile
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  rw [perspectiveProjectorCommutatorCLM_apply, perspectiveProjectorCommutator_comp_apply]
  calc
    ‖perspectiveProjectorCommutator D U c (V x) +
        U (perspectiveProjectorCommutator D V c x)‖ ≤
        ‖perspectiveProjectorCommutator D U c (V x)‖ +
          ‖U (perspectiveProjectorCommutator D V c x)‖ := norm_add_le _ _
    _ = ‖perspectiveProjectorCommutator D U c (V x)‖ +
          ‖perspectiveProjectorCommutator D V c x‖ := by rw [U.norm_map]
    _ ≤ ‖perspectiveProjectorCommutatorCLM D U c‖ * ‖V x‖ +
          ‖perspectiveProjectorCommutatorCLM D V c‖ * ‖x‖ :=
        add_le_add
          (by rw [← perspectiveProjectorCommutatorCLM_apply]; exact ContinuousLinearMap.le_opNorm _ _)
          (by rw [← perspectiveProjectorCommutatorCLM_apply]; exact ContinuousLinearMap.le_opNorm _ _)
    _ = ‖perspectiveProjectorCommutatorCLM D U c‖ * ‖x‖ +
          ‖perspectiveProjectorCommutatorCLM D V c‖ * ‖x‖ := by rw [V.norm_map]
    _ = (‖perspectiveProjectorCommutatorCLM D U c‖ +
          ‖perspectiveProjectorCommutatorCLM D V c‖) * ‖x‖ := by ring

theorem operatorNormProjectorCommutatorL2_comp_le
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U V : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) :
    operatorNormProjectorCommutatorL2 D (linearIsometryEquivComp U V) ≤
      operatorNormProjectorCommutatorL2 D U + operatorNormProjectorCommutatorL2 D V := by
  unfold operatorNormProjectorCommutatorL2
  exact EverettianDecoherence.Metrics.finiteL2_le_add_of_pointwise_le_add
    (perspectiveProjectorCommutatorOpNormProfile D (linearIsometryEquivComp U V))
    (perspectiveProjectorCommutatorOpNormProfile D U)
    (perspectiveProjectorCommutatorOpNormProfile D V)
    (perspectiveProjectorCommutatorOpNormProfile_nonneg D (linearIsometryEquivComp U V))
    (perspectiveProjectorCommutatorOpNormProfile_nonneg D U)
    (perspectiveProjectorCommutatorOpNormProfile_nonneg D V)
    (fun c => perspectiveProjectorCommutatorOpNormProfile_comp_le D U V c)

theorem operatorNormProjectorCommutatorWithin_comp
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U V : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (ε δ : ℝ)
    (hU : operatorNormProjectorCommutatorWithin D U ε)
    (hV : operatorNormProjectorCommutatorWithin D V δ) :
    operatorNormProjectorCommutatorWithin D (linearIsometryEquivComp U V) (ε + δ) :=
  (operatorNormProjectorCommutatorL2_comp_le D U V).trans (add_le_add hU hV)

theorem operatorNormProjectorCommutatorL2_comp_eq_zero
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U V : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (hU : operatorNormProjectorCommutatorL2 D U = 0)
    (hV : operatorNormProjectorCommutatorL2 D V = 0) :
    operatorNormProjectorCommutatorL2 D (linearIsometryEquivComp U V) = 0 := by
  have h := operatorNormProjectorCommutatorL2_comp_le D U V
  rw [hU, hV, add_zero] at h
  exact le_antisymm h (operatorNormProjectorCommutatorL2_nonneg D (linearIsometryEquivComp U V))

end EverettianDecoherence.Approximation

import EverettianDecoherence.Metrics.FiniteL2Bounds
import EverettianDecoherence.Core.UpstreamAPI

/-!
**FR.** Couche algébrique : défaut de commutation des projecteurs d'une
perspective fournie, agrégé relativement à un état. Elle ne dépend pas de
`bornRecord`, ne formalise ni dynamique temporelle ni décohérence.

**EN.** Algebraic layer: a supplied perspective's projector-commutation defect,
aggregated relative to a state. It does not depend on `bornRecord` and
formalizes neither time dynamics nor decoherence.
-/

namespace EverettianDecoherence.Approximation

open scoped BigOperators

noncomputable def perspectiveProjectorCommutator
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    Gleason.H n →ₗ[ℂ] Gleason.H n :=
  (Gleason.projL c.val).comp U.toLinearEquiv.toLinearMap -
    U.toLinearEquiv.toLinearMap.comp (Gleason.projL c.val)

theorem perspectiveProjectorCommutator_apply
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D)
    (x : Gleason.H n) :
    perspectiveProjectorCommutator D U c x =
      Gleason.projL c.val (U x) - U (Gleason.projL c.val x) := by
  rfl

noncomputable def perspectiveProjectorCommutatorNormProfile
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) :
    (EverettianProbability.Abstract.Projective.interface n).Cell D → ℝ :=
  fun c => ‖perspectiveProjectorCommutator D U c x‖

noncomputable def statewiseProjectorCommutatorL2
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) : ℝ :=
  EverettianDecoherence.Metrics.finiteL2
    (perspectiveProjectorCommutatorNormProfile D U x)

def statewiseProjectorCommutatorWithin
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) (ε : ℝ) : Prop :=
  statewiseProjectorCommutatorL2 D U x ≤ ε

theorem perspectiveProjectorCommutatorNormProfile_nonneg
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    0 ≤ perspectiveProjectorCommutatorNormProfile D U x c :=
  norm_nonneg _

theorem statewiseProjectorCommutatorL2_nonneg
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) :
    0 ≤ statewiseProjectorCommutatorL2 D U x :=
  EverettianDecoherence.Metrics.finiteL2_nonneg _

theorem statewiseProjectorCommutatorWithin_mono
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n) (ε δ : ℝ) :
    statewiseProjectorCommutatorWithin D U x ε → ε ≤ δ →
      statewiseProjectorCommutatorWithin D U x δ := by
  intro h hεδ
  exact h.trans hεδ

theorem statewiseProjectorCommutatorL2_eq_zero_of_apply_eq_zero
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (U : Gleason.H n ≃ₗᵢ[ℂ] Gleason.H n) (x : Gleason.H n)
    (h : ∀ c, perspectiveProjectorCommutator D U c x = 0) :
    statewiseProjectorCommutatorL2 D U x = 0 := by
  unfold statewiseProjectorCommutatorL2 EverettianDecoherence.Metrics.finiteL2
    EverettianDecoherence.Metrics.finiteL2Sq
  simp [perspectiveProjectorCommutatorNormProfile, h]

theorem perspectiveProjectorCommutator_refl
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    perspectiveProjectorCommutator D (LinearIsometryEquiv.refl ℂ (Gleason.H n)) c = 0 := by
  apply LinearMap.ext
  intro x
  simp [perspectiveProjectorCommutator]

theorem statewiseProjectorCommutatorL2_refl
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) (x : Gleason.H n) :
    statewiseProjectorCommutatorL2 D (LinearIsometryEquiv.refl ℂ (Gleason.H n)) x = 0 :=
  statewiseProjectorCommutatorL2_eq_zero_of_apply_eq_zero D
    (LinearIsometryEquiv.refl ℂ (Gleason.H n)) x
    (fun c => congrArg (fun T : Gleason.H n →ₗ[ℂ] Gleason.H n => T x)
      (perspectiveProjectorCommutator_refl D c))

end EverettianDecoherence.Approximation

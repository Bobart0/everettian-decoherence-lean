import EverettianDecoherence.Approximation.RecordSubsetCrossBlockOpNorm
import EverettianDecoherence.Approximation.SubsetCommutatorBudget
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
**FR.** Symétrie par inversion unitaire. L'adjoint du bloc sortant pour U est
le bloc entrant pour U⁻¹, et réciproquement. L'adjoint du commutateur cellulaire
est l'opposé du commutateur pour U⁻¹. Les normes d'opérateur cellulaires,
les budgets quadratiques de sous-ensembles et la norme du commutateur agrégé
sont donc invariants par U ↦ U⁻¹.

**EN.** Unitary-inverse symmetry. The adjoint of the outgoing block for U is
the incoming block for U⁻¹, and conversely. The adjoint of each cell
commutator is the negative commutator for U⁻¹. Hence cellwise operator norms,
subset quadratic budgets, and the aggregate commutator norm are invariant
under U ↦ U⁻¹.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped Classical InnerProductSpace

noncomputable section

/-- The adjoint of the outgoing block for U is the incoming block for U⁻¹. -/
theorem recordSubsetOutgoingCLM_adjoint_eq_incoming_symm
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    ContinuousLinearMap.adjoint (recordSubsetOutgoingCLM D U S) =
      recordSubsetIncomingCLM D U.symm S := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  change
    inner ℂ
      (Gleason.projL (recordSubsetSubspace D Sᶜ)
        (U (Gleason.projL (recordSubsetSubspace D S) y))) x =
      inner ℂ y
        (Gleason.projL (recordSubsetSubspace D S)
          (U.symm (Gleason.projL (recordSubsetSubspace D Sᶜ) x)))
  have hQ (a b : H n) :
      inner ℂ (Gleason.projL (recordSubsetSubspace D Sᶜ) a) b =
        inner ℂ a (Gleason.projL (recordSubsetSubspace D Sᶜ) b) := by
    change inner ℂ
      ((recordSubsetSubspace D Sᶜ).starProjection a) b =
        inner ℂ a ((recordSubsetSubspace D Sᶜ).starProjection b)
    exact Submodule.inner_starProjection_left_eq_right _ _ _
  have hP (a b : H n) :
      inner ℂ (Gleason.projL (recordSubsetSubspace D S) a) b =
        inner ℂ a (Gleason.projL (recordSubsetSubspace D S) b) := by
    change inner ℂ
      ((recordSubsetSubspace D S).starProjection a) b =
        inner ℂ a ((recordSubsetSubspace D S).starProjection b)
    exact Submodule.inner_starProjection_left_eq_right _ _ _
  calc
    inner ℂ
        (Gleason.projL (recordSubsetSubspace D Sᶜ)
          (U (Gleason.projL (recordSubsetSubspace D S) y))) x =
      inner ℂ
        (U (Gleason.projL (recordSubsetSubspace D S) y))
        (Gleason.projL (recordSubsetSubspace D Sᶜ) x) :=
          hQ _ _
    _ = inner ℂ
        (Gleason.projL (recordSubsetSubspace D S) y)
        (U.symm (Gleason.projL (recordSubsetSubspace D Sᶜ) x)) :=
          U.inner_map_eq_flip _ _
    _ = inner ℂ y
        (Gleason.projL (recordSubsetSubspace D S)
          (U.symm (Gleason.projL (recordSubsetSubspace D Sᶜ) x))) :=
          hP _ _

/-- The adjoint of the incoming block for U is the outgoing block for U⁻¹. -/
theorem recordSubsetIncomingCLM_adjoint_eq_outgoing_symm
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    ContinuousLinearMap.adjoint (recordSubsetIncomingCLM D U S) =
      recordSubsetOutgoingCLM D U.symm S := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  change
    inner ℂ
      (Gleason.projL (recordSubsetSubspace D S)
        (U (Gleason.projL (recordSubsetSubspace D Sᶜ) y))) x =
      inner ℂ y
        (Gleason.projL (recordSubsetSubspace D Sᶜ)
          (U.symm (Gleason.projL (recordSubsetSubspace D S) x)))
  have hP (a b : H n) :
      inner ℂ (Gleason.projL (recordSubsetSubspace D S) a) b =
        inner ℂ a (Gleason.projL (recordSubsetSubspace D S) b) := by
    change inner ℂ
      ((recordSubsetSubspace D S).starProjection a) b =
        inner ℂ a ((recordSubsetSubspace D S).starProjection b)
    exact Submodule.inner_starProjection_left_eq_right _ _ _
  have hQ (a b : H n) :
      inner ℂ (Gleason.projL (recordSubsetSubspace D Sᶜ) a) b =
        inner ℂ a (Gleason.projL (recordSubsetSubspace D Sᶜ) b) := by
    change inner ℂ
      ((recordSubsetSubspace D Sᶜ).starProjection a) b =
        inner ℂ a ((recordSubsetSubspace D Sᶜ).starProjection b)
    exact Submodule.inner_starProjection_left_eq_right _ _ _
  calc
    inner ℂ
        (Gleason.projL (recordSubsetSubspace D S)
          (U (Gleason.projL (recordSubsetSubspace D Sᶜ) y))) x =
      inner ℂ
        (U (Gleason.projL (recordSubsetSubspace D Sᶜ) y))
        (Gleason.projL (recordSubsetSubspace D S) x) :=
          hP _ _
    _ = inner ℂ
        (Gleason.projL (recordSubsetSubspace D Sᶜ) y)
        (U.symm (Gleason.projL (recordSubsetSubspace D S) x)) :=
          U.inner_map_eq_flip _ _
    _ = inner ℂ y
        (Gleason.projL (recordSubsetSubspace D Sᶜ)
          (U.symm (Gleason.projL (recordSubsetSubspace D S) x))) :=
          hQ _ _

theorem recordSubsetOutgoingCLM_opNorm_eq_incoming_symm
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    ‖recordSubsetOutgoingCLM D U S‖ =
      ‖recordSubsetIncomingCLM D U.symm S‖ := by
  have hnorm :
      ‖ContinuousLinearMap.adjoint (recordSubsetOutgoingCLM D U S)‖ =
        ‖recordSubsetOutgoingCLM D U S‖ :=
    LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint
      (recordSubsetOutgoingCLM D U S)
  rw [recordSubsetOutgoingCLM_adjoint_eq_incoming_symm D U S] at hnorm
  exact hnorm.symm

theorem recordSubsetIncomingCLM_opNorm_eq_outgoing_symm
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    ‖recordSubsetIncomingCLM D U S‖ =
      ‖recordSubsetOutgoingCLM D U.symm S‖ := by
  have hnorm :
      ‖ContinuousLinearMap.adjoint (recordSubsetIncomingCLM D U S)‖ =
        ‖recordSubsetIncomingCLM D U S‖ :=
    LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint
      (recordSubsetIncomingCLM D U S)
  rw [recordSubsetIncomingCLM_adjoint_eq_outgoing_symm D U S] at hnorm
  exact hnorm.symm

/-- The adjoint of a cell commutator is the negative inverse-unitary
commutator. -/
theorem perspectiveProjectorCommutatorCLM_adjoint_eq_neg_symm
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (c : (Projective.interface n).Cell D) :
    ContinuousLinearMap.adjoint (perspectiveProjectorCommutatorCLM D U c) =
      - perspectiveProjectorCommutatorCLM D U.symm c := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  change
    inner ℂ
      (Gleason.projL c.val (U y) -
        U (Gleason.projL c.val y)) x =
      inner ℂ y
        (-(Gleason.projL c.val (U.symm x) -
          U.symm (Gleason.projL c.val x)))
  rw [inner_sub_left, inner_neg_right, inner_sub_right]
  have hP (a b : H n) :
      inner ℂ (Gleason.projL c.val a) b =
        inner ℂ a (Gleason.projL c.val b) := by
    change inner ℂ (c.val.starProjection a) b =
      inner ℂ a (c.val.starProjection b)
    exact Submodule.inner_starProjection_left_eq_right _ _ _
  have hfirst :
      inner ℂ (Gleason.projL c.val (U y)) x =
        inner ℂ y (U.symm (Gleason.projL c.val x)) := by
    calc
      inner ℂ (Gleason.projL c.val (U y)) x =
          inner ℂ (U y) (Gleason.projL c.val x) := hP _ _
      _ = inner ℂ y (U.symm (Gleason.projL c.val x)) :=
          U.inner_map_eq_flip _ _
  have hsecond :
      inner ℂ (U (Gleason.projL c.val y)) x =
        inner ℂ y (Gleason.projL c.val (U.symm x)) := by
    calc
      inner ℂ (U (Gleason.projL c.val y)) x =
          inner ℂ (Gleason.projL c.val y) (U.symm x) :=
            U.inner_map_eq_flip _ _
      _ = inner ℂ y (Gleason.projL c.val (U.symm x)) := hP _ _
  rw [hfirst, hsecond]
  ring

/-- Cellwise operator-norm commutator profiles are invariant under U ↦ U⁻¹. -/
theorem perspectiveProjectorCommutatorOpNormProfile_symm
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (c : (Projective.interface n).Cell D) :
    perspectiveProjectorCommutatorOpNormProfile D U.symm c =
      perspectiveProjectorCommutatorOpNormProfile D U c := by
  unfold perspectiveProjectorCommutatorOpNormProfile
  have hnorm :
      ‖ContinuousLinearMap.adjoint (perspectiveProjectorCommutatorCLM D U c)‖ =
        ‖perspectiveProjectorCommutatorCLM D U c‖ :=
    LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint
      (perspectiveProjectorCommutatorCLM D U c)
  rw [perspectiveProjectorCommutatorCLM_adjoint_eq_neg_symm D U c,
    norm_neg] at hnorm
  exact hnorm

theorem subsetProjectorCommutatorOpNormSq_symm
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    subsetProjectorCommutatorOpNormSq D U.symm S =
      subsetProjectorCommutatorOpNormSq D U S := by
  unfold subsetProjectorCommutatorOpNormSq
  apply Finset.sum_congr rfl
  intro c hc
  rw [perspectiveProjectorCommutatorOpNormProfile_symm D U c]

/-- The aggregate subset commutator operator norm is invariant under
U ↦ U⁻¹. -/
theorem recordSubsetProjectorCommutatorCLM_opNorm_symm
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    ‖recordSubsetProjectorCommutatorCLM D U.symm S‖ =
      ‖recordSubsetProjectorCommutatorCLM D U S‖ := by
  rw [recordSubsetProjectorCommutatorCLM_opNorm_eq_max_cross,
    recordSubsetProjectorCommutatorCLM_opNorm_eq_max_cross,
    ← recordSubsetOutgoingCLM_opNorm_eq_incoming_symm D U S,
    ← recordSubsetIncomingCLM_opNorm_eq_outgoing_symm D U S]
  rw [max_comm]

end
end EverettianDecoherence.Approximation

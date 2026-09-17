import EverettianDecoherence.Metrics.RecordSubsetProjector
import EverettianDecoherence.Approximation.ProjectorCommutator

/-!
**FR.** Commutateur associé au projecteur orthogonal sur un sous-ensemble
agrégé de cellules. Cette couche est algébrique ; elle ne définit ni temps,
ni dynamique physique, ni décohérence. La spécialisation ultérieure au
sous-ensemble positif d'une variation de profil est BORN-SENSITIVE.

**EN.** Commutator associated with the orthogonal projector onto an aggregated
subset of cells. This layer is algebraic; it defines neither time, physical
dynamics, nor decoherence. A later specialization to the positive subset of a
profile variation is BORN-SENSITIVE.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical InnerProductSpace

noncomputable section

/-- Linear commutator between a supplied unitary and the projector onto an
aggregated finite subset of cells. -/
noncomputable def recordSubsetProjectorCommutator
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) :
    H n →ₗ[ℂ] H n :=
  (Gleason.projL (recordSubsetSubspace D S)).comp U.toLinearEquiv.toLinearMap -
    U.toLinearEquiv.toLinearMap.comp
      (Gleason.projL (recordSubsetSubspace D S))

theorem recordSubsetProjectorCommutator_apply
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    recordSubsetProjectorCommutator D U S x =
      Gleason.projL (recordSubsetSubspace D S) (U x) -
        U (Gleason.projL (recordSubsetSubspace D S) x) := by
  rfl

private theorem re_inner_recordSubsetProjector_eq_norm_sq
    {n : ℕ} (D : Perspective n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    Complex.re
        ⟪Gleason.projL (recordSubsetSubspace D S) x, x⟫_ℂ =
      ‖Gleason.projL (recordSubsetSubspace D S) x‖ ^ 2 := by
  simpa [Gleason.projL, Submodule.starProjection_apply] using
    (Submodule.re_inner_starProjection_eq_normSq
      (𝕜 := ℂ) (recordSubsetSubspace D S) x)

/-- Difference of the squared projection norms is the real part of the
aggregate commutator expectation. -/
theorem recordSubsetProjector_norm_sq_sub_eq_re_inner_commutator
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    ‖Gleason.projL (recordSubsetSubspace D S) (U x)‖ ^ 2 -
        ‖Gleason.projL (recordSubsetSubspace D S) x‖ ^ 2 =
      Complex.re
        ⟪recordSubsetProjectorCommutator D U S x, U x⟫_ℂ := by
  rw [recordSubsetProjectorCommutator_apply]
  rw [inner_sub_left]
  rw [U.inner_map_map]
  rw [map_sub]
  rw [re_inner_recordSubsetProjector_eq_norm_sq D S (U x),
    re_inner_recordSubsetProjector_eq_norm_sq D S x]

/-- A unitary can change the probability of an aggregated subspace by at most
the statewise norm of its projector commutator, with constant one. -/
theorem abs_recordSubsetProjector_norm_sq_sub_le_commutator
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    |‖Gleason.projL (recordSubsetSubspace D S) (U x)‖ ^ 2 -
        ‖Gleason.projL (recordSubsetSubspace D S) x‖ ^ 2| ≤
      ‖recordSubsetProjectorCommutator D U S x‖ * ‖x‖ := by
  rw [recordSubsetProjector_norm_sq_sub_eq_re_inner_commutator D U S x]
  calc
    |Complex.re
        ⟪recordSubsetProjectorCommutator D U S x, U x⟫_ℂ| ≤
      ‖⟪recordSubsetProjectorCommutator D U S x, U x⟫_ℂ‖ :=
        RCLike.abs_re_le_norm _
    _ ≤ ‖recordSubsetProjectorCommutator D U S x‖ * ‖U x‖ :=
      norm_inner_le_norm _ _
    _ = ‖recordSubsetProjectorCommutator D U S x‖ * ‖x‖ := by
      rw [U.norm_map]

end
end EverettianDecoherence.Approximation

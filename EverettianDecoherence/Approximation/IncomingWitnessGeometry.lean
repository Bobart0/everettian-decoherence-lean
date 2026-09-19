import EverettianDecoherence.Approximation.RecordSubsetCrossBlockOpNorm
import EverettianDecoherence.Approximation.OperatorNormProjectorCommutator
import EverettianDecoherence.Metrics.NormalizedResidualStability

/-!
**FR.** Géométrie d'un témoin pour le bloc entrant d'un cut. On introduit
z_c = U⁻¹ P_c U v et son résidu par rapport à la cellule originale. Cette
couche relie les normes de commutateurs cellule-par-cellule à la stabilité de
Gram, sans quantité bornienne.

**EN.** Geometry of a witness for the incoming block of a cut. We introduce
z_c = U⁻¹ P_c U v and its residual relative to the original cell. This layer
connects cellwise commutator norms to Gram stability, with no Born quantity.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped BigOperators Classical InnerProductSpace

noncomputable section

/-- Back-transported cell component U⁻¹ P_c U v. -/
noncomputable def incomingWitnessCellVector
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (c : (Projective.interface n).Cell D) (v : H n) : H n :=
  U.symm (Gleason.projL c.val (U v))

/-- Residual of the back-transported cell component outside the original cell. -/
noncomputable def incomingWitnessCellResidual
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (c : (Projective.interface n).Cell D) (v : H n) : H n :=
  incomingWitnessCellVector D U c v -
    Gleason.projL c.val (incomingWitnessCellVector D U c v)

@[simp]
theorem norm_incomingWitnessCellVector
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (c : (Projective.interface n).Cell D) (v : H n) :
    ‖incomingWitnessCellVector D U c v‖ =
      ‖Gleason.projL c.val (U v)‖ := by
  unfold incomingWitnessCellVector
  exact U.symm.norm_map _

/-- Distinct witness cell vectors are orthogonal. -/
theorem incomingWitnessCellVector_inner_eq_zero_of_ne
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    {c d : (Projective.interface n).Cell D} (hcd : c ≠ d)
    (v : H n) :
    inner ℂ (incomingWitnessCellVector D U c v)
      (incomingWitnessCellVector D U d v) = 0 := by
  unfold incomingWitnessCellVector
  rw [LinearIsometryEquiv.inner_map_map]
  have hcc : c.val ⟂ d.val :=
    D.ortho c.val c.property d.val d.property
      (fun hval => hcd (Subtype.ext hval))
  have hc_mem : Gleason.projL c.val (U v) ∈ c.val :=
    Submodule.starProjection_apply_mem c.val (U v)
  have hd_mem : Gleason.projL d.val (U v) ∈ d.val :=
    Submodule.starProjection_apply_mem d.val (U v)
  have hc_perp : Gleason.projL c.val (U v) ∈ d.valᗮ := hcc hc_mem
  have hz :
      inner ℂ (Gleason.projL d.val (U v))
        (Gleason.projL c.val (U v)) = 0 :=
    (Submodule.mem_orthogonal d.val (Gleason.projL c.val (U v))).mp hc_perp
      (Gleason.projL d.val (U v)) hd_mem
  rw [← inner_conj_symm (Gleason.projL c.val (U v))
    (Gleason.projL d.val (U v)), hz]
  simp

/-- The witness-cell squared norms add to the squared norm of the aggregate
projection of Uv onto the selected cells. -/
theorem sum_sq_norm_incomingWitnessCellVector
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (v : H n) :
    (∑ c ∈ S, ‖incomingWitnessCellVector D U c v‖ ^ 2) =
      ‖Gleason.projL (recordSubsetSubspace D S) (U v)‖ ^ 2 := by
  simp_rw [norm_incomingWitnessCellVector]
  exact (norm_sq_recordSubsetProjector_eq_sum D S (U v)).symm

/-- If v lies in the complementary aggregate subspace, the previous sum is
exactly the squared incoming-block norm at v. -/
theorem sum_sq_norm_incomingWitnessCellVector_eq_incoming
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D)) (v : H n)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v) :
    (∑ c ∈ S, ‖incomingWitnessCellVector D U c v‖ ^ 2) =
      ‖recordSubsetIncoming D U S v‖ ^ 2 := by
  rw [sum_sq_norm_incomingWitnessCellVector]
  unfold recordSubsetIncoming
  rw [hvcompl]

private theorem recordCellProjector_apply_eq_zero_of_mem_of_compl_fixed
    {n : ℕ} (D : Perspective n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : (Projective.interface n).Cell D) (hc : c ∈ S)
    (v : H n)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v) :
    Gleason.projL c.val v = 0 := by
  have h :=
    recordCellProjector_compl_apply_eq_zero_of_mem D S c hc v
  rw [hvcompl] at h
  exact h

/-- On a complementary witness, the cell commutator is exactly the selected
cell component of Uv. -/
theorem perspectiveProjectorCommutator_apply_complWitness
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : (Projective.interface n).Cell D) (hc : c ∈ S)
    (v : H n)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v) :
    perspectiveProjectorCommutator D U c v =
      Gleason.projL c.val (U v) := by
  rw [perspectiveProjectorCommutator_apply,
    recordCellProjector_apply_eq_zero_of_mem_of_compl_fixed
      D S c hc v hvcompl,
    map_zero, sub_zero]

/-- For a unit complementary witness, r_c = ||z_c||^2 is bounded by the
squared cellwise commutator operator norm p_c. -/
theorem incomingWitnessCellVector_norm_sq_le_commutator_sq
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : (Projective.interface n).Cell D) (hc : c ∈ S)
    (v : H n) (hv : ‖v‖ = 1)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v) :
    ‖incomingWitnessCellVector D U c v‖ ^ 2 ≤
      perspectiveProjectorCommutatorOpNormProfile D U c ^ 2 := by
  rw [norm_incomingWitnessCellVector]
  have hle :=
    perspectiveProjectorCommutatorNormProfile_le_opNorm_mul_norm D U v c
  unfold perspectiveProjectorCommutatorNormProfile at hle
  rw [perspectiveProjectorCommutator_apply_complWitness
    D U S c hc v hvcompl, hv, mul_one] at hle
  exact (sq_le_sq₀ (norm_nonneg _)
    (perspectiveProjectorCommutatorOpNormProfile_nonneg D U c)).2 hle

/-- Applying U to the residual gives the original cell commutator acting on
the back-transported cell vector. -/
theorem map_incomingWitnessCellResidual
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (c : (Projective.interface n).Cell D) (v : H n) :
    U (incomingWitnessCellResidual D U c v) =
      perspectiveProjectorCommutator D U c
        (incomingWitnessCellVector D U c v) := by
  unfold incomingWitnessCellResidual incomingWitnessCellVector
  rw [map_sub, U.apply_symm_apply, perspectiveProjectorCommutator_apply,
    U.apply_symm_apply]
  have hidem :
      Gleason.projL c.val (Gleason.projL c.val (U v)) =
        Gleason.projL c.val (U v) := by
    unfold Gleason.projL
    exact Submodule.starProjection_eq_self_iff.mpr
      (Submodule.starProjection_apply_mem c.val (U v))
  rw [hidem]

/-- The residual satisfies ||q_c||^2 ≤ p_c r_c. -/
theorem incomingWitnessCellResidual_norm_sq_le
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (c : (Projective.interface n).Cell D) (v : H n) :
    ‖incomingWitnessCellResidual D U c v‖ ^ 2 ≤
      perspectiveProjectorCommutatorOpNormProfile D U c ^ 2 *
        ‖incomingWitnessCellVector D U c v‖ ^ 2 := by
  have hle :=
    perspectiveProjectorCommutatorNormProfile_le_opNorm_mul_norm
      D U (incomingWitnessCellVector D U c v) c
  unfold perspectiveProjectorCommutatorNormProfile at hle
  rw [← map_incomingWitnessCellResidual D U c v, U.norm_map] at hle
  have hs :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg
        (perspectiveProjectorCommutatorOpNormProfile_nonneg D U c)
        (norm_nonneg _))).2 hle
  simpa [mul_pow] using hs

/-- For a complementary witness, the real inner component of the residual
along v is exactly r_c = ||z_c||^2. -/
theorem re_inner_incomingWitnessCellResidual_eq_norm_sq
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : (Projective.interface n).Cell D) (hc : c ∈ S)
    (v : H n)
    (hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v) :
    RCLike.re
      (inner ℂ v (incomingWitnessCellResidual D U c v)) =
      ‖incomingWitnessCellVector D U c v‖ ^ 2 := by
  have hcellzero :
      Gleason.projL c.val v = 0 :=
    recordCellProjector_apply_eq_zero_of_mem_of_compl_fixed
      D S c hc v hvcompl
  have hprojzero :
      inner ℂ v
        (Gleason.projL c.val (incomingWitnessCellVector D U c v)) = 0 := by
    rw [← Submodule.inner_starProjection_left_eq_right c.val, hcellzero,
      inner_zero_left]
  have hvz :
      inner ℂ v (incomingWitnessCellVector D U c v) =
        inner ℂ (Gleason.projL c.val (U v))
          (Gleason.projL c.val (U v)) := by
    unfold incomingWitnessCellVector
    rw [← U.inner_map_eq_flip]
    have hidem :
        Gleason.projL c.val (Gleason.projL c.val (U v)) =
          Gleason.projL c.val (U v) := by
      unfold Gleason.projL
      exact Submodule.starProjection_eq_self_iff.mpr
        (Submodule.starProjection_apply_mem c.val (U v))
    rw [← Submodule.inner_starProjection_left_eq_right c.val, hidem]
  unfold incomingWitnessCellResidual
  rw [inner_sub_right, hprojzero, sub_zero, hvz,
    inner_self_eq_norm_sq]
  rw [norm_incomingWitnessCellVector]

end
end EverettianDecoherence.Approximation

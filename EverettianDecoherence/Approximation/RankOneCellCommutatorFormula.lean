import EverettianDecoherence.Approximation.RankOneCellCommutator

/-!
**FR.** Formule fermée du commutateur pour une cellule de rang un. Pour une
cellule c = span{e}, ||e||=1, les deux blocs croisés d'une unitaire ont la
même norme et le carré de la norme du commutateur cellulaire vaut
1 - ||<e,Ue>||^2.

**EN.** Closed commutator formula for a rank-one cell. For a cell
c = span{e}, ||e||=1, the two cross blocks of a unitary have the same norm and
the squared norm of the cell commutator is 1 - ||<e,Ue>||^2.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped Classical InnerProductSpace

noncomputable section

theorem rankOneCell_projection_norm_sq
    {n : ℕ} (U : H n ≃ₗᵢ[ℂ] H n)
    (c : Submodule ℂ (H n))
    (e : H n) (he : ‖e‖ = 1)
    (hc : c = ℂ ∙ e) :
    ‖Gleason.projL c (U e)‖ ^ 2 =
      ‖inner ℂ e (U e)‖ ^ 2 := by
  rw [hc]
  change ‖(ℂ ∙ e).starProjection (U e)‖ ^ 2 = _
  rw [Submodule.starProjection_unit_singleton ℂ he]
  rw [norm_smul, he, mul_one]

theorem recordSubsetOutgoingCLM_singleton_opNorm_sq_diagonal
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (c : (Projective.interface n).Cell D)
    (e : H n) (he : ‖e‖ = 1)
    (hc : c.val = ℂ ∙ e) :
    ‖recordSubsetOutgoingCLM D U {c}‖ ^ 2 =
      1 - ‖inner ℂ e (U e)‖ ^ 2 := by
  rw [recordSubsetOutgoingCLM_singleton_opNorm_sq D U c e he hc]
  rw [rankOneCell_projection_norm_sq U c.val e he hc]

theorem norm_inner_unitary_symm_self_eq
    {n : ℕ} (U : H n ≃ₗᵢ[ℂ] H n) (e : H n) :
    ‖inner ℂ e (U.symm e)‖ = ‖inner ℂ e (U e)‖ := by
  calc
    ‖inner ℂ e (U.symm e)‖ =
        ‖inner ℂ (U e) e‖ := by
      rw [U.inner_map_eq_flip e e]
    _ = ‖inner ℂ e (U e)‖ :=
      norm_inner_symm (U e) e

theorem recordSubsetIncomingCLM_singleton_opNorm_sq_diagonal
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (c : (Projective.interface n).Cell D)
    (e : H n) (he : ‖e‖ = 1)
    (hc : c.val = ℂ ∙ e) :
    ‖recordSubsetIncomingCLM D U {c}‖ ^ 2 =
      1 - ‖inner ℂ e (U e)‖ ^ 2 := by
  rw [recordSubsetIncomingCLM_opNorm_eq_outgoing_symm D U {c}]
  rw [recordSubsetOutgoingCLM_singleton_opNorm_sq_diagonal
    D U.symm c e he hc]
  rw [norm_inner_unitary_symm_self_eq U e]

theorem recordSubsetIncomingCLM_singleton_opNorm_eq_outgoing
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (c : (Projective.interface n).Cell D)
    (e : H n) (he : ‖e‖ = 1)
    (hc : c.val = ℂ ∙ e) :
    ‖recordSubsetIncomingCLM D U {c}‖ =
      ‖recordSubsetOutgoingCLM D U {c}‖ := by
  have hin :=
    recordSubsetIncomingCLM_singleton_opNorm_sq_diagonal
      D U c e he hc
  have hout :=
    recordSubsetOutgoingCLM_singleton_opNorm_sq_diagonal
      D U c e he hc
  have hnonneg_in : 0 ≤ ‖recordSubsetIncomingCLM D U {c}‖ := norm_nonneg _
  have hnonneg_out : 0 ≤ ‖recordSubsetOutgoingCLM D U {c}‖ := norm_nonneg _
  nlinarith

/-- Closed squared operator-norm formula for a rank-one cell commutator. -/
theorem perspectiveProjectorCommutatorOpNormProfile_sq_rankOne
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (c : (Projective.interface n).Cell D)
    (e : H n) (he : ‖e‖ = 1)
    (hc : c.val = ℂ ∙ e) :
    perspectiveProjectorCommutatorOpNormProfile D U c ^ 2 =
      1 - ‖inner ℂ e (U e)‖ ^ 2 := by
  have hsingle :
      ‖perspectiveProjectorCommutatorCLM D U c‖ =
        ‖recordSubsetProjectorCommutatorCLM D U {c}‖ := by
    rw [recordSubsetProjectorCommutatorCLM_singleton]
  have hcross :=
    recordSubsetProjectorCommutatorCLM_opNorm_eq_max_cross
      D U {c}
  have heq :=
    recordSubsetIncomingCLM_singleton_opNorm_eq_outgoing
      D U c e he hc
  unfold perspectiveProjectorCommutatorOpNormProfile
  rw [hsingle, hcross, heq, max_self]
  exact recordSubsetOutgoingCLM_singleton_opNorm_sq_diagonal
    D U c e he hc

end
end EverettianDecoherence.Approximation

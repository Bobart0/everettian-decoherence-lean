import EverettianDecoherence.Approximation.RecordSubsetCrossBlockOpNorm
import EverettianDecoherence.Metrics.FiniteDimensionalOpNorm

/-!
**FR.** Construction d'un témoin unitaire normant pour le bloc entrant
P_S U P_{S^c}. Si la norme du bloc est strictement positive, un vecteur
normant arbitraire peut être projeté sur le complément sans changer la sortie.
L'égalité de norme force alors cette projection à rester unitaire.

**EN.** Construction of a unit norming witness for the incoming block
P_S U P_{S^c}. If the block norm is strictly positive, an arbitrary norming
vector can be projected onto the complement without changing the output.
Norm equality then forces that projection to remain unit.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open scoped Classical

noncomputable section

private theorem incomingCLM_project_compl_eq
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (x : H n) :
    recordSubsetIncomingCLM D U S
        (Gleason.projL (recordSubsetSubspace D Sᶜ) x) =
      recordSubsetIncomingCLM D U S x := by
  change
    recordSubsetIncoming D U S
        (Gleason.projL (recordSubsetSubspace D Sᶜ) x) =
      recordSubsetIncoming D U S x
  unfold recordSubsetIncoming Gleason.projL
  have hidem :
      (recordSubsetSubspace D Sᶜ).starProjection
          ((recordSubsetSubspace D Sᶜ).starProjection x) =
        (recordSubsetSubspace D Sᶜ).starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr
      (Submodule.starProjection_apply_mem (recordSubsetSubspace D Sᶜ) x)
  exact congrArg
    (fun y =>
      (recordSubsetSubspace D S).starProjection (U y))
    hidem

/-- A positive incoming-block norm is attained by a unit vector fixed by the
complement projector. -/
theorem exists_unit_complWitness_norm_incoming
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n)
    (S : Finset ((Projective.interface n).Cell D))
    (hpos : 0 < ‖recordSubsetIncomingCLM D U S‖) :
    ∃ v : H n,
      ‖v‖ = 1 ∧
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v ∧
      ‖recordSubsetIncoming D U S v‖ =
        ‖recordSubsetIncomingCLM D U S‖ := by
  obtain ⟨x, hx, hnorm⟩ :=
    exists_unit_norm_apply_eq_opNorm_of_pos
      (recordSubsetIncomingCLM D U S) hpos
  let v : H n := Gleason.projL (recordSubsetSubspace D Sᶜ) x
  have hTv :
      recordSubsetIncomingCLM D U S v =
        recordSubsetIncomingCLM D U S x := by
    dsimp [v]
    exact incomingCLM_project_compl_eq D U S x
  have hTvnorm :
      ‖recordSubsetIncomingCLM D U S v‖ =
        ‖recordSubsetIncomingCLM D U S‖ := by
    rw [hTv, hnorm]
  have hvle : ‖v‖ ≤ 1 := by
    calc
      ‖v‖ ≤ ‖x‖ := by
        dsimp [v]
        unfold Gleason.projL
        exact Submodule.norm_starProjection_apply_le
          (K := recordSubsetSubspace D Sᶜ) x
      _ = 1 := hx
  have hbound :
      ‖recordSubsetIncomingCLM D U S‖ ≤
        ‖recordSubsetIncomingCLM D U S‖ * ‖v‖ := by
    calc
      ‖recordSubsetIncomingCLM D U S‖ =
          ‖recordSubsetIncomingCLM D U S v‖ := hTvnorm.symm
      _ ≤ ‖recordSubsetIncomingCLM D U S‖ * ‖v‖ :=
        (recordSubsetIncomingCLM D U S).le_opNorm v
  have hvge : 1 ≤ ‖v‖ := by
    nlinarith
  have hv : ‖v‖ = 1 := le_antisymm hvle hvge
  have hvcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) v = v := by
    dsimp [v]
    unfold Gleason.projL
    exact Submodule.starProjection_eq_self_iff.mpr
      (Submodule.starProjection_apply_mem (recordSubsetSubspace D Sᶜ) x)
  refine ⟨v, hv, hvcompl, ?_⟩
  change ‖recordSubsetIncomingCLM D U S v‖ =
    ‖recordSubsetIncomingCLM D U S‖
  exact hTvnorm

end
end EverettianDecoherence.Approximation

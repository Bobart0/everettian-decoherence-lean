import EverettianDecoherence.Metrics.FiniteL2Bounds
import EverettianDecoherence.Metrics.RecordProfileL1

/-!
**FR.** Identités quadratiques globales d'une perspective projective finie.
La décomposition est cinématique ; l'emploi de `bornRecord` est BORN-SENSITIVE.
Aucune dynamique ni aucun théorème de décohérence n'est impliqué.

**EN.** Global quadratic identities for a finite projective perspective. The
decomposition is kinematic; use of `bornRecord` is BORN-SENSITIVE. No dynamics
or decoherence theorem is involved.
-/

namespace EverettianDecoherence.Metrics

open scoped BigOperators

noncomputable def recordCellNormProfile
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) (x : Gleason.H n) :
    (EverettianProbability.Abstract.Projective.interface n).Cell D → ℝ :=
  fun c => ‖Gleason.projL c.val x‖

theorem recordCellNormProfile_nonneg
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) (x : Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    0 ≤ recordCellNormProfile D x c :=
  norm_nonneg _

theorem recordCellNormProfile_sq_eq_bornRecord
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) (x : Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    (recordCellNormProfile D x c) ^ 2 =
      EverettianProbability.Abstract.bornRecord D x c :=
  rfl

theorem sum_sq_recordCellNormProfile_eq_norm_sq
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) (z : Gleason.H n) :
    (∑ c : (EverettianProbability.Abstract.Projective.interface n).Cell D,
      (recordCellNormProfile D z c) ^ 2) = ‖z‖ ^ 2 := by
  change (∑ c : {c : Submodule ℂ (Gleason.H n) // c ∈ D.cells},
    ‖Gleason.projL c.val z‖ ^ 2) = ‖z‖ ^ 2
  calc
    (∑ c : {c : Submodule ℂ (Gleason.H n) // c ∈ D.cells},
      ‖Gleason.projL c.val z‖ ^ 2) =
        ∑ c ∈ D.cells, ‖Gleason.projL c z‖ ^ 2 := by
      symm
      exact Finset.sum_subtype D.cells (fun c => Iff.rfl)
        (fun c => ‖Gleason.projL c z‖ ^ 2)
    _ = ‖z‖ ^ 2 := by
      have h := QuantumFoundations.BornRule.sum_sq_projL_of_pairwise_isOrtho
        D.cells D.ortho z
      rw [Finset.sup_id_eq_sSup, D.span] at h
      have htop : Gleason.projL (⊤ : Submodule ℂ (Gleason.H n)) = LinearMap.id := by
        unfold Gleason.projL
        rw [Submodule.starProjection_top]
        rfl
      rw [htop] at h
      simpa using h.symm

theorem sqrt_sum_sq_recordCellNormProfile_eq_norm
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) (z : Gleason.H n) :
    Real.sqrt (∑ c : (EverettianProbability.Abstract.Projective.interface n).Cell D,
      (recordCellNormProfile D z c) ^ 2) = ‖z‖ := by
  rw [sum_sq_recordCellNormProfile_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem abs_recordCellNormProfile_sub_le
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) (x y : Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    |recordCellNormProfile D x c - recordCellNormProfile D y c| ≤
      recordCellNormProfile D (x - y) c := by
  unfold recordCellNormProfile
  calc
    |‖Gleason.projL c.val x‖ - ‖Gleason.projL c.val y‖| ≤
        ‖Gleason.projL c.val x - Gleason.projL c.val y‖ :=
      abs_norm_sub_norm_le _ _
    _ = ‖Gleason.projL c.val (x - y)‖ := by
      rw [(Gleason.projL c.val).map_sub]

end EverettianDecoherence.Metrics

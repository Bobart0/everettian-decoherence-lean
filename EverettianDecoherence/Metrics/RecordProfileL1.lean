import EverettianDecoherence.Metrics.FiniteProfileL1
import EverettianDecoherence.Core.UpstreamAPI

/-!
**FR.** Cette couche utilise explicitement `bornRecord` : elle est donc
BORN-SENSITIVE. Elle ne définit pas indépendamment la décohérence et ne dérive
pas Born ; elle fournit une interface quantitative vers la structure exacte
finie amont.

**EN.** This layer explicitly uses `bornRecord`, and is therefore
BORN-SENSITIVE. It neither independently defines decoherence nor derives Born;
it provides a quantitative interface to the upstream exact-finite structure.
-/

namespace EverettianDecoherence.Metrics

noncomputable def recordProfile
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) (x : Gleason.H n) :
    (EverettianProbability.Abstract.Projective.interface n).Cell D → ℝ :=
  fun c => EverettianProbability.Abstract.bornRecord D x c

noncomputable def recordProfileL1
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (x y : Gleason.H n) : ℝ :=
  finiteProfileL1 (recordProfile D x) (recordProfile D y)

def recordProfileWithin
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) (ε : ℝ)
    (x y : Gleason.H n) : Prop :=
  recordProfileL1 D x y ≤ ε

theorem recordProfileL1_nonneg
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) (x y : Gleason.H n) :
    0 ≤ recordProfileL1 D x y :=
  finiteProfileL1_nonneg _ _

theorem recordProfileL1_self
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) (x : Gleason.H n) :
    recordProfileL1 D x x = 0 :=
  finiteProfileL1_self _

theorem recordProfileL1_symm
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) (x y : Gleason.H n) :
    recordProfileL1 D x y = recordProfileL1 D y x :=
  finiteProfileL1_symm _ _

theorem recordProfileL1_triangle
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (x y z : Gleason.H n) :
    recordProfileL1 D x z ≤ recordProfileL1 D x y + recordProfileL1 D y z :=
  finiteProfileL1_triangle _ _ _

theorem abs_bornRecord_sub_le_recordProfileL1
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n)
    (x y : Gleason.H n)
    (c : (EverettianProbability.Abstract.Projective.interface n).Cell D) :
    |EverettianProbability.Abstract.bornRecord D x c -
        EverettianProbability.Abstract.bornRecord D y c| ≤ recordProfileL1 D x y :=
  abs_sub_le_finiteProfileL1 _ _ c

theorem recordProfileL1_eq_zero_iff_sameRecord
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) (x y : Gleason.H n) :
    recordProfileL1 D x y = 0 ↔
      EverettianProbability.API.ExactFinite.SameRecord D x y := by
  constructor
  · intro h
    have hprofiles : recordProfile D x = recordProfile D y :=
      (finiteProfileL1_eq_zero_iff _ _).mp h
    change ∀ c, EverettianProbability.Abstract.bornRecord D x c =
      EverettianProbability.Abstract.bornRecord D y c
    intro c
    exact congrFun hprofiles c
  · intro h
    apply (finiteProfileL1_eq_zero_iff _ _).mpr
    funext c
    change EverettianProbability.Abstract.bornRecord D x c =
      EverettianProbability.Abstract.bornRecord D y c
    exact h c

theorem recordProfileL1_eq_zero_of_recordUnitaryOrbit
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) (x y : Gleason.H n)
    (h : EverettianProbability.API.ExactFinite.RecordUnitaryOrbit D x y) :
    recordProfileL1 D x y = 0 :=
  (recordProfileL1_eq_zero_iff_sameRecord D x y).mpr
    ((EverettianProbability.API.ExactFinite.recordUnitaryOrbit_iff_sameRecord D x y).mp h)

theorem recordProfileWithin_refl
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) (ε : ℝ)
    (x : Gleason.H n) (hε : 0 ≤ ε) :
    recordProfileWithin D ε x x := by
  unfold recordProfileWithin
  rw [recordProfileL1_self]
  exact hε

theorem recordProfileWithin_symm
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) (ε : ℝ)
    (x y : Gleason.H n) :
    recordProfileWithin D ε x y → recordProfileWithin D ε y x := by
  intro h
  calc
    recordProfileL1 D y x = recordProfileL1 D x y := recordProfileL1_symm D y x
    _ ≤ ε := h

theorem recordProfileWithin_trans
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) (ε δ : ℝ)
    (x y z : Gleason.H n) :
    recordProfileWithin D ε x y → recordProfileWithin D δ y z →
      recordProfileWithin D (ε + δ) x z := by
  intro hxy hyz
  exact (recordProfileL1_triangle D x y z).trans (add_le_add hxy hyz)

theorem recordProfileWithin_zero_iff_sameRecord
    {n : ℕ} (D : QuantumFoundations.BornRule.Perspective n) (x y : Gleason.H n) :
    recordProfileWithin D 0 x y ↔
      EverettianProbability.API.ExactFinite.SameRecord D x y := by
  constructor
  · intro h
    apply recordProfileL1_eq_zero_iff_sameRecord D x y |>.mp
    exact le_antisymm h (recordProfileL1_nonneg D x y)
  · intro h
    unfold recordProfileWithin
    rw [(recordProfileL1_eq_zero_iff_sameRecord D x y).mpr h]

end EverettianDecoherence.Metrics

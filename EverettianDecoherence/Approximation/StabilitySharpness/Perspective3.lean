import EverettianDecoherence.Approximation.StabilitySharpness.Rotation3
import QuantumFoundations.BornRule.Perspective

/-!
**FR.** Perspective coordonnée à trois cellules pour la famille de sharpness
de stabilité. Elle est construite à partir de la base orthonormale canonique
de H 3. Les trois cellules sont les droites coordonnées.

**EN.** Three-cell coordinate perspective for the stability-sharpness family.
It is built from the canonical orthonormal basis of H 3. The three cells are
the coordinate lines.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open scoped Classical InnerProductSpace

noncomputable section

noncomputable def stabilitySharpnessBasis3 :
    OrthonormalBasis (Fin 3) ℂ (H 3) :=
  EuclideanSpace.basisFun (Fin 3) ℂ

noncomputable def stabilitySharpnessPerspective3 : Perspective 3 :=
  Perspective.basisPerspective stabilitySharpnessBasis3

noncomputable def stabilitySharpnessCell3 (i : Fin 3) :
    (Projective.interface 3).Cell stabilitySharpnessPerspective3 := by
  refine ⟨ℂ ∙ (stabilitySharpnessBasis3 i : H 3), ?_⟩
  unfold stabilitySharpnessPerspective3
  unfold Perspective.basisPerspective
  simp [stabilitySharpnessBasis3]

theorem stabilitySharpnessCell3_val (i : Fin 3) :
    (stabilitySharpnessCell3 i).val =
      ℂ ∙ (stabilitySharpnessBasis3 i : H 3) := by
  rfl

theorem stabilitySharpnessBasis3_norm (i : Fin 3) :
    ‖(stabilitySharpnessBasis3 i : H 3)‖ = 1 :=
  stabilitySharpnessBasis3.orthonormal.1 i

theorem stabilitySharpnessBasis3_inner_eq_zero
    {i j : Fin 3} (hij : i ≠ j) :
    inner ℂ (stabilitySharpnessBasis3 i : H 3)
      (stabilitySharpnessBasis3 j : H 3) = 0 :=
  stabilitySharpnessBasis3.orthonormal.2 hij

theorem stabilitySharpnessCell3_ne
    {i j : Fin 3} (hij : i ≠ j) :
    stabilitySharpnessCell3 i ≠ stabilitySharpnessCell3 j := by
  intro h
  have hval :
      (ℂ ∙ (stabilitySharpnessBasis3 i : H 3) : Submodule ℂ (H 3)) =
        ℂ ∙ (stabilitySharpnessBasis3 j : H 3) := by
    exact congrArg Subtype.val h
  have hinj :=
    Perspective.line_injective stabilitySharpnessBasis3
      (show i ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) by simp)
      (show j ∈ (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) by simp)
      hval
  exact hij hinj

end
end EverettianDecoherence.Approximation

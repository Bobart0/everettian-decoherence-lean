import QuantumFoundations.BornRule.Perspective

/-!
**FR.** Perspective coordonnée générique sur `H n`. Cette couche factorise
la construction jusque-là spécialisée à trois cellules et sert notamment à la
famille diffuse à `2m` cellules du manuscrit.

**EN.** Generic coordinate perspective on `H n`. This factors the
construction previously specialized to three cells and is used by the
manuscript's diffuse `2m`-cell family.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open scoped Classical InnerProductSpace

noncomputable section

noncomputable def coordinateOrthonormalBasis (n : ℕ) :
    OrthonormalBasis (Fin n) ℂ (H n) :=
  EuclideanSpace.basisFun (Fin n) ℂ

noncomputable def coordinatePerspective (n : ℕ) : Perspective n :=
  basisPerspective (coordinateOrthonormalBasis n)

noncomputable def coordinateCell {n : ℕ} (i : Fin n) :
    (Projective.interface n).Cell (coordinatePerspective n) := by
  refine ⟨ℂ ∙ (coordinateOrthonormalBasis n i : H n), ?_⟩
  unfold coordinatePerspective
  unfold basisPerspective
  simp [coordinateOrthonormalBasis]

theorem coordinateCell_val {n : ℕ} (i : Fin n) :
    (coordinateCell i).val =
      ℂ ∙ (coordinateOrthonormalBasis n i : H n) := by
  rfl

theorem coordinateBasis_norm {n : ℕ} (i : Fin n) :
    ‖(coordinateOrthonormalBasis n i : H n)‖ = 1 :=
  (coordinateOrthonormalBasis n).orthonormal.1 i

theorem coordinateBasis_inner_eq_zero
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    inner ℂ (coordinateOrthonormalBasis n i : H n)
      (coordinateOrthonormalBasis n j : H n) = 0 :=
  (coordinateOrthonormalBasis n).orthonormal.2 hij

theorem coordinateCell_ne
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    coordinateCell i ≠ coordinateCell j := by
  intro h
  have hval :
      (ℂ ∙ (coordinateOrthonormalBasis n i : H n) :
          Submodule ℂ (H n)) =
        ℂ ∙ (coordinateOrthonormalBasis n j : H n) := by
    exact congrArg Subtype.val h
  have hinj :=
    line_injective (coordinateOrthonormalBasis n)
      (show i ∈ (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)) by simp)
      (show j ∈ (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)) by simp)
      hval
  exact hij hinj

end
end EverettianDecoherence.Approximation

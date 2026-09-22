import EverettianDecoherence.Approximation.StabilitySharpness.Rotation3
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


theorem coordinateCell_bijective (n : ℕ) :
    Function.Bijective
      (coordinateCell :
        Fin n →
          (Projective.interface n).Cell (coordinatePerspective n)) := by
  constructor
  · intro i j hij
    by_contra hne
    exact coordinateCell_ne hne hij
  · intro c
    rcases c with ⟨V, hV⟩
    change V ∈ (basisPerspective (coordinateOrthonormalBasis n)).cells at hV
    change
      V ∈
        Finset.univ.image
          (fun i : Fin n =>
            ℂ ∙ (coordinateOrthonormalBasis n i : H n))
      at hV
    obtain ⟨i, _hi, hVi⟩ := Finset.mem_image.mp hV
    refine ⟨i, ?_⟩
    apply Subtype.ext
    rw [coordinateCell_val]
    exact hVi

noncomputable def coordinateCellEquiv (n : ℕ) :
    Fin n ≃
      (Projective.interface n).Cell (coordinatePerspective n) :=
  Equiv.ofBijective coordinateCell (coordinateCell_bijective n)

@[simp]
theorem coordinateCellEquiv_apply {n : ℕ} (i : Fin n) :
    coordinateCellEquiv n i = coordinateCell i := by
  rfl

theorem sum_coordinateCells {n : ℕ}
    (f : (Projective.interface n).Cell (coordinatePerspective n) → ℝ) :
    (∑ c, f c) = ∑ i : Fin n, f (coordinateCell i) := by
  symm
  exact Fintype.sum_equiv (coordinateCellEquiv n)
    (fun i => f (coordinateCell i)) f (fun i => rfl)

end
end EverettianDecoherence.Approximation

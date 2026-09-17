import EverettianDecoherence.Metrics.FiniteProfileTotalVariation
import EverettianDecoherence.Metrics.OrthogonalRecordDecomposition

/-!
**FR.** Géométrie cinématique d'un sous-ensemble fini de cellules d'une
perspective. Le sous-espace agrégé est le supremum des cellules choisies ; sa
projection orthogonale reproduit exactement la somme de leurs poids borniens.
L'utilisation de `bornRecord` rend la dernière identité BORN-SENSITIVE, mais
aucune dynamique ni décohérence n'est introduite.

**EN.** Kinematic geometry of a finite subset of cells of a perspective. The
aggregated subspace is the supremum of the selected cells; its orthogonal
projection reproduces exactly the sum of their Born weights. The final
identity is BORN-SENSITIVE because it uses `bornRecord`, but no dynamics or
decoherence is introduced.
-/

namespace EverettianDecoherence.Metrics

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open scoped BigOperators Classical InnerProductSpace

noncomputable section

/-- Supremum of a finite subset of the cells of a supplied perspective. -/
noncomputable def recordSubsetSubspace
    {n : ℕ} (D : Perspective n)
    (S : Finset ((Projective.interface n).Cell D)) : Submodule ℂ (H n) :=
  S.sup fun c => c.val

/-- Pythagoras for the projector onto the supremum of a subset of perspective
cells. -/
theorem norm_sq_recordSubsetProjector_eq_sum
    {n : ℕ} (D : Perspective n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    ‖Gleason.projL (recordSubsetSubspace D S) x‖ ^ 2 =
      ∑ c ∈ S, ‖Gleason.projL c.val x‖ ^ 2 := by
  have hortho :
      ∀ c ∈ S, ∀ d ∈ S, c ≠ d → c.val ⟂ d.val := by
    intro c hc d hd hcd
    exact D.ortho c.val c.property d.val d.property
      (fun hval => hcd (Subtype.ext hval))
  unfold recordSubsetSubspace
  rw [Gleason.projL_sup_of_pairwise_isOrtho S (fun c => c.val) hortho]
  have happly :
      (∑ c ∈ S, Gleason.projL c.val) x =
        ∑ c ∈ S, Gleason.projL c.val x := by
    simp [LinearMap.sum_apply]
  rw [happly]
  apply QuantumFoundations.BornRule.norm_sq_sum_of_pairwise_orthogonal
  intro c hc d hd hcd
  have hcc : c.val ⟂ d.val := hortho c hc d hd hcd
  have hc_mem : Gleason.projL c.val x ∈ c.val :=
    Submodule.starProjection_apply_mem c.val x
  have hd_mem : Gleason.projL d.val x ∈ d.val :=
    Submodule.starProjection_apply_mem d.val x
  have hc_perp : Gleason.projL c.val x ∈ d.valᗮ := hcc hc_mem
  have hz : ⟪Gleason.projL d.val x, Gleason.projL c.val x⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal d.val (Gleason.projL c.val x)).mp hc_perp
      (Gleason.projL d.val x) hd_mem
  rw [← inner_conj_symm (Gleason.projL c.val x) (Gleason.projL d.val x), hz]
  simp


/-- The projector onto an aggregated subset is the finite sum of its mutually
orthogonal cell projectors. -/
theorem recordSubsetProjector_eq_sum
    {n : ℕ} (D : Perspective n)
    (S : Finset ((Projective.interface n).Cell D)) :
    Gleason.projL (recordSubsetSubspace D S) =
      ∑ c ∈ S, Gleason.projL c.val := by
  have hortho :
      ∀ c ∈ S, ∀ d ∈ S, c ≠ d → c.val ⟂ d.val := by
    intro c hc d hd hcd
    exact D.ortho c.val c.property d.val d.property
      (fun hval => hcd (Subtype.ext hval))
  unfold recordSubsetSubspace
  exact Gleason.projL_sup_of_pairwise_isOrtho S (fun c => c.val) hortho

/-- The projectors of all cells in a perspective sum to the identity. -/
theorem sum_recordCellProjectors_eq_id
    {n : ℕ} (D : Perspective n) :
    (∑ c : (Projective.interface n).Cell D, Gleason.projL c.val) =
      LinearMap.id := by
  have hsubtype :
      (∑ c : (Projective.interface n).Cell D, Gleason.projL c.val) =
        ∑ c ∈ D.cells, Gleason.projL c := by
    symm
    exact Finset.sum_subtype D.cells (fun c => Iff.rfl)
      (fun c => Gleason.projL c)
  rw [hsubtype]
  have h := Gleason.projL_sup_of_pairwise_isOrtho
    D.cells (fun c => c) D.ortho
  have hsup : D.cells.sup (fun c => c) = (⊤ : Submodule ℂ (H n)) := by
    change D.cells.sup id = (⊤ : Submodule ℂ (H n))
    rw [Finset.sup_id_eq_sSup, D.span]
  rw [hsup] at h
  have htop : Gleason.projL (⊤ : Submodule ℂ (H n)) = LinearMap.id := by
    unfold Gleason.projL
    rw [Submodule.starProjection_top]
    rfl
  rw [htop] at h
  exact h.symm

/-- The aggregate projectors of a subset and its finite complement decompose
every vector exactly. -/
theorem recordSubsetProjector_add_compl_apply_eq
    {n : ℕ} (D : Perspective n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    Gleason.projL (recordSubsetSubspace D S) x +
        Gleason.projL (recordSubsetSubspace D Sᶜ) x = x := by
  have hsplit :
      (∑ c ∈ S, Gleason.projL c.val x) +
          (∑ c ∈ Sᶜ, Gleason.projL c.val x) =
        ∑ c : (Projective.interface n).Cell D, Gleason.projL c.val x := by
    exact S.sum_add_sum_compl (fun c => Gleason.projL c.val x)
  have hall := congrArg (fun T : H n →ₗ[ℂ] H n => T x)
    (sum_recordCellProjectors_eq_id D)
  rw [recordSubsetProjector_eq_sum D S,
    recordSubsetProjector_eq_sum D Sᶜ]
  simp only [LinearMap.sum_apply]
  calc
    (∑ c ∈ S, Gleason.projL c.val x) +
        (∑ c ∈ Sᶜ, Gleason.projL c.val x) =
      ∑ c : (Projective.interface n).Cell D, Gleason.projL c.val x := hsplit
    _ = x := by simpa [LinearMap.sum_apply] using hall

/-- The complement aggregate projector is the orthogonal-complement part of
the subset projector. -/
theorem recordSubsetProjector_compl_apply_eq_sub
    {n : ℕ} (D : Perspective n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    Gleason.projL (recordSubsetSubspace D Sᶜ) x =
      x - Gleason.projL (recordSubsetSubspace D S) x := by
  exact eq_sub_of_add_eq' (recordSubsetProjector_add_compl_apply_eq D S x)



/-- Every selected cell lies in the aggregate subspace of the subset. -/
theorem recordCell_le_recordSubsetSubspace
    {n : ℕ} (D : Perspective n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : (Projective.interface n).Cell D) (hc : c ∈ S) :
    c.val ≤ recordSubsetSubspace D S := by
  unfold recordSubsetSubspace
  exact Finset.le_sup hc


/-- The aggregate projector acts as the identity on every selected cell. -/
theorem recordSubsetProjector_cell_apply_eq_self_of_mem
    {n : ℕ} (D : Perspective n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : (Projective.interface n).Cell D) (hc : c ∈ S) (x : H n) :
    Gleason.projL (recordSubsetSubspace D S)
        (Gleason.projL c.val x) = Gleason.projL c.val x := by
  unfold Gleason.projL
  apply Submodule.starProjection_eq_self_iff.mpr
  exact recordCell_le_recordSubsetSubspace D S c hc
    (Submodule.starProjection_apply_mem c.val x)

/-- The complement aggregate projector annihilates every selected cell. -/
theorem recordSubsetComplementProjector_cell_apply_eq_zero_of_mem
    {n : ℕ} (D : Perspective n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : (Projective.interface n).Cell D) (hc : c ∈ S) (x : H n) :
    Gleason.projL (recordSubsetSubspace D Sᶜ)
        (Gleason.projL c.val x) = 0 := by
  rw [recordSubsetProjector_compl_apply_eq_sub D S,
    recordSubsetProjector_cell_apply_eq_self_of_mem D S c hc x,
    sub_self]

/-- Symmetric form: the aggregate projector onto `S` annihilates a cell in
the finite complement. -/
theorem recordSubsetProjector_cell_apply_eq_zero_of_mem_compl
    {n : ℕ} (D : Perspective n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : (Projective.interface n).Cell D) (hc : c ∈ Sᶜ) (x : H n) :
    Gleason.projL (recordSubsetSubspace D S)
        (Gleason.projL c.val x) = 0 := by
  simpa using
    (recordSubsetComplementProjector_cell_apply_eq_zero_of_mem
      D Sᶜ c hc x)


/-- A cell selected in `S` annihilates the aggregate projection onto
`Sᶜ`. -/
theorem recordCellProjector_compl_apply_eq_zero_of_mem
    {n : ℕ} (D : Perspective n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : (Projective.interface n).Cell D) (hc : c ∈ S) (x : H n) :
    Gleason.projL c.val
        (Gleason.projL (recordSubsetSubspace D Sᶜ) x) = 0 := by
  have hle : c.val ≤ recordSubsetSubspace D S :=
    recordCell_le_recordSubsetSubspace D S c hc
  have hcompl :
      Gleason.projL (recordSubsetSubspace D Sᶜ) x =
        x - Gleason.projL (recordSubsetSubspace D S) x :=
    recordSubsetProjector_compl_apply_eq_sub D S x
  have hmemAgg :
      Gleason.projL (recordSubsetSubspace D Sᶜ) x ∈
        (recordSubsetSubspace D S)ᗮ := by
    rw [hcompl]
    unfold Gleason.projL
    exact Submodule.sub_starProjection_mem_orthogonal x
  have hmemCell :
      Gleason.projL (recordSubsetSubspace D Sᶜ) x ∈ c.valᗮ :=
    Submodule.orthogonal_le hle hmemAgg
  change c.val.starProjection
      (Gleason.projL (recordSubsetSubspace D Sᶜ) x) = 0
  exact (Submodule.starProjection_apply_eq_zero_iff (K := c.val)).2 hmemCell

/-- Symmetric form: a cell in the finite complement annihilates the aggregate
projection onto `S`. -/
theorem recordCellProjector_apply_eq_zero_of_mem_compl
    {n : ℕ} (D : Perspective n)
    (S : Finset ((Projective.interface n).Cell D))
    (c : (Projective.interface n).Cell D) (hc : c ∈ Sᶜ) (x : H n) :
    Gleason.projL c.val
        (Gleason.projL (recordSubsetSubspace D S) x) = 0 := by
  simpa using
    (recordCellProjector_compl_apply_eq_zero_of_mem D Sᶜ c hc x)


/-- The sum of Born weights over a finite subset of cells is exactly the
squared norm of the projection onto their aggregated subspace. -/
theorem sum_bornRecord_subset_eq_norm_sq_projector
    {n : ℕ} (D : Perspective n)
    (S : Finset ((Projective.interface n).Cell D)) (x : H n) :
    (∑ c ∈ S, bornRecord D x c) =
      ‖Gleason.projL (recordSubsetSubspace D S) x‖ ^ 2 := by
  change (∑ c ∈ S, ‖Gleason.projL c.val x‖ ^ 2) = _
  exact (norm_sq_recordSubsetProjector_eq_sum D S x).symm

/-- The total Born mass of a supplied perspective is the squared norm of the
state. -/
theorem sum_bornRecord_eq_norm_sq
    {n : ℕ} (D : Perspective n) (x : H n) :
    (∑ c : (Projective.interface n).Cell D, bornRecord D x c) = ‖x‖ ^ 2 := by
  change (∑ c : (Projective.interface n).Cell D,
    (recordCellNormProfile D x c) ^ 2) = ‖x‖ ^ 2
  exact sum_sq_recordCellNormProfile_eq_norm_sq D x


/-- Cells whose Born weight is at least as large in `x` as in `y`. This is
the positive set entering the finite total-variation identity. -/
noncomputable def positiveRecordSubset
    {n : ℕ} (D : Perspective n) (x y : H n) :
    Finset ((Projective.interface n).Cell D) :=
  Finset.univ.filter (fun c => bornRecord D y c ≤ bornRecord D x c)

/-- For equal-norm states, record-profile L1 distance is twice the total Born
mass excess on the cells whose weight increased. -/
theorem recordProfileL1_eq_two_mul_sum_positive_of_norm_eq
    {n : ℕ} (D : Perspective n) (x y : H n) (hxy : ‖x‖ = ‖y‖) :
    recordProfileL1 D x y =
      2 * ∑ c ∈ positiveRecordSubset D x y,
        (bornRecord D x c - bornRecord D y c) := by
  unfold recordProfileL1 positiveRecordSubset recordProfile
  apply finiteProfileL1_eq_two_mul_sum_filter_of_sum_eq
  rw [sum_bornRecord_eq_norm_sq, sum_bornRecord_eq_norm_sq, hxy]

/-- The positive-mass total-variation identity expressed through the orthogonal
projector onto the aggregated increasing cells. -/
theorem recordProfileL1_eq_two_mul_recordSubsetProjector_excess_of_norm_eq
    {n : ℕ} (D : Perspective n) (x y : H n) (hxy : ‖x‖ = ‖y‖) :
    recordProfileL1 D x y =
      2 * (
        ‖Gleason.projL
            (recordSubsetSubspace D (positiveRecordSubset D x y)) x‖ ^ 2 -
        ‖Gleason.projL
            (recordSubsetSubspace D (positiveRecordSubset D x y)) y‖ ^ 2) := by
  rw [recordProfileL1_eq_two_mul_sum_positive_of_norm_eq D x y hxy,
    Finset.sum_sub_distrib,
    sum_bornRecord_subset_eq_norm_sq_projector D (positiveRecordSubset D x y) x,
    sum_bornRecord_subset_eq_norm_sq_projector D (positiveRecordSubset D x y) y]

/-- Unitary specialization: all record-profile variation is exactly twice the
Born-mass gain of one aggregated projector selected by the signs of the
cellwise changes. -/
theorem recordProfileL1_unitary_eq_two_mul_recordSubsetProjector_excess
    {n : ℕ} (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) (x : H n) :
    recordProfileL1 D (U x) x =
      2 * (
        ‖Gleason.projL
            (recordSubsetSubspace D (positiveRecordSubset D (U x) x)) (U x)‖ ^ 2 -
        ‖Gleason.projL
            (recordSubsetSubspace D (positiveRecordSubset D (U x) x)) x‖ ^ 2) := by
  exact recordProfileL1_eq_two_mul_recordSubsetProjector_excess_of_norm_eq
    D (U x) x (U.norm_map x)

end
end EverettianDecoherence.Metrics

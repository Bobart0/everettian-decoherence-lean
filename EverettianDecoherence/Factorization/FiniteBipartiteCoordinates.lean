import EverettianDecoherence.Core.UpstreamAPI

/-!
**FR.** Espace de coordonnées bipartite fini et réindexation isométrique
standard entre `Gleason.H (s * e)` et `EuclideanSpace ℂ (Fin s × Fin e)`.
Aucune factorisation n'est encore associée à un espace ambiant arbitraire ;
seule la dimension `s * e` reçoit un témoin standard. Aucune opération
locale, trace partielle, intrication, dynamique ou décohérence n'est
introduite. Aucun `bornRecord`, `recordProfileL1` ou `SameRecord` n'apparaît.

**EN.** Finite bipartite coordinate space and the standard isometric
reindexing between `Gleason.H (s * e)` and
`EuclideanSpace ℂ (Fin s × Fin e)`. No factorization is yet associated with
an arbitrary ambient space; only dimension `s * e` receives a standard
witness. No local operation, partial trace, entanglement, dynamics, or
decoherence is introduced. No `bornRecord`, `recordProfileL1`, or
`SameRecord` appears.
-/

namespace EverettianDecoherence.Factorization

abbrev FiniteBipartiteCoordinateSpace
    (systemDim environmentDim : ℕ) :=
  EuclideanSpace ℂ (Fin systemDim × Fin environmentDim)

noncomputable def finiteProductIndexEquiv
    (systemDim environmentDim : ℕ) :
    Fin (systemDim * environmentDim)
      ≃
    Fin systemDim × Fin environmentDim :=
  Fintype.equivOfCardEq (by simp [Fintype.card_fin, Fintype.card_prod])

noncomputable def finiteBipartiteCoordinateReindex
    (systemDim environmentDim : ℕ) :
    Gleason.H (systemDim * environmentDim)
      ≃ₗᵢ[ℂ]
    FiniteBipartiteCoordinateSpace
      systemDim environmentDim :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (finiteProductIndexEquiv systemDim environmentDim)

theorem finiteBipartiteCoordinateReindex_apply
    (systemDim environmentDim : ℕ)
    (x : Gleason.H (systemDim * environmentDim))
    (p : Fin systemDim × Fin environmentDim) :
    finiteBipartiteCoordinateReindex systemDim environmentDim x p =
      x ((finiteProductIndexEquiv systemDim environmentDim).symm p) := by
  unfold finiteBipartiteCoordinateReindex
  rw [LinearIsometryEquiv.piLpCongrLeft_apply]
  rfl

end EverettianDecoherence.Factorization

import EverettianDecoherence.Metrics.FiniteConcentration
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
**FR.** Brique analytique générique : en dimension finie, la norme
d'opérateur d'une application linéaire continue sur un espace complexe non
trivial est atteinte sur la sphère unité. Ce fichier ne porte aucune
interprétation quantique ou probabiliste.

**EN.** Generic analytic building block: in finite dimension, the operator
norm of a continuous linear map on a nontrivial complex space is attained on
the unit sphere. This file carries no quantum or probabilistic interpretation.
-/

namespace EverettianDecoherence.Metrics

/-- In a nontrivial finite-dimensional complex normed space, every continuous
linear map attains its operator norm on the unit sphere. -/
theorem exists_unit_norm_apply_eq_opNorm
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [Nontrivial E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : E →L[ℂ] F) :
    ∃ x : E, ‖x‖ = 1 ∧ ‖T x‖ = ‖T‖ := by
  letI : ProperSpace E := FiniteDimensional.proper_rclike ℂ E
  have hcompact : IsCompact (Metric.sphere (0 : E) 1) :=
    isCompact_sphere 0 1
  have hnonempty : (Metric.sphere (0 : E) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨x, hx, hmax⟩ :=
    hcompact.exists_isMaxOn hnonempty T.continuous.norm.continuousOn
  have hxnorm : ‖x‖ = 1 := by
    simpa [Metric.mem_sphere] using hx
  have happ_le : ‖T x‖ ≤ ‖T‖ := by
    simpa [hxnorm] using T.le_opNorm x
  have hop_le : ‖T‖ ≤ ‖T x‖ := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg (T x))
    intro y hy
    exact hmax y (by simpa [Metric.mem_sphere, hy])
  exact ⟨x, hxnorm, le_antisymm happ_le hop_le⟩

end EverettianDecoherence.Metrics

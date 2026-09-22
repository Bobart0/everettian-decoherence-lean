import EverettianDecoherence.Approximation.StabilitySharpness.V12TwoParameterAsymptotics

/-!
**FR.** Rattrapage v18 du manuscrit : couche scalaire du régime à budget
positif fixé. Elle isole la minoration à trois cellules et formalise le fait
élémentaire mais conceptuellement important qu'un défaut relatif tendant vers
zéro à budget strictement positif est automatiquement ultra-near.

**EN.** v18 manuscript catch-up: scalar fixed-positive-budget layer. It
isolates the three-cell lower-slope candidate and formally records that
vanishing relative defect at a strictly positive limiting budget is
automatically ultra-near.
-/

namespace EverettianDecoherence.Approximation

open Filter
open scoped Topology

noncomputable section

/-- Positive-budget value reached by the continuous three-cell family as
x tends to zero with angular parameter d fixed. -/
def v18FixedBudgetBase (d : ℝ) : ℝ :=
  4 * d - 2 * d ^ 2

/-- Three-cell lower-slope candidate at fixed angular parameter d. -/
def v18FixedBudgetLowerSlope (d : ℝ) : ℝ :=
  1 / d

theorem v18FixedBudgetBase_eq_two_mul (d : ℝ) :
    v18FixedBudgetBase d = 2 * d * (2 - d) := by
  unfold v18FixedBudgetBase
  ring

theorem v18FixedBudgetBase_eq_twoParamGlobal_zero (d : ℝ) :
    v18FixedBudgetBase d = v12TwoParamGlobal d 0 := by
  unfold v18FixedBudgetBase v12TwoParamGlobal
  ring

/-- Exact scaled lower-slope identity used in the fixed-budget discussion:
A0(d) * (1/d) = 4 - 2d. -/
theorem v18FixedBudgetBase_mul_lowerSlope
    (d : ℝ) (hd : d ≠ 0) :
    v18FixedBudgetBase d * v18FixedBudgetLowerSlope d =
      4 - 2 * d := by
  unfold v18FixedBudgetBase v18FixedBudgetLowerSlope
  field_simp [hd]
  ring

/-- The three-cell fixed-budget lower slope has the sharp small-budget scaled
limit 4. -/
theorem v18FixedBudgetScaledLower_tendsto_four
    {α : Type*} {l : Filter α}
    (d : α → ℝ)
    (hd : Tendsto d l (𝓝 0))
    (hdne : ∀ k, d k ≠ 0) :
    Tendsto
      (fun k =>
        v18FixedBudgetBase (d k) *
          v18FixedBudgetLowerSlope (d k))
      l (𝓝 4) := by
  have hfun :
      (fun k =>
        v18FixedBudgetBase (d k) *
          v18FixedBudgetLowerSlope (d k)) =
      (fun k => 4 - 2 * d k) := by
    funext k
    exact v18FixedBudgetBase_mul_lowerSlope (d k) (hdne k)
  have htwo :
      Tendsto (fun _ : α => (2 : ℝ)) l (𝓝 2) :=
    tendsto_const_nhds
  have hfour :
      Tendsto (fun _ : α => (4 : ℝ)) l (𝓝 4) :=
    tendsto_const_nhds
  have h := hfour.sub (htwo.mul hd)
  rw [hfun]
  simpa using h

/-- Formal 4-versus-8 clarification: if the global budget converges to a
nonzero value while the relative saturation deficit vanishes, then eta/A
tends to zero, so the sequence is automatically ultra-near. -/
theorem fixedPositiveBudget_forces_ultraNear
    {α : Type*} {l : Filter α}
    (A eta : α → ℝ) (A0 : ℝ)
    (hA : Tendsto A l (𝓝 A0))
    (hA0 : A0 ≠ 0)
    (heta : Tendsto eta l (𝓝 0)) :
    Tendsto (fun k => eta k / A k) l (𝓝 0) := by
  have h := heta.div hA hA0
  simpa using h

end
end EverettianDecoherence.Approximation

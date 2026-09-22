import EverettianDecoherence.Approximation.V12UltraNearFour
import EverettianDecoherence.Approximation.StabilitySharpness.FixedBudgetSlope

/-!
**FR.** Rattrapage de l'argument diagonal de la Proposition 7.3 du manuscrit.
On isole d'abord un lemme scalaire : si A0 -> 0, A/A0 -> 1 et eta/A0 -> 0,
alors A -> 0, eta -> 0 et eta/A -> 0. On réinjecte ensuite ces trois limites
dans le théorème ultra-near déjà formalisé.

**EN.** Catch-up for the diagonal argument in manuscript Proposition 7.3.
First, a scalar lemma shows that A0 -> 0, A/A0 -> 1 and eta/A0 -> 0 imply
A -> 0, eta -> 0 and eta/A -> 0. These limits are then fed into the already
formalized ultra-near coefficient-4 theorem.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open Filter
open scoped BigOperators Classical Topology

noncomputable section

theorem fixedBudgetDiagonal_budget_tendsto_zero
    {α : Type*} {l : Filter α}
    (A0 A : α → ℝ)
    (hA0 : Tendsto A0 l (𝓝 0))
    (hA0ne : ∀ k, A0 k ≠ 0)
    (hAover :
      Tendsto (fun k => A k / A0 k) l (𝓝 1)) :
    Tendsto A l (𝓝 0) := by
  have hprod :
      Tendsto (fun k => (A k / A0 k) * A0 k) l (𝓝 0) := by
    simpa using hAover.mul hA0
  convert hprod using 1
  funext k
  field_simp [hA0ne k]

theorem fixedBudgetDiagonal_eta_tendsto_zero
    {α : Type*} {l : Filter α}
    (A0 eta : α → ℝ)
    (hA0 : Tendsto A0 l (𝓝 0))
    (hA0ne : ∀ k, A0 k ≠ 0)
    (hetaOver :
      Tendsto (fun k => eta k / A0 k) l (𝓝 0)) :
    Tendsto eta l (𝓝 0) := by
  have hprod :
      Tendsto (fun k => (eta k / A0 k) * A0 k) l (𝓝 0) := by
    simpa using hetaOver.mul hA0
  convert hprod using 1
  funext k
  field_simp [hA0ne k]

theorem fixedBudgetDiagonal_forces_ultraNear
    {α : Type*} {l : Filter α}
    (A0 A eta : α → ℝ)
    (hA0 : Tendsto A0 l (𝓝 0))
    (hA0ne : ∀ k, A0 k ≠ 0)
    (hAne : ∀ k, A k ≠ 0)
    (hAover :
      Tendsto (fun k => A k / A0 k) l (𝓝 1))
    (hetaOver :
      Tendsto (fun k => eta k / A0 k) l (𝓝 0)) :
    Tendsto (fun k => eta k / A k) l (𝓝 0) := by
  have hdiv :=
    hetaOver.div hAover (by norm_num : (1 : ℝ) ≠ 0)
  have hfun :
      (fun k => eta k / A k) =
        (fun k => eta k / A0 k) / (fun k => A k / A0 k) := by
    funext k
    change eta k / A k =
      (eta k / A0 k) / (A k / A0 k)
    field_simp [hA0ne k, hAne k]
  rw [hfun]
  simpa using hdiv

/-- Sequence-level form of the diagonal upper-bound mechanism behind the
fixed-budget local-slope asymptotic.  It deliberately avoids packaging the
order-theoretic supremum C_fix: once a selected sequence has
A/A0 -> 1 and eta/A0 -> 0 with A0 -> 0, the existing ultra-near theorem
supplies every coefficient c > 4. -/
theorem eventually_two_cell_tail_le_of_fixedBudgetDiagonal
    (dim : ℕ → ℕ)
    (D : (k : ℕ) → Perspective (dim k))
    (U : (k : ℕ) → H (dim k) ≃ₗᵢ[ℂ] H (dim k))
    (A0 eta : ℕ → ℝ)
    (hdelta :
      ∀ k, 0 < operatorNormProjectorCommutatorL2 (D k) (U k))
    (hetaPos : ∀ k, 0 < eta k)
    (hexact : ∀ k,
      maxCutEnvelopeDefect (D k) (U k) =
        eta k * operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2)
    (hA0 : Tendsto A0 atTop (𝓝 0))
    (hA0ne : ∀ k, A0 k ≠ 0)
    (hAover :
      Tendsto
        (fun k =>
          operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2 / A0 k)
        atTop (𝓝 1))
    (hetaOver :
      Tendsto (fun k => eta k / A0 k) atTop (𝓝 0))
    (c : ℝ) (hc : 4 < c) :
    ∀ᶠ k in atTop,
      ∃ i j : (Projective.interface (dim k)).Cell (D k),
        i ≠ j ∧
        operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2 -
            cellCommutatorOpNormSq (D k) (U k) i -
            cellCommutatorOpNormSq (D k) (U k) j ≤
          c * eta k := by
  let A : ℕ → ℝ := fun k =>
    operatorNormProjectorCommutatorL2 (D k) (U k) ^ 2
  have hAne : ∀ k, A k ≠ 0 := by
    intro k
    dsimp [A]
    exact ne_of_gt (sq_pos_of_pos (hdelta k))
  have hA :
      Tendsto A atTop (𝓝 0) :=
    fixedBudgetDiagonal_budget_tendsto_zero
      A0 A hA0 hA0ne (by simpa [A] using hAover)
  have heta :
      Tendsto eta atTop (𝓝 0) :=
    fixedBudgetDiagonal_eta_tendsto_zero
      A0 eta hA0 hA0ne hetaOver
  have hultra :
      Tendsto (fun k => eta k / A k) atTop (𝓝 0) :=
    fixedBudgetDiagonal_forces_ultraNear
      A0 A eta hA0 hA0ne hAne
      (by simpa [A] using hAover) hetaOver
  exact eventually_two_cell_tail_le_of_ultra_near
    dim D U eta hdelta hetaPos hexact
    (by simpa [A] using hA) heta
    (by simpa [A] using hultra) c hc

end
end EverettianDecoherence.Approximation

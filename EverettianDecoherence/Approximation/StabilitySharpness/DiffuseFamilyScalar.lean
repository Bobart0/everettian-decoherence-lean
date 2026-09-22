import EverettianDecoherence.Approximation.StabilitySharpness.V12TwoParameterAsymptotics

/-!
**FR.** Couche scalaire de la famille diffuse à 2m cellules introduite dans
la v16--v18 du manuscrit. Cette étape formalise les identités exactes de
budget, défaut, queue et ratio sharp, sans encore construire l'unitaire
2m-dimensionnel.

**EN.** Scalar layer of the diffuse 2m-cell family introduced in manuscript
v16--v18. This step checks the exact budget, defect, tail, and sharp-ratio
identities; the geometric 2m-dimensional unitary realization is a separate
front.
-/

namespace EverettianDecoherence.Approximation

open Filter
open scoped Topology

noncomputable section

def v18DiffuseCellBudget (m : ℕ) (d : ℝ) : ℝ :=
  2 * d / (m : ℝ) - d ^ 2 / (m : ℝ) ^ 2

def v18DiffuseGlobal (m : ℕ) (d : ℝ) : ℝ :=
  2 * (m : ℝ) * v18DiffuseCellBudget m d

def v18DiffuseMaxCutSq (d : ℝ) : ℝ :=
  2 * d - d ^ 2

def v18DiffuseEnvelopeDefect (m : ℕ) (d : ℝ) : ℝ :=
  v18DiffuseGlobal m d - 2 * v18DiffuseMaxCutSq d

def v18DiffuseTau (m : ℕ) : ℝ :=
  1 - 1 / (m : ℝ)

theorem v18DiffuseGlobal_exact
    (m : ℕ) (hm : m ≠ 0) (d : ℝ) :
    v18DiffuseGlobal m d =
      4 * d - 2 * d ^ 2 / (m : ℝ) := by
  unfold v18DiffuseGlobal v18DiffuseCellBudget
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  field_simp [hmR]
  ring

theorem v18DiffuseEnvelopeDefect_exact
    (m : ℕ) (hm : m ≠ 0) (d : ℝ) :
    v18DiffuseEnvelopeDefect m d =
      2 * d ^ 2 * (1 - 1 / (m : ℝ)) := by
  unfold v18DiffuseEnvelopeDefect v18DiffuseMaxCutSq
  rw [v18DiffuseGlobal_exact m hm d]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  field_simp [hmR]
  ring

/-- Algebraic form of the manuscript's exact diffuse sharp ratio
A^2 tau / E = 8 (1 - d/(2m))^2. -/
theorem v18Diffuse_scaledRatio_exact
    (m : ℕ) (hm2 : 2 ≤ m) (d : ℝ) (hd : d ≠ 0) :
    v18DiffuseGlobal m d ^ 2 * v18DiffuseTau m /
        v18DiffuseEnvelopeDefect m d =
      8 * (1 - d / (2 * (m : ℝ))) ^ 2 := by
  have hm : m ≠ 0 := by omega
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hm1 : (m : ℝ) - 1 ≠ 0 := by
    have hlt : (1 : ℝ) < (m : ℝ) := by
      exact_mod_cast (show 1 < m by omega)
    linarith
  rw [v18DiffuseGlobal_exact m hm d]
  rw [v18DiffuseEnvelopeDefect_exact m hm d]
  unfold v18DiffuseTau
  field_simp [hmR, hm1, hd]
  ring

/-- For fixed m >= 2, the exact diffuse scaled ratio tends to 8 as d -> 0. -/
theorem v18Diffuse_scaledRatio_tendsto_eight
    {α : Type*} {l : Filter α}
    (m : ℕ) (hm2 : 2 ≤ m)
    (d : α → ℝ)
    (hd : Tendsto d l (𝓝 0))
    (hdne : ∀ k, d k ≠ 0) :
    Tendsto
      (fun k =>
        v18DiffuseGlobal m (d k) ^ 2 * v18DiffuseTau m /
          v18DiffuseEnvelopeDefect m (d k))
      l (𝓝 8) := by
  have hm : m ≠ 0 := by omega
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hfrac :
      Tendsto (fun k => d k / (2 * (m : ℝ))) l (𝓝 0) := by
    simpa using hd.div_const (2 * (m : ℝ))
  have hone :
      Tendsto (fun _ : α => (1 : ℝ)) l (𝓝 1) :=
    tendsto_const_nhds
  have hinner :
      Tendsto (fun k => 1 - d k / (2 * (m : ℝ))) l (𝓝 1) := by
    simpa using hone.sub hfrac
  have hsq :
      Tendsto
        (fun k => (1 - d k / (2 * (m : ℝ))) ^ 2)
        l (𝓝 1) := by
    have h := hinner.mul hinner
    simpa [pow_two] using h
  have height :
      Tendsto
        (fun k => 8 * (1 - d k / (2 * (m : ℝ))) ^ 2)
        l (𝓝 8) := by
    have hc :
        Tendsto (fun _ : α => (8 : ℝ)) l (𝓝 8) :=
      tendsto_const_nhds
    have h := hc.mul hsq
    norm_num at h
    exact h
  have hfun :
      (fun k =>
        v18DiffuseGlobal m (d k) ^ 2 * v18DiffuseTau m /
          v18DiffuseEnvelopeDefect m (d k)) =
      (fun k => 8 * (1 - d k / (2 * (m : ℝ))) ^ 2) := by
    funext k
    exact v18Diffuse_scaledRatio_exact m hm2 (d k) (hdne k)
  rw [hfun]
  exact height

end
end EverettianDecoherence.Approximation

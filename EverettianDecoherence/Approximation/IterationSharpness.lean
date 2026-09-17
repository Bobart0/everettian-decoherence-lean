import Mathlib.Analysis.SpecificLimits.Basic
import EverettianDecoherence.Approximation.IterationSharpness.ElementaryDefect
import EverettianDecoherence.Approximation.IteratedProjectorCommutator

/-!
**FR.** # Sharpness de l'accumulation additive ED4B

Ce module ferme T3 par une famille explicite de deux transformations identiques.
Pour la rotation rationnelle `Uₙ`, le défaut élémentaire L2 vaut `sqrt 2 * sₙ`.
Le composé `Uₙ ∘ Uₙ` possède un défaut exact `sqrt 2 * (2 cₙ sₙ)`, tandis que
la somme ED4B des deux défauts élémentaires vaut `2 * sqrt 2 * sₙ`. Leur ratio
est donc exactement `cₙ`, et `cₙ → 1`. Ainsi le coefficient `1` devant la somme
dans la borne additive ED4B ne peut être remplacé uniformément par une constante
strictement plus petite, même pour des listes de longueur deux.

Cette couche est **NON BORN-SENSITIVE** : elle n'utilise ni `bornRecord` ni poids
de branche. Elle reste algébrique, finie et à perspective fixe ; aucune notion
de temps, de dynamique physique ou de décohérence n'est introduite.

**EN.** # Sharpness of the ED4B additive accumulation bound

This module closes T3 with an explicit family of two identical transformations.
For the rational rotation `Uₙ`, the elementary L2 defect is `sqrt 2 * sₙ`.
The composite `Uₙ ∘ Uₙ` has exact defect `sqrt 2 * (2 cₙ sₙ)`, while the ED4B
sum of the two elementary defects is `2 * sqrt 2 * sₙ`. Their ratio is therefore
exactly `cₙ`, and `cₙ → 1`. Hence the coefficient `1` in front of the additive
ED4B sum cannot be uniformly replaced by any strictly smaller constant, already
for lists of length two.

This layer is **NON BORN-SENSITIVE**: it uses neither `bornRecord` nor branch
weights. It remains algebraic, finite, and at fixed perspective; no notion of
time, physical dynamics, or decoherence is introduced.
-/

namespace EverettianDecoherence.Approximation

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Abstract
open EverettianDecoherence.Metrics
open Filter
open scoped BigOperators Classical InnerProductSpace Topology

noncomputable section

/-- The explicit length-two list used to witness additive sharpness. -/
def iterationSharpnessTwoStepList (n : ℕ) :
    List (H 2 ≃ₗᵢ[ℂ] H 2) :=
  [iterationSharpnessRotation n, iterationSharpnessRotation n]

/-- The corresponding two-step composite. -/
noncomputable def iterationSharpnessTwoStep (n : ℕ) : H 2 ≃ₗᵢ[ℂ] H 2 :=
  iteratedLinearIsometryEquivComp (iterationSharpnessTwoStepList n)

/-- First coordinate of the two-step composite. -/
@[simp] theorem iterationSharpnessTwoStep_zero (n : ℕ) (x : H 2) :
    iterationSharpnessTwoStep n x (0 : Fin 2) =
      ((iterationSharpnessC n : ℂ) ^ 2 - (iterationSharpnessS n : ℂ) ^ 2) *
          x (0 : Fin 2) -
        (2 * (iterationSharpnessC n : ℂ) * (iterationSharpnessS n : ℂ)) *
          x (1 : Fin 2) := by
  unfold iterationSharpnessTwoStep iterationSharpnessTwoStepList
  rw [iteratedLinearIsometryEquivComp_cons_apply,
    iteratedLinearIsometryEquivComp_singleton_apply,
    iterationSharpnessRotation_zero,
    iterationSharpnessRotation_zero,
    iterationSharpnessRotation_one]
  ring

/-- Second coordinate of the two-step composite. -/
@[simp] theorem iterationSharpnessTwoStep_one (n : ℕ) (x : H 2) :
    iterationSharpnessTwoStep n x (1 : Fin 2) =
      (2 * (iterationSharpnessC n : ℂ) * (iterationSharpnessS n : ℂ)) *
          x (0 : Fin 2) +
        ((iterationSharpnessC n : ℂ) ^ 2 - (iterationSharpnessS n : ℂ) ^ 2) *
          x (1 : Fin 2) := by
  unfold iterationSharpnessTwoStep iterationSharpnessTwoStepList
  rw [iteratedLinearIsometryEquivComp_cons_apply,
    iteratedLinearIsometryEquivComp_singleton_apply,
    iterationSharpnessRotation_one,
    iterationSharpnessRotation_zero,
    iterationSharpnessRotation_one]
  ring

/-- Off-diagonal parameter of the two-step rotation. It may vanish at the
first family member and is nonnegative for every `n`. -/
def iterationSharpnessTwoStepS (n : ℕ) : ℝ :=
  2 * iterationSharpnessC n * iterationSharpnessS n

theorem iterationSharpnessTwoStepS_nonneg (n : ℕ) :
    0 ≤ iterationSharpnessTwoStepS n := by
  unfold iterationSharpnessTwoStepS
  exact mul_nonneg
    (mul_nonneg (by norm_num) (iterationSharpnessC_nonneg n))
    (le_of_lt (iterationSharpnessS_pos n))

private theorem iterationSharpnessTwoStepLineCommutator_zero (n : ℕ) (x : H 2) :
    (perspectiveProjectorCommutatorCLM sharpnessPerspective
      (iterationSharpnessTwoStep n) iterationSharpnessLineCell x) (0 : Fin 2) =
      -(iterationSharpnessTwoStepS n : ℂ) * x (1 : Fin 2) := by
  rw [perspectiveProjectorCommutatorCLM_apply, perspectiveProjectorCommutator_apply]
  change
    (projL sharpnessLine (iterationSharpnessTwoStep n x) -
      iterationSharpnessTwoStep n (projL sharpnessLine x)) (0 : Fin 2) = _
  rw [iterationSharpnessLine_proj, iterationSharpnessLine_proj]
  simp [iterationSharpnessTwoStepS, iterationSharpnessTwoStep_zero, sharpnessE0]
  ring

private theorem iterationSharpnessTwoStepLineCommutator_one (n : ℕ) (x : H 2) :
    (perspectiveProjectorCommutatorCLM sharpnessPerspective
      (iterationSharpnessTwoStep n) iterationSharpnessLineCell x) (1 : Fin 2) =
      -(iterationSharpnessTwoStepS n : ℂ) * x (0 : Fin 2) := by
  rw [perspectiveProjectorCommutatorCLM_apply, perspectiveProjectorCommutator_apply]
  change
    (projL sharpnessLine (iterationSharpnessTwoStep n x) -
      iterationSharpnessTwoStep n (projL sharpnessLine x)) (1 : Fin 2) = _
  rw [iterationSharpnessLine_proj, iterationSharpnessLine_proj]
  simp [iterationSharpnessTwoStepS, iterationSharpnessTwoStep_one, sharpnessE0]
  ring

private theorem iterationSharpnessTwoStepLineCommutator_norm (n : ℕ) (x : H 2) :
    ‖perspectiveProjectorCommutatorCLM sharpnessPerspective
      (iterationSharpnessTwoStep n) iterationSharpnessLineCell x‖ =
      iterationSharpnessTwoStepS n * ‖x‖ := by
  have hs : 0 ≤ iterationSharpnessTwoStepS n :=
    iterationSharpnessTwoStepS_nonneg n
  have hsq :
      ‖perspectiveProjectorCommutatorCLM sharpnessPerspective
        (iterationSharpnessTwoStep n) iterationSharpnessLineCell x‖ ^ 2 =
        (iterationSharpnessTwoStepS n * ‖x‖) ^ 2 := by
    calc
      ‖perspectiveProjectorCommutatorCLM sharpnessPerspective
          (iterationSharpnessTwoStep n) iterationSharpnessLineCell x‖ ^ 2 =
          ‖(perspectiveProjectorCommutatorCLM sharpnessPerspective
              (iterationSharpnessTwoStep n) iterationSharpnessLineCell x) (0 : Fin 2)‖ ^ 2 +
            ‖(perspectiveProjectorCommutatorCLM sharpnessPerspective
              (iterationSharpnessTwoStep n) iterationSharpnessLineCell x) (1 : Fin 2)‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      _ = iterationSharpnessTwoStepS n ^ 2 *
          (‖x (0 : Fin 2)‖ ^ 2 + ‖x (1 : Fin 2)‖ ^ 2) := by
        rw [iterationSharpnessTwoStepLineCommutator_zero,
          iterationSharpnessTwoStepLineCommutator_one]
        simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
        ring
      _ = iterationSharpnessTwoStepS n ^ 2 * ‖x‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      _ = (iterationSharpnessTwoStepS n * ‖x‖) ^ 2 := by ring
  nlinarith [norm_nonneg
    (perspectiveProjectorCommutatorCLM sharpnessPerspective
      (iterationSharpnessTwoStep n) iterationSharpnessLineCell x),
    norm_nonneg x, mul_nonneg hs (norm_nonneg x)]

private theorem iterationSharpnessTwoStepLineCommutator_opNorm (n : ℕ) :
    ‖perspectiveProjectorCommutatorCLM sharpnessPerspective
      (iterationSharpnessTwoStep n) iterationSharpnessLineCell‖ =
      iterationSharpnessTwoStepS n := by
  have hs : 0 ≤ iterationSharpnessTwoStepS n :=
    iterationSharpnessTwoStepS_nonneg n
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ hs
      (fun x => by rw [iterationSharpnessTwoStepLineCommutator_norm])
  · have h := ContinuousLinearMap.le_opNorm
      (perspectiveProjectorCommutatorCLM sharpnessPerspective
        (iterationSharpnessTwoStep n) iterationSharpnessLineCell) sharpnessE0
    rw [iterationSharpnessTwoStepLineCommutator_norm,
      sharpnessE0_norm, mul_one, mul_one] at h
    exact h

private theorem iterationSharpnessTwoStepOrthogonalCommutator_eq_neg (n : ℕ) :
    perspectiveProjectorCommutatorCLM sharpnessPerspective
      (iterationSharpnessTwoStep n) iterationSharpnessOrthogonalCell =
      - perspectiveProjectorCommutatorCLM sharpnessPerspective
        (iterationSharpnessTwoStep n) iterationSharpnessLineCell := by
  apply ContinuousLinearMap.ext
  intro x
  change
    perspectiveProjectorCommutator sharpnessPerspective
      (iterationSharpnessTwoStep n) iterationSharpnessOrthogonalCell x =
      -(perspectiveProjectorCommutator sharpnessPerspective
        (iterationSharpnessTwoStep n) iterationSharpnessLineCell x)
  rw [perspectiveProjectorCommutator_apply,
    perspectiveProjectorCommutator_apply]
  change
    projL sharpnessLineᗮ (iterationSharpnessTwoStep n x) -
      iterationSharpnessTwoStep n (projL sharpnessLineᗮ x) =
      -(projL sharpnessLine (iterationSharpnessTwoStep n x) -
        iterationSharpnessTwoStep n (projL sharpnessLine x))
  rw [iterationSharpnessOrthogonal_proj_sub,
    iterationSharpnessOrthogonal_proj_sub, map_sub]
  abel

private theorem iterationSharpnessTwoStepOrthogonalCommutator_opNorm (n : ℕ) :
    ‖perspectiveProjectorCommutatorCLM sharpnessPerspective
      (iterationSharpnessTwoStep n) iterationSharpnessOrthogonalCell‖ =
      iterationSharpnessTwoStepS n := by
  rw [iterationSharpnessTwoStepOrthogonalCommutator_eq_neg, norm_neg,
    iterationSharpnessTwoStepLineCommutator_opNorm]

private theorem iterationSharpnessLine_ne_orthogonal_twoStep :
    sharpnessLine ≠ sharpnessLineᗮ := by
  intro h
  apply sharpnessLine_ne_bot
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hx' : x ∈ sharpnessLineᗮ := h ▸ hx
  rw [Submodule.mem_orthogonal] at hx'
  exact inner_self_eq_zero.mp (hx' x hx)

private theorem iterationSharpnessPerspective_cell_card_twoStep :
    Fintype.card
      ((EverettianProbability.Abstract.Projective.interface 2).Cell sharpnessPerspective) = 2 := by
  change Fintype.card ↥sharpnessPerspective.cells = 2
  rw [Fintype.card_coe]
  change ({sharpnessLine, sharpnessLineᗮ} : Finset (Submodule ℂ (H 2))).card = 2
  simp [iterationSharpnessLine_ne_orthogonal_twoStep]

private theorem iterationSharpnessTwoStepCommutatorOpNormProfile_eq (n : ℕ)
    (c : (EverettianProbability.Abstract.Projective.interface 2).Cell sharpnessPerspective) :
    perspectiveProjectorCommutatorOpNormProfile sharpnessPerspective
      (iterationSharpnessTwoStep n) c = iterationSharpnessTwoStepS n := by
  have hc0 : c.val ∈ sharpnessPerspective.cells := c.property
  change c.val ∈ ({sharpnessLine, sharpnessLineᗮ} :
    Finset (Submodule ℂ (H 2))) at hc0
  have hc : c.val = sharpnessLine ∨ c.val = sharpnessLineᗮ := by
    rcases Finset.mem_insert.mp hc0 with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.mp h)
  rcases hc with hc | hc
  · have hcell : c = iterationSharpnessLineCell := Subtype.ext hc
    subst c
    exact iterationSharpnessTwoStepLineCommutator_opNorm n
  · have hcell : c = iterationSharpnessOrthogonalCell := Subtype.ext hc
    subst c
    exact iterationSharpnessTwoStepOrthogonalCommutator_opNorm n

/-- Exact ED4B defect of the length-two composite. -/
theorem operatorNormProjectorCommutatorL2_iterationSharpnessTwoStep (n : ℕ) :
    operatorNormProjectorCommutatorL2 sharpnessPerspective
      (iterationSharpnessTwoStep n) =
      Real.sqrt 2 * iterationSharpnessTwoStepS n := by
  unfold operatorNormProjectorCommutatorL2
  have hp :
      perspectiveProjectorCommutatorOpNormProfile sharpnessPerspective
        (iterationSharpnessTwoStep n) =
        fun _ => iterationSharpnessTwoStepS n := by
    funext c
    exact iterationSharpnessTwoStepCommutatorOpNormProfile_eq n c
  rw [hp]
  unfold EverettianDecoherence.Metrics.finiteL2
    EverettianDecoherence.Metrics.finiteL2Sq
  rw [Finset.sum_const, Finset.card_univ,
    iterationSharpnessPerspective_cell_card_twoStep]
  norm_num
  rw [Real.sqrt_sq (iterationSharpnessTwoStepS_nonneg n)]

/-- Exact sum of the two elementary ED4B defects. -/
theorem operatorNormProjectorCommutatorSum_iterationSharpnessTwoStep (n : ℕ) :
    operatorNormProjectorCommutatorSum sharpnessPerspective
      (iterationSharpnessTwoStepList n) =
      2 * (Real.sqrt 2 * iterationSharpnessS n) := by
  unfold iterationSharpnessTwoStepList
  rw [operatorNormProjectorCommutatorSum_cons,
    operatorNormProjectorCommutatorSum_cons,
    operatorNormProjectorCommutatorSum_nil,
    operatorNormProjectorCommutatorL2_iterationSharpnessRotation]
  ring

/-- The ED4B denominator for the two-step family is strictly positive. -/
theorem operatorNormProjectorCommutatorSum_iterationSharpnessTwoStep_pos (n : ℕ) :
    0 < operatorNormProjectorCommutatorSum sharpnessPerspective
      (iterationSharpnessTwoStepList n) := by
  rw [operatorNormProjectorCommutatorSum_iterationSharpnessTwoStep]
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs : 0 < iterationSharpnessS n := iterationSharpnessS_pos n
  positivity

/-- Ratio between the exact composite defect and the ED4B additive sum. -/
noncomputable def iterationSharpnessAdditiveRatio (n : ℕ) : ℝ :=
  operatorNormProjectorCommutatorL2 sharpnessPerspective
      (iterationSharpnessTwoStep n) /
    operatorNormProjectorCommutatorSum sharpnessPerspective
      (iterationSharpnessTwoStepList n)

/-- Exact closed form of the additive-sharpness ratio. -/
theorem iterationSharpnessAdditiveRatio_eq_C (n : ℕ) :
    iterationSharpnessAdditiveRatio n = iterationSharpnessC n := by
  unfold iterationSharpnessAdditiveRatio
  rw [operatorNormProjectorCommutatorL2_iterationSharpnessTwoStep,
    operatorNormProjectorCommutatorSum_iterationSharpnessTwoStep]
  unfold iterationSharpnessTwoStepS
  have hsqrt : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs : iterationSharpnessS n ≠ 0 := ne_of_gt (iterationSharpnessS_pos n)
  field_simp [hsqrt, hs]

/-- Rational form of the cosine-like parameter. -/
theorem iterationSharpnessC_eq_one_sub_two_div (n : ℕ) :
    iterationSharpnessC n =
      1 - 2 / ((sharpnessP n : ℝ) ^ 2 + 1) := by
  have hq : (sharpnessQ n : ℝ) ≠ 0 := ne_of_gt (sharpnessQ_real_pos n)
  have hpden : (sharpnessP n : ℝ) ^ 2 + 1 ≠ 0 := by positivity
  have hpell :
      (sharpnessP n : ℝ) ^ 2 + 1 = 2 * (sharpnessQ n : ℝ) ^ 2 := by
    exact_mod_cast sharpnessP_sq_add_one_eq_two_mul_Q_sq n
  unfold iterationSharpnessC sharpnessA sharpnessB
  field_simp [hq, hpden]
  nlinarith [hpell]

private theorem iterationSharpnessCDenominator_tendsto_atTop :
    Filter.Tendsto (fun n : ℕ => (sharpnessP n : ℝ) ^ 2 + 1)
      Filter.atTop Filter.atTop := by
  have hsquare :
      Filter.Tendsto (fun x : ℝ => x ^ 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_pow_atTop (by norm_num)
  exact tendsto_atTop_add_const_right _ _ (hsquare.comp sharpnessP_tendsto_atTop)

private theorem iterationSharpnessCDefect_tendsto_zero :
    Filter.Tendsto
      (fun n : ℕ => 2 / ((sharpnessP n : ℝ) ^ 2 + 1))
      Filter.atTop (𝓝 0) := by
  simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using
    (tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero.comp iterationSharpnessCDenominator_tendsto_atTop))

/-- The ratio parameter tends to one along the explicit Pell family. -/
theorem iterationSharpnessC_tendsto_one :
    Filter.Tendsto iterationSharpnessC Filter.atTop (𝓝 1) := by
  have hconst :
      Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (𝓝 1) :=
    tendsto_const_nhds
  have h := hconst.sub iterationSharpnessCDefect_tendsto_zero
  have hfun : iterationSharpnessC =
      fun n : ℕ => 1 - 2 / ((sharpnessP n : ℝ) ^ 2 + 1) := by
    funext n
    exact iterationSharpnessC_eq_one_sub_two_div n
  rw [hfun]
  exact h

/-- Main T3 sharpness theorem: the exact composite-to-sum ratio tends to `1`. -/
theorem iterationSharpnessAdditiveRatio_tendsto_one :
    Filter.Tendsto iterationSharpnessAdditiveRatio Filter.atTop (𝓝 1) := by
  have hfun : iterationSharpnessAdditiveRatio = iterationSharpnessC := by
    funext n
    exact iterationSharpnessAdditiveRatio_eq_C n
  rw [hfun]
  exact iterationSharpnessC_tendsto_one

/-- Operational sharpness statement: every proposed uniform coefficient below
`1` is violated by some explicit two-step rational rotation. -/
theorem exists_twoStep_defect_gt_const_mul_sum_of_lt_one
    {K : ℝ} (hK : K < 1) :
    ∃ n : ℕ,
      K * operatorNormProjectorCommutatorSum sharpnessPerspective
          (iterationSharpnessTwoStepList n) <
        operatorNormProjectorCommutatorL2 sharpnessPerspective
          (iterationSharpnessTwoStep n) := by
  have hev : ∀ᶠ n in Filter.atTop, K < iterationSharpnessAdditiveRatio n :=
    iterationSharpnessAdditiveRatio_tendsto_one.eventually
      (eventually_gt_nhds hK)
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨n, ?_⟩
  unfold iterationSharpnessAdditiveRatio at hn
  exact (lt_div_iff₀
    (operatorNormProjectorCommutatorSum_iterationSharpnessTwoStep_pos n)).mp hn

end
end EverettianDecoherence.Approximation

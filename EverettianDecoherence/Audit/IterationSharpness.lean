import EverettianDecoherence.Approximation.IterationSharpness

/-!
**FR.** Audit T3 de la sharpness de l'accumulation additive ED4B. Cette
surface est **NON BORN-SENSITIVE** : elle ne dépend ni de `bornRecord` ni de
poids de branche. L'audit vérifie la famille explicite de deux rotations
rationnelles identiques, le défaut exact du composé, la somme exacte des deux
défauts élémentaires, l'identité du ratio avec `iterationSharpnessC`, sa
convergence vers `1`, et le corollaire excluant tout coefficient uniforme
`K < 1`. Aucun statut de publication ni aucune notion de décohérence n'est
affirmé ici.

**EN.** T3 audit of sharpness of the ED4B additive accumulation bound. This
surface is **NON BORN-SENSITIVE**: it depends on neither `bornRecord` nor branch
weights. The audit checks the explicit family of two identical rational
rotations, the exact composite defect, the exact sum of the two elementary
defects, the ratio identity with `iterationSharpnessC`, its convergence to
`1`, and the corollary excluding every uniform coefficient `K < 1`. No
publication status or decoherence notion is asserted here.
-/

open EverettianDecoherence.Approximation

#check iterationSharpnessTwoStepList
#check iterationSharpnessTwoStep
#check iterationSharpnessTwoStepS
#check iterationSharpnessTwoStepS_pos
#check operatorNormProjectorCommutatorL2_iterationSharpnessTwoStep
#check operatorNormProjectorCommutatorSum_iterationSharpnessTwoStep
#check operatorNormProjectorCommutatorSum_iterationSharpnessTwoStep_pos
#check iterationSharpnessAdditiveRatio
#check iterationSharpnessAdditiveRatio_eq_C
#check iterationSharpnessC_eq_one_sub_two_div
#check iterationSharpnessC_tendsto_one
#check iterationSharpnessAdditiveRatio_tendsto_one
#check exists_twoStep_defect_gt_const_mul_sum_of_lt_one

#print axioms EverettianDecoherence.Approximation.operatorNormProjectorCommutatorL2_iterationSharpnessTwoStep
#print axioms EverettianDecoherence.Approximation.operatorNormProjectorCommutatorSum_iterationSharpnessTwoStep
#print axioms EverettianDecoherence.Approximation.iterationSharpnessAdditiveRatio_eq_C
#print axioms EverettianDecoherence.Approximation.iterationSharpnessC_tendsto_one
#print axioms EverettianDecoherence.Approximation.iterationSharpnessAdditiveRatio_tendsto_one
#print axioms EverettianDecoherence.Approximation.exists_twoStep_defect_gt_const_mul_sum_of_lt_one

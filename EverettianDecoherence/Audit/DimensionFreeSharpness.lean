import EverettianDecoherence.Metrics.DimensionFreeSharpness

/-!
**FR.** Audit T2 de l'optimalité de la constante `2` dans la borne ED2B.
Cette surface est **BORN-SENSITIVE** parce qu'elle utilise `recordProfileL1`.
L'audit vérifie la famille rationnelle explicite, sa normalisation, le calcul
exact du profil, la convergence du quotient vers `2` et le corollaire disant
que toute constante strictement inférieure à `2` échoue sur un membre de la
famille. Aucun statut de publication n'est affirmé ici.

**EN.** T2 audit of sharpness of the constant `2` in the ED2B bound. This
surface is **BORN-SENSITIVE** because it uses `recordProfileL1`. The audit
checks the explicit rational family, normalization, the exact profile
calculation, convergence of the quotient to `2`, and the corollary stating
that every constant strictly below `2` fails on some family member. No
publication status is asserted here.
-/

open EverettianDecoherence.Metrics

#check sharpnessP_sq_add_one_eq_two_mul_Q_sq
#check sharpnessP_tendsto_atTop
#check sharpnessA_sq_add_B_sq
#check sharpnessX_norm
#check sharpnessY_norm
#check sharpness_recordProfileL1
#check sharpness_recordProfileL1_rational
#check dimensionFreeSharpnessRatio
#check dimensionFreeSharpnessRatio_nonneg
#check dimensionFreeSharpnessRatio_le_two
#check dimensionFreeSharpnessRatio_sq
#check dimensionFreeSharpnessRatio_tendsto_two
#check exists_recordProfileL1_gt_const_mul_norm_sub_of_lt_two

#print axioms EverettianDecoherence.Metrics.sharpnessP_sq_add_one_eq_two_mul_Q_sq
#print axioms EverettianDecoherence.Metrics.sharpnessA_sq_add_B_sq
#print axioms EverettianDecoherence.Metrics.sharpnessX_norm
#print axioms EverettianDecoherence.Metrics.sharpnessY_norm
#print axioms EverettianDecoherence.Metrics.sharpness_recordProfileL1
#print axioms EverettianDecoherence.Metrics.sharpness_recordProfileL1_rational
#print axioms EverettianDecoherence.Metrics.dimensionFreeSharpnessRatio_sq
#print axioms EverettianDecoherence.Metrics.dimensionFreeSharpnessRatio_tendsto_two
#print axioms EverettianDecoherence.Metrics.exists_recordProfileL1_gt_const_mul_norm_sub_of_lt_two

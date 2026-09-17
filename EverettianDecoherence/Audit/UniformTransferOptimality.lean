import EverettianDecoherence.Approximation.UniformTransferOptimality

/-!
**FR.** Audit T5B de la borne universelle optimale `sqrt 2` pour le transfert
ED3B. La partie projecteur/commutateur est NON BORN-SENSITIVE ; le passage à
`recordProfileL1` et l'optimalité par T5A sont BORN-SENSITIVE. L'audit vérifie
la borne quadratique agrégée, la borne universelle générale et normalisée,
ainsi que la caractérisation exacte des coefficients universels.

Aucune dynamique, décohérence, émergence de perspective ou revendication de
publication n'est impliquée.

**EN.** T5B audit of the optimal universal `sqrt 2` ED3B transfer bound. The
projector/commutator part is NON BORN-SENSITIVE; transfer to `recordProfileL1`
and optimality through T5A are BORN-SENSITIVE. The audit checks the aggregate
quadratic bound, the general and normalized universal bounds, and the exact
characterization of universal coefficients.

No dynamics, decoherence, perspective emergence, or publication claim is
involved.
-/

open EverettianDecoherence.Approximation

#check norm_sq_recordSubsetProjectorCommutator_le_half_globalSq_mul_norm_sq
#check sqrt_two_mul_norm_recordSubsetProjectorCommutator_le_global_mul_norm
#check recordProfileL1_unitary_le_sqrt_two_mul_norm_sq_mul_operatorNormCommutatorL2
#check recordProfileL1_unitary_le_sqrt_two_mul_operatorNormCommutatorL2
#check IsUniversalUniformTransferCoefficient
#check isUniversalUniformTransferCoefficient_iff_sqrt_two_le

#print axioms EverettianDecoherence.Approximation.norm_sq_recordSubsetProjectorCommutator_le_half_globalSq_mul_norm_sq
#print axioms EverettianDecoherence.Approximation.sqrt_two_mul_norm_recordSubsetProjectorCommutator_le_global_mul_norm
#print axioms EverettianDecoherence.Approximation.recordProfileL1_unitary_le_sqrt_two_mul_norm_sq_mul_operatorNormCommutatorL2
#print axioms EverettianDecoherence.Approximation.recordProfileL1_unitary_le_sqrt_two_mul_operatorNormCommutatorL2
#print axioms EverettianDecoherence.Approximation.isUniversalUniformTransferCoefficient_iff_sqrt_two_le

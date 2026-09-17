import EverettianDecoherence.Metrics.WorkedInstance

/-!
**FR.** Audit T4 de l'instance numérique exacte en dimension `2`. L'audit
vérifie la perspective et l'unitaire explicites, les coefficients rationnels
`24/25` et `7/25`, les poids Born transformés `(576/625, 49/625)`, le profil
L1 réel `98/625`, le défaut de commutateur exact `7 * sqrt 2 / 25`, sa
certification rationnelle `≤ 2/5`, la borne ED3B `4/5` et le gap exact
`402/625`. Le défaut est NON BORN-SENSITIVE ; les poids, le profil et le gap
sont BORN-SENSITIVE. Aucun statut de publication ni aucune notion de
décohérence n'est affirmé ici.

**EN.** T4 audit of the exact numerical instance in dimension `2`. The audit
checks the explicit perspective and unitary, rational coefficients `24/25`
and `7/25`, transformed Born weights `(576/625, 49/625)`, actual L1 profile
`98/625`, exact commutator defect `7 * sqrt 2 / 25`, its rational certificate
`≤ 2/5`, the ED3B bound `4/5`, and the exact gap `402/625`. The defect is NON
BORN-SENSITIVE; the weights, profile, and gap are BORN-SENSITIVE. No
publication status or decoherence notion is asserted here.
-/

open EverettianDecoherence.Metrics

#check workedPerspective
#check workedUnitary
#check workedState
#check workedC_exact
#check workedS_exact
#check workedUnitary_zero
#check workedUnitary_one
#check workedTransformed_line_weight
#check workedTransformed_orthogonal_weight
#check worked_recordProfileL1_exact
#check worked_commutator_defect_exact
#check worked_commutator_defect_le_epsilon
#check worked_exact_ED3B_budget
#check worked_recordProfileL1_le_bound
#check worked_gap_exact
#check worked_actualProfile_lt_bound

#print axioms EverettianDecoherence.Metrics.worked_recordProfileL1_exact
#print axioms EverettianDecoherence.Metrics.worked_commutator_defect_exact
#print axioms EverettianDecoherence.Metrics.worked_commutator_defect_le_epsilon
#print axioms EverettianDecoherence.Metrics.worked_recordProfileL1_le_bound
#print axioms EverettianDecoherence.Metrics.worked_gap_exact

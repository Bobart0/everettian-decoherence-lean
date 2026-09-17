import EverettianDecoherence.Approximation.UniformTransferSharpness

/-!
**FR.** Audit T5A de la barrière `sqrt 2` pour le transfert uniforme ED3B.
Cette surface est BORN-SENSITIVE parce qu'elle utilise `recordProfileL1`, tout
en gardant le défaut uniforme de commutateur séparé comme quantité NON
BORN-SENSITIVE. L'audit vérifie l'identité exacte entre la rotation T3 de
`sharpnessX` et `sharpnessY`, le profil exact `2 s_n`, la positivité du défaut,
le ratio exact `sqrt 2`, l'ancienne borne ED3B `2` conservée comme résultat
valide, et le corollaire excluant tout coefficient uniforme `K < sqrt 2`.
La borne universelle optimale est auditée séparément dans T5B.

T5A ne revendique pas que `sqrt 2` est la meilleure constante universelle :
il établit uniquement une barrière inférieure explicite. Aucun statut de
publication ni nouvelle interprétation physique n'est affirmé ici.

**EN.** T5A audit of the `sqrt 2` barrier for the ED3B uniform transfer. This
surface is BORN-SENSITIVE because it uses `recordProfileL1`, while keeping the
uniform commutator defect separate as a NON BORN-SENSITIVE quantity. The audit
checks the exact identity between the T3 rotation of `sharpnessX` and
`sharpnessY`, the exact profile `2 s_n`, positivity of the defect, the exact
`sqrt 2` ratio, the legacy ED3B upper bound `2` retained as a valid result, and
the corollary excluding every uniform coefficient `K < sqrt 2`. The optimal
universal bound is audited separately in T5B.

T5A does not claim that `sqrt 2` is the best universal constant: it establishes
only an explicit lower barrier. No publication status or new physical
interpretation is asserted here.
-/

open EverettianDecoherence.Approximation

#check iterationSharpnessRotation_sharpnessX_eq_sharpnessY
#check uniformTransferSharpness_profile_exact
#check uniformTransferSharpness_defect_pos
#check uniformTransferSharpnessRatio
#check uniformTransferSharpnessRatio_eq_sqrt_two
#check uniformTransferSharpnessRatio_le_two
#check exists_uniformTransfer_violation_of_lt_sqrt_two

#print axioms EverettianDecoherence.Approximation.iterationSharpnessRotation_sharpnessX_eq_sharpnessY
#print axioms EverettianDecoherence.Approximation.uniformTransferSharpness_profile_exact
#print axioms EverettianDecoherence.Approximation.uniformTransferSharpness_defect_pos
#print axioms EverettianDecoherence.Approximation.uniformTransferSharpnessRatio_eq_sqrt_two
#print axioms EverettianDecoherence.Approximation.uniformTransferSharpnessRatio_le_two
#print axioms EverettianDecoherence.Approximation.exists_uniformTransfer_violation_of_lt_sqrt_two

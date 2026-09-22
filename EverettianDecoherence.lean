import EverettianDecoherence.Core.UpstreamAPI
import EverettianDecoherence.Metrics.RecordProfileL1
import EverettianDecoherence.Metrics.StateRecordPerturbation
import EverettianDecoherence.Metrics.StateRecordDimensionFree
import EverettianDecoherence.Metrics.DimensionFreeSharpness
import EverettianDecoherence.Metrics.WorkedInstance
import EverettianDecoherence.Approximation.ApproximateRecordPreservation
import EverettianDecoherence.Approximation.UniformRecordPreservation
import EverettianDecoherence.Approximation.ComposedRecordPreservation
import EverettianDecoherence.Approximation.IteratedRecordPreservation
import EverettianDecoherence.Approximation.ProjectorStructureStability
import EverettianDecoherence.Approximation.IterationSharpness.RotationParameters
import EverettianDecoherence.Approximation.IterationSharpness.RationalRotation
import EverettianDecoherence.Approximation.IterationSharpness.ElementaryDefect
import EverettianDecoherence.Approximation.IterationSharpness
import EverettianDecoherence.Approximation.UniformTransferSharpness
import EverettianDecoherence.Approximation.UniformTransferOptimality
import EverettianDecoherence.Approximation.StabilitySharpness
import EverettianDecoherence.Factorization.FiniteBipartiteFactorization
import EverettianDecoherence.Factorization.FiniteBipartiteSlices
import EverettianDecoherence.Factorization.AmbientBipartiteCoordinateMasks

/-!
**FR.** ED1 fournit la géométrie L1, ED2A une borne explicite dépendant du
nombre de cellules, ED2B une borne globale indépendante de ce nombre, ED3A un
défaut statewise, ED3B son uniformisation par norme d'opérateur, ED4A la
composition de deux transformations à perspective fixée, ED4B l'itération
finie sur une liste ordonnée avec accumulation d'erreurs. Le contrôle T1
`ProjectorStructureStability` relie en outre, de manière NON BORN-SENSITIVE,
le défaut uniforme de commutation à l'écart entre projecteurs transportés et
originaux. T2 `DimensionFreeSharpness`, BORN-SENSITIVE, établit en dimension
`2` l'optimalité de la constante `2` de la borne ED2B par une famille
rationnelle explicite. T3 `IterationSharpness`, NON BORN-SENSITIVE, montre sur
une famille explicite de deux rotations identiques que le coefficient `1` de
l'accumulation additive ED4B est asymptotiquement optimal : le ratio entre le
défaut exact du composé et la somme des défauts élémentaires tend vers `1`.
T4 `WorkedInstance` fournit en dimension `2` une instance entièrement calculée
avec unitaire rationnel, défaut de commutateur exact, borne ED3B rationnelle,
poids borniens, profil L1 réel et gap explicite ; le défaut est NON
BORN-SENSITIVE tandis que le profil et le gap sont BORN-SENSITIVE. T5A
`UniformTransferSharpness` ouvre un front transversal : sur la même famille
rationnelle, la rotation T3 envoie exactement `sharpnessX` sur `sharpnessY`, et
le rapport entre variation réelle du profil et défaut uniforme vaut exactement
`sqrt 2`. T5B `UniformTransferOptimality` complète cette barrière par une
borne universelle `sqrt 2` et caractérise exactement les coefficients
universels normalisés : `K` convient si et seulement si `sqrt 2 ≤ K`. Le
front post-T5 `StabilitySharpness`, NON BORN-SENSITIVE, formalise en outre la
rigidité exacte de la saturation de l'enveloppe des cuts, un modulus explicite
de concentration sur deux cellules et une famille tridimensionnelle montrant
que la dépendance en `η / ρ^2` est nécessaire à constante près. ED5A fournit une factorisation bipartite finie
typée en coordonnées, ED5B des tranches bipartites et profils de normes
purement coordonnés, et ED5C des masques finis de coordonnées bipartites
transportés dans l'espace ambiant. Aucune API locale stable ni théorème de
décohérence n'est annoncé.

**EN.** ED1 provides L1 geometry, ED2A an explicit cell-count-dependent bound,
ED2B a global bound independent of that count, ED3A a statewise defect, ED3B
its operator-norm uniformization, ED4A the composition of two transformations
at a fixed perspective, and ED4B finite iteration over an ordered list with
error accumulation. The T1 `ProjectorStructureStability` control additionally
relates, in a NON BORN-SENSITIVE way, the uniform commutator defect to the
displacement between transported and original projectors. T2
`DimensionFreeSharpness`, which is BORN-SENSITIVE, establishes in dimension
`2` sharpness of the ED2B constant `2` through an explicit rational family.
T3 `IterationSharpness`, which is NON BORN-SENSITIVE, shows on an explicit
family of two identical rotations that the coefficient `1` in the ED4B
additive accumulation bound is asymptotically sharp: the ratio between the
exact composite defect and the sum of elementary defects tends to `1`. T4
`WorkedInstance` gives a fully calculated dimension-`2` example with a
rational unitary, exact commutator defect, rational ED3B bound, Born weights,
actual L1 profile, and explicit gap; the defect is NON BORN-SENSITIVE while the
profile and gap are BORN-SENSITIVE. T5A `UniformTransferSharpness` opens a
transversal front: on the same rational family, the T3 rotation maps
`sharpnessX` exactly to `sharpnessY`, and the ratio between actual profile
variation and uniform defect is exactly `sqrt 2`. T5B `UniformTransferOptimality` complements this lower barrier with
a universal `sqrt 2` upper bound and exactly characterizes normalized
universal coefficients: `K` works if and only if `sqrt 2 ≤ K`. The post-T5
`StabilitySharpness` front, which is NON BORN-SENSITIVE, additionally
formalizes the cut envelope, exact saturation rigidity, the exact optimal
top-two tail, finite coefficient `18`, sharp asymptotic coefficients `8`
and `4`, the continuous `C^3` family, the fixed-budget mechanisms, and a
geometric diffuse `2m`-cell family attaining the sharp `1/8` threshold. ED5A provides a typed finite bipartite coordinate
factorization, ED5B purely coordinate bipartite slices and norm profiles, and
ED5C finite bipartite coordinate masks transported into the ambient space. No
stable local API or decoherence theorem is announced.
-/
import EverettianDecoherence.Core.UpstreamAPI
import EverettianDecoherence.Metrics.RecordProfileL1
import EverettianDecoherence.Metrics.StateRecordPerturbation
import EverettianDecoherence.Metrics.StateRecordDimensionFree
import EverettianDecoherence.Metrics.DimensionFreeSharpness
import EverettianDecoherence.Approximation.ApproximateRecordPreservation
import EverettianDecoherence.Approximation.UniformRecordPreservation
import EverettianDecoherence.Approximation.ComposedRecordPreservation
import EverettianDecoherence.Approximation.IteratedRecordPreservation
import EverettianDecoherence.Approximation.ProjectorStructureStability
import EverettianDecoherence.Approximation.IterationSharpness.RotationParameters
import EverettianDecoherence.Approximation.IterationSharpness.RationalRotation
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
originaux. T2 `DimensionFreeSharpness` étudie, de manière BORN-SENSITIVE,
l'optimalité de la constante `2` de la borne ED2B par une famille rationnelle
explicite en dimension `2`; son intégration sur `main` précède ici la
vérification locale de compilation demandée par l'auteur. ED5A fournit une
factorisation bipartite finie typée en coordonnées, ED5B des tranches
bipartites et profils de normes purement coordonnés, et ED5C des masques finis
de coordonnées bipartites transportés dans l'espace ambiant. Aucune API locale
stable ni théorème de décohérence n'est annoncé.

**EN.** ED1 provides L1 geometry, ED2A an explicit cell-count-dependent bound,
ED2B a global bound independent of that count, ED3A a statewise defect, ED3B
its operator-norm uniformization, ED4A the composition of two transformations
at a fixed perspective, and ED4B finite iteration over an ordered list with
error accumulation. The T1 `ProjectorStructureStability` control additionally
relates, in a NON BORN-SENSITIVE way, the uniform commutator defect to the
displacement between transported and original projectors. T2
`DimensionFreeSharpness` studies, in a BORN-SENSITIVE way, sharpness of the
ED2B constant `2` through an explicit rational family in dimension `2`; its
integration on `main` here precedes the local compilation check requested by
the author. ED5A provides a typed finite bipartite coordinate factorization,
ED5B purely coordinate bipartite slices and norm profiles, and ED5C finite
bipartite coordinate masks transported into the ambient space. No stable local
API or decoherence theorem is announced.
-/

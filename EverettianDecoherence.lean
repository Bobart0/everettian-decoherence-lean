import EverettianDecoherence.Core.UpstreamAPI
import EverettianDecoherence.Metrics.RecordProfileL1
import EverettianDecoherence.Metrics.StateRecordPerturbation
import EverettianDecoherence.Metrics.StateRecordDimensionFree
import EverettianDecoherence.Approximation.ApproximateRecordPreservation
import EverettianDecoherence.Approximation.UniformRecordPreservation
import EverettianDecoherence.Approximation.ComposedRecordPreservation
import EverettianDecoherence.Approximation.IteratedRecordPreservation

/-!
**FR.** ED1 fournit la géométrie L1, ED2A une borne explicite dépendant du
nombre de cellules, ED2B une borne globale indépendante de ce nombre, ED3A un
défaut statewise, ED3B son uniformisation par norme d'opérateur, ED4A la
composition de deux transformations à perspective fixée, et ED4B l'itération
finie sur une liste ordonnée avec accumulation d'erreurs. Aucune API locale
stable ni théorème de décohérence n'est annoncé.

**EN.** ED1 provides L1 geometry, ED2A an explicit cell-count-dependent bound,
ED2B a global bound independent of that count, ED3A a statewise defect, ED3B
its operator-norm uniformization, ED4A the composition of two transformations
at a fixed perspective, and ED4B finite iteration over an ordered list with
error accumulation. No stable local API or decoherence theorem is announced.
-/

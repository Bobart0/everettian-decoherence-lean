import EverettianDecoherence.Core.UpstreamAPI
import EverettianDecoherence.Metrics.RecordProfileL1
import EverettianDecoherence.Metrics.StateRecordPerturbation
import EverettianDecoherence.Metrics.StateRecordDimensionFree
import EverettianDecoherence.Approximation.ApproximateRecordPreservation
import EverettianDecoherence.Approximation.UniformRecordPreservation

/-!
**FR.** ED1 fournit la géométrie L1, ED2A une borne explicite dépendant du
nombre de cellules, et ED2B une borne globale indépendante de ce nombre.
Aucune API locale stable ni théorème de décohérence n'est annoncé.

**EN.** ED1 provides L1 geometry, ED2A an explicit cell-count-dependent bound,
and ED2B a global bound independent of that count. No stable local API or
decoherence theorem is announced.
-/

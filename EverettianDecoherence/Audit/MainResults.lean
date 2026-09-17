import EverettianDecoherence.Audit.UpstreamAPIContract
import EverettianDecoherence.Audit.RecordProfileL1
import EverettianDecoherence.Audit.StateRecordPerturbation
import EverettianDecoherence.Audit.StateRecordDimensionFree
import EverettianDecoherence.Audit.DimensionFreeSharpness
import EverettianDecoherence.Audit.ApproximateRecordPreservation
import EverettianDecoherence.Audit.UniformRecordPreservation
import EverettianDecoherence.Audit.ComposedRecordPreservation
import EverettianDecoherence.Audit.IteratedRecordPreservation
import EverettianDecoherence.Audit.ProjectorStructureStability
import EverettianDecoherence.Audit.FiniteBipartiteFactorization
import EverettianDecoherence.Audit.FiniteBipartiteSlices
import EverettianDecoherence.Audit.FiniteBipartiteCoordinateMasks

/-!
**FR.** Agrégateur des audits des résultats locaux ED1, ED2A, ED2B, ED3A,
ED3B, ED4A, ED4B, du contrôle T1 NON BORN-SENSITIVE de structure projective,
du module T2 BORN-SENSITIVE d'optimalité de la constante `2`, ainsi que ED5A,
ED5B et ED5C. Le fichier d'audit T2 est présent, mais son exécution doit encore
être confirmée par compilation locale.

**EN.** Aggregator of local ED1, ED2A, ED2B, ED3A, ED3B, ED4A, ED4B result
audits, the T1 NON BORN-SENSITIVE projector-structure control, the T2
BORN-SENSITIVE sharpness module for constant `2`, and ED5A, ED5B, and ED5C
audits. The T2 audit file is present, but its execution still requires local
compilation confirmation.
-/

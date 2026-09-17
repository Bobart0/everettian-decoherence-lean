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
import EverettianDecoherence.Audit.IterationSharpness
import EverettianDecoherence.Audit.FiniteBipartiteFactorization
import EverettianDecoherence.Audit.FiniteBipartiteSlices
import EverettianDecoherence.Audit.FiniteBipartiteCoordinateMasks

/-!
**FR.** Agrégateur des audits des résultats locaux ED1, ED2A, ED2B, ED3A,
ED3B, ED4A, ED4B, du contrôle T1 NON BORN-SENSITIVE de structure projective,
du module T2 BORN-SENSITIVE d'optimalité de la constante `2`, du module T3
NON BORN-SENSITIVE de sharpness de l'accumulation additive ED4B, ainsi que
ED5A, ED5B et ED5C. T2 et T3 sont formalisés et audités ; aucun statut de
publication n'est affirmé ici.

**EN.** Aggregator of local ED1, ED2A, ED2B, ED3A, ED3B, ED4A, ED4B result
audits, the T1 NON BORN-SENSITIVE projector-structure control, the T2
BORN-SENSITIVE sharpness module for constant `2`, the T3 NON BORN-SENSITIVE
sharpness module for ED4B additive accumulation, and ED5A, ED5B, and ED5C
audits. T2 and T3 are formalized and audited; no publication status is asserted
here.
-/

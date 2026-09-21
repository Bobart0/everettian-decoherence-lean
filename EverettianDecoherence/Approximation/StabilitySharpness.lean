import EverettianDecoherence.Approximation.ExactTwoCellActiveRigidity
import EverettianDecoherence.Approximation.CutEnvelopeStability
import EverettianDecoherence.Approximation.CutEnvelopeStabilitySharp
import EverettianDecoherence.Approximation.TwoCellConcentrationThreshold
import EverettianDecoherence.Approximation.StabilitySharpness.Asymptotics

/-!
**FR.** Agrégateur du nouveau front de stabilité quantitative ouvert après
T5. Il rassemble :
- la rigidité exacte des cas de saturation de l'enveloppe des cuts ;
- la stabilité quantitative à deux cellules, y compris le modulus v12 à constante 18 ;
- la famille tridimensionnelle de sharpness et son obstruction d'échelle.

Ce module ne change aucune interprétation physique de T0--T5 et n'introduit
aucune revendication de nouveauté bibliographique.

**EN.** Aggregator for the quantitative-stability front opened after T5. It
collects exact cut-envelope rigidity, quantitative two-cell stability, including the v12 modulus with constant 18, and the three-dimensional sharpness family with its scale
obstruction. It changes no T0--T5 physical interpretation and makes no
bibliographic novelty claim.
-/

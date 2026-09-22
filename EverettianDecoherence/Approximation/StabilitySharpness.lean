import EverettianDecoherence.Approximation.ExactTwoCellActiveRigidity
import EverettianDecoherence.Approximation.CutEnvelopeStability
import EverettianDecoherence.Approximation.CutEnvelopeStabilitySharp
import EverettianDecoherence.Approximation.TwoCellConcentrationThreshold
import EverettianDecoherence.Approximation.StabilitySharpness.V12SharpConstants
import EverettianDecoherence.Approximation.StabilitySharpness.V12TwoParameterAsymptotics
import EverettianDecoherence.Approximation.MaxCutThresholdStability
import EverettianDecoherence.Approximation.V12AsymptoticEight
import EverettianDecoherence.Approximation.V12UltraNearFour
import EverettianDecoherence.Approximation.StabilitySharpness.Asymptotics
import EverettianDecoherence.Approximation.StabilitySharpness.FixedBudgetSlope
import EverettianDecoherence.Approximation.StabilitySharpness.DiffuseFamilyScalar

/-!
**FR.** Agrégateur du nouveau front de stabilité quantitative ouvert après
T5. Il rassemble :
- la rigidité exacte des cas de saturation de l'enveloppe des cuts ;
- la stabilité quantitative à deux cellules, y compris le modulus v12 à constante 18 ;
- les coefficients asymptotiques universels v12 : 8 en régime général de petit défaut et 4 en régime ultra-near ;
- la famille tridimensionnelle de sharpness qui atteint respectivement 8 et 4 ;
- la famille continue à deux paramètres réalisée géométriquement dans C^3, avec interpolation de la constante 4/max{x,1-x}, chemin symétrique 8 et chemin ultra-near 4 ;
- le rattrapage v18 : couche scalaire à budget fixé et identités scalaires de la famille diffuse 2m-cellules.

Ce module ne change aucune interprétation physique de T0--T5 et n'introduit
aucune revendication de nouveauté bibliographique.

**EN.** Aggregator for the quantitative-stability front opened after T5. It
collects exact cut-envelope rigidity, quantitative two-cell stability including the v12 finite constant 18, the universal asymptotic coefficient 8, the ultra-near coefficient 4, the three-dimensional sharpness family attaining the constants 8 and 4, and the continuous two-parameter C3 realization interpolating the coefficient 4/max{x,1-x}, with symmetric coefficient 8 and ultra-near coefficient 4. It also includes the v18 catch-up scalar layers for fixed positive budget and the diffuse 2m-cell family. It changes no T0--T5 physical interpretation and makes no
bibliographic novelty claim.
-/

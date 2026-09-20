# Priority audit v02 — gap recast

Reference manuscript: \`paper/stability_rigidity_sharpness_v10_gap_recast.tex\`.

This pass re-ran the novelty search after changing the conceptual framing from
projector--unitary commutator profiles to gaps between two labelled orthogonal
decompositions and their matched coarsenings.

## 1. Search axes

The search was deliberately broadened beyond the manuscript's terminology:

- gaps / distances between subspaces and differences of orthogonal projections;
- principal and canonical angles;
- pairs and finite families of orthogonal projections;
- unitary conjugation of decompositions;
- coarsenings / subset sums of resolutions of the identity;
- projection commutators;
- pinching operators and off-diagonal parts;
- almost-invariant / almost-commuting structures;
- equality and near-equality / stability for matrix inequalities.

## 2. Closest literature after the gap recast

### Classical gap / principal-angle geometry

- Björck--Golub (1973): computational principal angles between subspaces.
- Miao--Ben-Israel (1992): principal angles and related subspace quantities.
- Galántai--Hegedűs (2006): projector-based principal angles in complex spaces.
- Galántai (2008): pairs of orthogonal projections, Halmos/Wedin forms, and relative subspace positions.
- Halmos (1969) and Böttcher--Spitkovsky (2010): canonical two-subspace / two-projection geometry.

These sources explain the intrinsic meaning of \(\|P_i-Q_i\|\), but the audit did
not locate a theorem comparing a whole labelled family of cell gaps with the
maximum gap over all matched coarsenings.

### Projection commutators and fixed-commutator geometry

- Li (2004), Shi--Ji (2019), Marcoux--Radjavi--Zhang (2024): representation and closure questions for commutators/differences of projections.
- Andruchow--Di Iorio y Lucero (2021): geometric classes defined by Schatten commutator conditions.
- Chaile--Chiumiento (2026 preprint): geometry of pairs of projections with a fixed commutator.

These are pair-of-projection problems. They do not appear to contain the
finite labelled-decomposition inverse theorem of v0.10.

### Pinching / off-diagonal operator methods

- Bhatia--Kittaneh (2008), *Commutators, pinchings, and spectral variation*,
  directly confirms that pinching and commutator estimates are a natural
  neighboring language.
- Searches under pinching/off-diagonal terminology did not locate the v0.10
  finite-family envelope plus two-cell equality/stability package.

This remains the main residual folklore risk for the elementary envelope
itself. The v0.10 manuscript therefore does **not** assert priority for that
base estimate.

### Almost commuting / perturbative stability

Lin, Friis--Rørdam, Hastings, Voiculescu, Exel--Loring, Herrera, and recent
unitary work concern perturbation toward nearby exact commutation or
topological obstructions. Their output is categorically different from
concentration of a fixed cell-gap profile.

## 3. Priority assessment by result

| Result | Current priority assessment |
|---|---|
| arbitrary-operator cut envelope | likely elementary / possible folklore; no strong priority claim should be made |
| gap-form envelope for two labelled decompositions | same residual folklore risk as above |
| equality iff exactly two nonzero cell gaps | no direct predecessor located |
| cardinality- and dimension-free near-equality concentration | strongest apparent novelty; no direct predecessor located |
| intrinsic \(O(\eta/\delta^2)\) modulus | no direct predecessor located |
| one-parameter 3-cell inverse-square obstruction | no direct predecessor located |
| limiting obstruction constant \(4\) for the explicit family | no direct predecessor located; not claimed universal-optimal |

## 4. Editorial novelty statement supported by this audit

A defensible formulation is:

> We prove an inverse theory for the finite-family coarsening-gap inequality:
> positive-defect equality is supported on exactly two cells, near equality
> forces dimension- and cardinality-free two-cell concentration, and a
> three-cell family shows that the inverse-square dependence on the global
> gap scale is unavoidable up to constants.

Avoid:
- "first";
- "new sharp \(1/2\) inequality" as the headline;
- claims that the constant \(4\) is the best universal stability coefficient.

## 5. Residual priority risks

The remaining serious risk is not the standard principal-angle literature but
an equivalent statement hidden in older block-operator, pinching, row/column
operator, or conditional-expectation terminology. The targeted search did not
find such a statement, but absence cannot be certified exhaustively.

The v0.10 framing materially reduces this risk because it places the problem
in the correct established language and cites the closest pinching and
subspace-geometry literature directly.

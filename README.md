# Lemniscate stability: review and Lean formalization in progress

**The full PDE theorem is not yet formalized. This repository must not be
described as a complete Lean proof of the paper.**

The target is the 22-page PDF supplied by the user, titled *Local asymptotic
stability of Bernoulli lemniscates under the free elastic flow*. Its SHA-256 is
`36c9336c9f1e002cde61b856650ba22b6320b9fa3a5b72e30b338d5d6f13ee07`.
The matched original standalone TeX has SHA-256
`8e8e5f3419bd2c8a0be99e16dd4e980aaf4bc4dad247cc8b51018b6eddda7d84`.

**The current formalization target is `audit/source/revised.tex`.** After each
manuscript revision, theorem statements, hypotheses and proof dependencies are
checked against that version. The original source is retained for comparison.

The revised manuscript preserves the final theorem, defines the adjoint trial
function by eighteen fixed rational coefficients instead of a Galerkin linear
solve, and replaces the adjoint
H4 residual proof with the shorter argument verified in Lean. It obtains the
bound 177 times the residual and a certified squared error below 62658e-30
for the fixed normalized trial. Intermediate single-period bounds use -21/4
directly. The original source is preserved; this revision is not a full-paper
proof certificate.

The work has three distinct layers:

1. Mathematical review of the definitions, proofs, analytic estimates and cited
   theorems. The record is in `audit/REVIEW.md`.
2. Exact rational recomputation of the paper's finite inequalities. These Python
   computations support the review; they are not Lean proofs.
3. Lean proofs, compiled with Lean 4.33.1 and Mathlib v4.33.1. A proof of an
   abstract implication is explicitly distinguished from its application to the
   paper's concrete unbounded operator.

## Modules

| Module | Intended coverage |
| --- | --- |
| `Lemniscate.Algebra` | Linearization and Fourier algebra, scalar estimates, exact neutral-factor cancellation, gap scaling |
| `Lemniscate.Bernstein` | Positivity on the whole half interval and exact degree-four and degree-six coefficient conversions |
| `Lemniscate.WeightedRows` | Weighted finite quadratic-form estimate without a uniform lower bound on weights |
| `Lemniscate.NeutralMode` | Explicit-domain Hilbert-space argument for the kernel, exclusion of generalized neutral modes, eigenvalue bound |
| `Lemniscate.CoarseArithmetic` | Executable rational definitions for the actual coarse Fourier enclosures and cosine rows |
| `Lemniscate.IntervalSoundness` | Real containment for addition, multiplication, scaling and absolute upper bounds |
| `Lemniscate.IntervalExtras` | Positive reciprocal and division, certified square-root enclosures, and the actual coarse square-root-of-two bounds |
| `Lemniscate.RoundedIntervals` | Outward rounding of exact rational intervals preserves real containment |
| `Lemniscate.RefinedFourierEnclosure` | Fine positive Fourier coefficient intervals and the constant coefficient with its complete infinite tail |
| `Lemniscate.OddArithmetic` | All 84 odd-subspace Bernstein comparisons and 12 zero-parameter comparisons, computed from rational formulas |
| `Lemniscate.OddPositivity` | Casts the computed coefficients into real polynomials and proves positivity on the entire parameter interval |
| `Lemniscate.OddPolynomialSemantics` | Proves the list-polynomial operations agree with real polynomial evaluation and connects the low-row certificates to that evaluation |
| `Lemniscate.OddWeights` | Positivity of every odd-row weight on the half interval, exact exceptional weights and geometric upper bounds for high weights |
| `Lemniscate.OddEntryPolynomials` | Proves the endpoint-based absolute-entry polynomials bound the actual coefficient formula throughout the half interval |
| `Lemniscate.OddRowSemantics` | Identifies each row polynomial with its diagonal, finite head and explicit rational omitted-tail expression |
| `Lemniscate.OddMatrix` | Symmetry and finite low-row inequalities for the real odd matrix, with the rational omitted-tail expression still explicit |
| `Lemniscate.OddEntryTails` | Bounds each off-diagonal entry by its actual half-distance and a geometric factor |
| `Lemniscate.PeriodicOddMatrix` | Identifies the zero-parameter odd matrix with actual periodic Fourier-mode pairings under explicit profile Fourier and period hypotheses |
| `Lemniscate.OddOmittedTails` | Proves convergence and the stated rational bound for both omitted infinite tails, and combines them with each of the twelve finite low-row estimates |
| `Lemniscate.OddLowRows` | Reindexes the complete low rows over all integer indices, proves absolute summability, and obtains normalized row bounds below -1 on the half interval and below -6 at zero |
| `Lemniscate.OddSignedWeights` | Proves geometric weight envelopes for every signed odd column, including all six exceptional low frequencies, and the same-sign and cross-sign weight ratios |
| `Lemniscate.OddSignedGeometry` | Computes actual half-distances and shifted frequencies on both sign branches and proves the sharper lower-direction polynomial bound |
| `Lemniscate.OddSignedEntries` | Bounds lower, upper and opposite-sign high-row entries using the actual shifted frequency |
| `Lemniscate.OddWeightedEntries` | Combines the entry and weight estimates, keeping the exact geometric factors qb/a, qb*a and qb*(qb/a)^j |
| `Lemniscate.OddHighMoments` | Exact geometric moment sums, decay for every high index, and the rational certificate for the opposite-sign constant |
| `Lemniscate.OddHighBranchSums` | Proves absolute summability of both complete sign branches; bounds the opposite branch strictly below 8 times the squared shifted frequency |
| `Lemniscate.OddHighRows` | Reassembles the full integer-indexed row and connects it to the certified quartic, obtaining the high-row bound below -3112 |
| `Lemniscate.OddAllRows` | Combines the low and high rows for every odd frequency: normalized rows below -1 on the half interval and below -6 at zero |
| `Lemniscate.OddFiniteForm` | Applies the full row bounds to every finite complex coefficient vector, with gaps 1 and 6 |
| `Lemniscate.OddSobolevEntries` | Uniform bounds for every odd matrix entry by actual H2 frequency weights and a decaying distance kernel |
| `Lemniscate.OddSobolevKernel` | Convergence of the complete integer distance-kernel row and its uniform bound 512 |
| `Lemniscate.OddSobolevSummability` | Absolute convergence of the full odd energy double series for every H2-weighted complex sequence, proved from finite sums |
| `Lemniscate.OddH2Dissipation` | Passes the finite-set estimates to the infinite H2 coefficient form: gap 1 on the half interval and gap 6 at zero |
| `Lemniscate.PeriodicOddCoefficients` | Complete reconstruction and Parseval identity for the actual odd Fourier subspace, and its H2 coefficient regularity |
| `Lemniscate.PeriodicOddPolynomials` | Identifies the differential energy of every finite odd Fourier polynomial with the zero-parameter matrix form |
| `Lemniscate.PeriodicOddApproximation` | Simultaneous L2 convergence of finite odd Fourier sums and their first two weak derivatives |
| `Lemniscate.PeriodicOddEnergy` | Identifies the infinite odd coefficient form with actual periodic H2 energy and transfers the -6 bound |
| `Lemniscate.PeriodicOddOperatorEnergy` | Proves -6 dissipation for the actual H4 operator on the full odd-frequency subspace under explicit profile Fourier and period hypotheses |
| `Lemniscate.PeriodicFrequencyParts` | Orthogonal even/odd frequency projections on actual L2, with preservation of H4 and commutation with weak derivatives |
| `Lemniscate.PeriodicFrequencyOperator` | Proves projection/operator commutation and vanishing cross energy terms from the coefficient's vanishing odd Fourier modes |
| `Lemniscate.PeriodicFullEnergy` | Combines all single-period subspaces to obtain -21/4 coercivity on the actual rotation-orthogonal H4 complement |
| `Lemniscate.NeutralNormalization` | Normalizes a proved nonzero neutral vector for the abstract kernel and spectral argument |
| `Lemniscate.PeriodicSingleSpectrum` | Instantiates the actual single-period operator: its kernel consists of rotation multiples, no nontrivial length-two generalized kernel chain exists, zero is spectral, and every nonzero spectral point has real part at most -21/4, under explicit Jacobi data |
| `Lemniscate.PeriodicPerturbedFredholm` | Proves a compact bounded inverse for a bounded L2 perturbation of the H4 operator whenever its kernel is zero |
| `Lemniscate.NeutralAdjointVector` | Constructs the unique normalized adjoint neutral vector from the two-sided inverse of the rank-one neutral shift |
| `Lemniscate.PeriodicAdjointNeutral` | Proves existence and uniqueness of the actual H4 adjoint zero vector normalized against the unit rotation, under the explicit profile data |
| `Lemniscate.PeriodicSymmetryPairing` | Self-adjoint pairing identities for reflection and even-frequency projection, and the corresponding symmetries of the normalized rotation |
| `Lemniscate.PeriodicAdjointSymmetry` | Derives reflection oddness and vanishing odd Fourier coefficients of the exact adjoint vector from uniqueness |
| `Lemniscate.PeriodicConjugation` | Pointwise complex conjugation on actual L2, its Fourier and pairing identities, and its compatibility with weak differentiation and real multiplication |
| `Lemniscate.PeriodicConjugateOperator` | Proves H4 preservation and commutation with the real differential operator, then derives reality from normalized adjoint uniqueness |
| `Lemniscate.PeriodicAdjointReality` | Constructs the unique real H4 adjoint zero vector in the even sine subspace and proves the common-phase Fourier identities |
| `Lemniscate.NeutralTransform` | Bounded mutually inverse exact neutral transforms, domain preservation, and the orthogonal-compression formula on an explicit operator domain |
| `Lemniscate.PeriodicNeutralTransform` | Instantiates the exact neutral decomposition on actual periodic H4, including zero neutral row and column; proves reflection commutation |
| `Lemniscate.NeutralHouseholder` | Exact Householder involution, symmetric pairing, inner-product preservation and inverse on an explicit linear domain |
| `Lemniscate.PeriodicHouseholderAnchor` | Constructs the actual unit H4 reference mode at Fourier frequencies ±2 and proves the chosen phase of rotation has strictly positive pairing with it |
| `Lemniscate.PeriodicHouseholder` | Proves the actual denominator exceeds one, all Householder identities on L2 and H4, preservation of even frequencies and reflection commutation |
| `Lemniscate.PeriodicCenteredNeutral` | Proves common-phase invariance of the neutral transform, then zero row and column corresponding to the fixed Fourier mode for the combined exact transformed expression and its symmetric pairing |
| `Lemniscate.PeriodicBlochPolynomial` | Defines the actual shifted differential expression on H4 and proves its exact quartic expansion in the Bloch parameter |
| `Lemniscate.PeriodicBlochParity` | Proves reflection parity of every Bloch coefficient and identifies the fourth coefficient as the scalar -4r² |
| `Lemniscate.PeriodicBlochCenter` | Identifies transformed coefficients along the fixed Fourier mode with exact adjoint/rotation pairings and eliminates the odd coefficients by reflection |
| `Lemniscate.PeriodicBlochCenterPolynomial` | Proves the full transformed polynomial, exact quadratic center cancellation and linear cross cancellation before division by the parameter |
| `Lemniscate.PeriodicBlochFourier` | Identifies all Fourier entries of the actual Bloch operator and their symmetric odd-frequency pairing with the certified matrix for every real parameter |
| `Lemniscate.PeriodicBlochOddFinite` | Identifies the actual energy of every finite odd Fourier sum with the certified matrix form and proves its half-interval bound |
| `Lemniscate.PeriodicBlochOddLimit` | Proves convergence of all four derivatives and the actual Bloch expression, then obtains -1 dissipation for every odd-subspace H4 function and every parameter in [0,1/2] |
| `Lemniscate.PeriodicAdjointResidual` | Bounds the L2 error of any normalized H4 adjoint trial in the even sine subspace by one seventy-fifth of its actual adjoint residual norm |
| `Lemniscate.PeriodicProfileBounds` | Derives uniform profile bounds from the first integral, square-multiplier energy identities and the actual H4 Gårding inequality |
| `Lemniscate.PeriodicAdjointDerivativeBounds` | Uses the actual adjoint differential equation to control the fourth derivative and obtain all four derivative error bounds |
| `Lemniscate.PeriodicAdjointSobolevError` | Proves the angular H4 trial error is at most 177 times the actual adjoint residual norm |
| `Lemniscate.PeriodicAdjointTrial` | Identifies every Fourier coefficient and the full Parseval sum of a finite trial's actual adjoint residual; proves exact normalization and residual scaling |
| `Lemniscate.FixedAdjointTrial` | The paper's 18 exact rational coefficients and the coarse inequalities used for normalization |
| `Lemniscate.AdjointTrialPairing` | A two-term proof that the trial pairing is greater than one |
| `Lemniscate.FineCoefficientData` | Kernel-checked rational enclosures for every coefficient needed in the finite residual |
| `Lemniscate.RawTrialArithmetic` | Every finite residual comparison and the rational sum-of-squares inequality |
| `Lemniscate.PeriodicSineAdjointTrial` | The actual adjoint action on a sine polynomial and its complete Parseval identity |
| `Lemniscate.AdjointResidualEntries` | Identification with the full operator matrix and soundness of the finite residual intervals |
| `Lemniscate.AdjointResidualTail` | The entire infinite residual tail, controlled by a convergent geometric moment |
| `Lemniscate.PeriodicFixedTrialResidual` | The actual adjoint residual of the fixed rational trial has squared norm below 2e-30, under the explicit profile Fourier hypotheses |
| `Lemniscate.PeriodicTrialNormalization` | The actual rotation pairing and the same residual bound after normalization, including either sign and every unit complex phase |
| `Lemniscate.PeriodicTrialSector` | The finite trial and its scalar multiples lie in the even-frequency sine subspace |
| `Lemniscate.PeriodicAngularH4Norm` | Nonnegativity, homogeneity and the triangle inequality for the angular Sobolev sum norm |
| `Lemniscate.PeriodicFixedTrialError` | The actual normalized fixed trial has squared H4 error below 62658e-30, under the explicit profile hypotheses and the previously established conditions on the exact adjoint eigenfunction |
| `Lemniscate.PeriodicSineDerivativeNorm` | Exact norms of all four derivatives of the normalized sine modes, proved uniformly using Fourier orthogonality |
| `Lemniscate.PeriodicSinePolynomialNorm` | The angular H4 norm of a sine polynomial is bounded by the manuscript's weighted coefficient sum L4 |
| `Lemniscate.PeriodicRotationNorm` | Derives the exact L2 norm of the rotation mode directly from the profile ODE and first integral |
| `Lemniscate.PeriodicSineParseval` | Parseval on the even-frequency sine subspace, expressed using only positive Fourier frequencies |
| `Lemniscate.PeriodicRotationSineMass` | Proves the sine coefficient normalization used in the manuscript, from the profile identities and Parseval |
| `Lemniscate.QuarticTail` | A general quartic estimate for every real argument beyond a cutoff |
| `Lemniscate.HighFrequency` | Instantiates that estimate with all four actual rational high-frequency quartics |
| `Lemniscate.GeometricTails` | Convergence and exact sums for the first three geometric moment tails |
| `Lemniscate.HigherGeometricMoments` | Convergence and exact rational sums for moments four through six |
| `Lemniscate.FourierEnclosure` | Monotonicity and rational enclosures for the positive Fourier coefficient formula, conditional on parameter bounds |
| `Lemniscate.FourierSeries` | Convergence and uniform tail bounds for that series, and the constant coefficient's full rational enclosure |
| `Lemniscate.CosineMatrix` | Connects the convergent coefficient formulas to the actual rational cosine-entry intervals, conditional on parameter bounds |
| `Lemniscate.NomeBounds` | Proves the refined interval of width 10^(-21) for exp(-pi) from the verified twenty-digit pi bounds and 26 exponential-series terms; later estimates use this single enclosure |
| `Lemniscate.ThetaBounds` | Convergence and interval bounds for the theta series and its negative fourth power |
| `Lemniscate.ConcreteCoefficients` | Instantiates the coefficient and cosine-entry enclosures at exp(-pi) and the theta parameter |
| `Lemniscate.SineConstraint` | Convergence and the strict 87/500 bound for the full squared coefficient-ratio series |
| `Lemniscate.SineHilbert` | Constructs the complex l2 tail vector; derives first-mode and mass bounds from orthogonality and the conditional -75 energy estimate |
| `Lemniscate.SineArithmetic` | Computes exact certificates for the sine first diagonal, the two low tail-block rows, the coupling square bound, and the positive diagonal correction |
| `Lemniscate.SineMatrix` | Defines the sine matrix from the actual coefficient formulas, proves interval containment and symmetry, and controls its full upper tails |
| `Lemniscate.GeometricMomentTails` | Proves the rational geometric moments and arbitrary shifted tails through degree six |
| `Lemniscate.SineCoupling` | Includes the entire coupling row, proves its square sum below 3916, constructs its l2 vector, and proves the norm bound 63 |
| `Lemniscate.SineHighEntries` | Controls lower entries and the sine diagonal's positive reflected-frequency term; derives the quartic diagonal bound |
| `Lemniscate.SineRows` | Combines exact low rows with a uniform high-frequency estimate to prove every complete tail-block row is below -100 |
| `Lemniscate.SineFiniteForm` | Proves tail-block dissipation for every finite set of complex coefficients |
| `Lemniscate.SineSobolevEntries` | Controls all sine entries by a summable distance kernel and H2 weights, including the shifted tail indices |
| `Lemniscate.SineTailSummability` | Proves absolute convergence of the complete tail-block energy on H2 coefficient sequences |
| `Lemniscate.SineH2Dissipation` | Passes finite-mode dissipation to the full H2 coefficient tail form, with bound -100 |
| `Lemniscate.SineConstrainedForm` | Uses the proved tail and coupling bounds to obtain -75 for the coefficient-defined block form under the explicit rotational coefficient constraint |
| `Lemniscate.EvenSineFamily` | Constructs the normalized positive even sine family from a two-sided orthonormal basis and its infinite isometric synthesis |
| `Lemniscate.PeriodicSineSpace` | Realizes that synthesis in periodic L2 with normalized Haar measure and proves Parseval normalization |
| `Lemniscate.PeriodicSineCoefficients` | Computes all Fourier coefficients of the infinite synthesis: positive even modes, negative antisymmetry, and vanishing zero and odd modes |
| `Lemniscate.PeriodicSineTail` | Separates the first mode and the infinite tail, proving their orthogonality and the exact block norm and inner product |
| `Lemniscate.PeriodicSineTailCoefficients` | Identifies the shifted tail frequencies and the absent first mode |
| `Lemniscate.SineSecondCoefficients` | Characterizes H2 coefficient sequences by the second derivative multiplier for every positive frequency offset |
| `Lemniscate.PeriodicSineH2` | Constructs the actual weak second derivatives with the circle scale and proves both directions of the H2 characterization for the full sine family and its tail |
| `Lemniscate.PeriodicSineConstraint` | Constructs a nonzero periodic L2 constraint vector and identifies its orthogonality with the coefficient constraint |
| `Lemniscate.PeriodicSineBlockH2` | Identifies the block's exact H2 domain and expresses coefficient-form dissipation using actual L2 mass and orthogonality |
| `Lemniscate.PeriodicSineRotation` | Identifies the constraint vector, up to a proved nonzero scalar, with the derivative of a profile having the explicit Fourier data, including vanishing odd modes |
| `Lemniscate.PeriodicSineProfile` | Expresses the coefficient constraint as orthogonality to q q' under the explicit Fourier hypotheses |
| `Lemniscate.PeriodicSineJets` | Proves all classical derivatives of normalized sine modes and the actual fourth-order expression on them |
| `Lemniscate.PeriodicSineMatrix` | Identifies every actual L2 mode pairing with the certified sine matrix, retaining the Fourier and period hypotheses |
| `Lemniscate.PeriodicSinePolynomials` | Constructs smooth first-mode/tail polynomials and proves their derivatives and differential-operator action |
| `Lemniscate.SineBlockFormLimit` | Proves convergence of both finite cross terms and the complete tail form to the infinite coefficient block |
| `Lemniscate.PeriodicSineFiniteEnergy` | Identifies finite polynomial differential energy with the block matrix form, including both complex cross terms |
| `Lemniscate.PeriodicSineApproximation` | Proves convergence of the functions and their first two actual weak derivatives without requiring H4 regularity |
| `Lemniscate.PeriodicSineEnergy` | Identifies the full H2 differential energy with the coefficient form and proves constrained -75 dissipation for arbitrary weak derivative witnesses |
| `Lemniscate.PeriodicSineProfileEnergy` | Restores the paper's curvature potential and the actual q q' orthogonality constraint in the H2 energy bound |
| `Lemniscate.PeriodicSineOperatorEnergy` | Transfers the -75 bound to the genuine H4 linearized operator, conditionally on the stated profile identities |
| `Lemniscate.PeriodicSineSector` | Reconstructs every Fourier-defined even sine function from its first mode and l2 tail and proves the operator bound for the entire subspace without an assumed representation |
| `Lemniscate.PeriodicCosineSector` | Reconstructs every Fourier-defined even cosine function, including the separately normalized constant mode, and proves -21/4 dissipation for the entire subspace |
| `Lemniscate.PeriodicReflection` | Constructs Fourier reflection as an actual L2 isometry, proves that it preserves H4, and identifies its action on the weak derivatives |
| `Lemniscate.PeriodicReflectionOperator` | Proves reflection identities for multiplication on all of L2 and commutation with the actual H4 operator for an even C2 coefficient |
| `Lemniscate.PeriodicReflectionSplit` | Splits every L2 or H4 function into orthogonal reflection parts, identifies their Fourier subspaces, and transfers the rotation constraint to the sine part |
| `Lemniscate.PeriodicEvenEnergy` | Proves vanishing of operator cross terms and combines the complete cosine and sine bounds into -21/4 dissipation for every even-frequency H4 function orthogonal to rotation, under the explicit profile hypotheses |
| `Lemniscate.PeriodicRotationDomain` | Constructs all four weak derivatives of q q' from the profile ODE, proves actual H4 membership, and proves that the defined H4 operator annihilates it using the first integral |
| `Lemniscate.CoefficientMajorant` | Uniform exponential coefficient bound and the comparison between sum and difference frequency indices |
| `Lemniscate.EntryMajorant` | Uniform off-diagonal entry bounds for both signs in the positive-frequency formula and for nonzero cosine rows |
| `Lemniscate.MatrixTailSeries` | Absolute convergence and exact rational upper bounds for complete upper tails of those rows |
| `Lemniscate.CosineTail` | Includes the normalized zero mode, proves symmetry and lower-tail bounds, and covers every cosine row |
| `Lemniscate.WeightedCosineTail` | Proves positivity of the paper's weights and controls the complete weighted tail used in its finite row certificates |
| `Lemniscate.CosineLowRows` | Connects all nine rational comparisons to convergent infinite weighted rows of the coefficient-defined cosine matrix |
| `Lemniscate.CosineHighEntries` | Bounds every actual weight ratio toward lower frequencies and the even-frequency cosine diagonal |
| `Lemniscate.CosineHighRows` | Connects complete high rows to the certified quartic and proves the uniform bound for every even-frequency cosine row |
| `Lemniscate.CosineFiniteForm` | Proves dissipation of the full coefficient-defined even-frequency cosine matrix for every finite set of complex modes |
| `Lemniscate.SobolevEntryBounds` | Controls matrix entries by H2 frequency weights and a summable distance kernel |
| `Lemniscate.SobolevKernel` | Proves a uniform complete-row bound for that kernel, including both frequency directions and the diagonal |
| `Lemniscate.SobolevSummability` | Proves absolute convergence of the infinite cosine energy for H2-weighted coefficient sequences |
| `Lemniscate.SobolevDissipation` | Passes finite-mode dissipation to H2-weighted sequences and checks the actual even-frequency weight convention |
| `Lemniscate.EvenCosineFamily` | Constructs the normalized cosine family from a two-sided orthonormal family and proves that infinite synthesis preserves the Hilbert-space norm |
| `Lemniscate.PeriodicCosineSpace` | Realizes the coefficient sequences as periodic L2 functions with normalized Haar measure, computes individual mode Fourier coefficients, and bounds coefficient energy by the function's L2 norm |
| `Lemniscate.PeriodicCosineCoefficients` | Computes the Fourier coefficients of the infinite synthesis: the zero mode, positive even modes, reflection symmetry, and vanishing odd modes |
| `Lemniscate.CosineSecondCoefficients` | Characterizes the H2 coefficient domain by square summability of both the original sequence and its second-frequency multiplier |
| `Lemniscate.PeriodicSecondCandidate` | Constructs the angular second-derivative candidate in periodic L2, proves its complete Fourier multiplier identity and symmetry, and proves convergence of the finite graph approximations |
| `Lemniscate.CosineModeDerivatives` | Identifies concrete representatives of the L2 modes and proves classical first and second derivatives of finite cosine sums, with the circle-coordinate scale explicit |
| `Lemniscate.PeriodicClassicalFourier` | Proves Fourier differentiation for arbitrary classical periodic functions, including the zero mode and endpoint cancellation |
| `Lemniscate.PeriodicWeakSecond` | Proves the second-derivative integration-by-parts identity for H2 cosine functions against all periodic C2 tests, with the period scale explicit |
| `Lemniscate.PeriodicWeakUniqueness` | Proves equivalence between the weak second-derivative test identity and the complete Fourier multiplier identity, and uniqueness in L2 |
| `Lemniscate.PeriodicWeakFirst` | Defines first weak derivatives using all periodic C1 tests, proves their Fourier characterization and uniqueness, and checks the integration-by-parts sign |
| `Lemniscate.PeriodicDerivativeChain` | Constructs the first L2 derivative from an L2 weak second derivative and proves equivalence with two successive weak derivatives |
| `Lemniscate.PeriodicH2Fourier` | Characterizes periodic H2 membership by the full Fourier sequence with the physical frequency weight, for every positive period |
| `Lemniscate.PeriodicCosineH2` | Identifies the weighted cosine sequence domain with actual periodic H2 membership in both directions and applies the coefficient energy bound on that domain |
| `Lemniscate.PeriodicFourierProducts` | Proves Fourier coefficient linearity and the exact frequency shift caused by multiplication by a Fourier mode |
| `Lemniscate.PeriodicProfileIdentity` | Derives the Fourier coefficients of the fourth power of a profile from its ODE and first integral, including its mean; identification of the Jacobi profile remains required |
| `Lemniscate.PeriodicSymmetricExpression` | Checks the actual fourth-order differential expression in real coordinates and derives its two-sided Fourier matrix under explicit profile hypotheses |
| `Lemniscate.PeriodicCosineJets` | Constructs all classical derivatives of the normalized cosine modes, identifies their L2 representatives, and computes the expression's action on them |
| `Lemniscate.PeriodicCosineMatrix` | Proves the positive and exceptional zero-mode L2 matrix formulas for the differential expression, assuming reflection symmetry of the coefficient's Fourier sequence |
| `Lemniscate.PeriodicMatrixIdentification` | Identifies these actual L2 matrix entries with the matrix used in the arithmetic proofs, conditional on the explicit Fourier coefficient formula and period relation |
| `Lemniscate.PeriodicCosinePolynomials` | Constructs finite cosine polynomials and all their classical derivatives, proves their L2 norm formula, and checks linearity of the differential expression |
| `Lemniscate.PeriodicFiniteEnergy` | Transfers the certified matrix dissipation to the actual L2 pairing with the differential expression on finite polynomials |
| `Lemniscate.PeriodicMultiplication` | Constructs bounded multiplication operators on periodic L2, identifies their integral pairings, and proves continuity of the H2 energy |
| `Lemniscate.PeriodicIntegrationByParts` | Uses periodic integration by parts to identify the classical fourth-order energy with the form involving only two derivatives |
| `Lemniscate.PeriodicDerivativeGraph` | Controls the first weak derivative by the zeroth and second derivatives and proves its convergence from convergence of those two quantities |
| `Lemniscate.PeriodicH2Approximation` | Proves simultaneous L2 convergence of finite cosine polynomials and their first two derivatives |
| `Lemniscate.PeriodicH2Energy` | Identifies the actual weak-derivative energy with the convergent coefficient form and proves cosine-subspace H2 dissipation under explicit coefficient hypotheses |
| `Lemniscate.PeriodicProfileEnergy` | Rewrites that H2 form in the paper's curvature-profile variables and proves its dissipation, retaining the profile ODE, Fourier formula and period relation as hypotheses |
| `Lemniscate.PeriodicSkewEnergy` | Proves symmetry of multiplication by a real coefficient on L2 and cancellation of the real energy of the classical periodic first-order skew correction |
| `Lemniscate.PeriodicLinearEnergy` | Splits the paper's linearized differential expression into symmetric and skew parts, identifies its classical real energy, and derives cosine-subspace dissipation under the explicit profile and Fourier hypotheses |
| `Lemniscate.PeriodicWeakCalculus` | Proves integration by parts between L2 weak derivatives, the product rule for real C1 coefficients, and zero real energy of the corresponding first-order skew term |
| `Lemniscate.PeriodicWeakOperatorEnergy` | Defines the four-weak-derivative domain and proves symmetric and linear-expression energy identities and conditional cosine dissipation on four successive L2 weak derivatives |
| `Lemniscate.PeriodicH4Domain` | Constructs that H4 domain as a complex submodule of L2, proves uniqueness of all derivative witnesses, and bundles the four derivative maps as linear maps |
| `Lemniscate.PeriodicH4Operator` | Defines the symmetric and linearized expressions as linear maps from the explicit H4 domain to L2 and proves their energy identity and conditional cosine-subspace dissipation |
| `Lemniscate.PeriodicFormalAdjoint` | Proves fourth-order, divergence and skew Green identities on H4, checks the formal adjoint expression, and proves the two-operator pairing identity; maximal-domain identification is proved in the later regularity module |
| `Lemniscate.PeriodicH4Density` | Shows every Fourier basis mode belongs to H4, proves the domain is dense in L2, and proves that pairing against this domain separates L2 functions |
| `Lemniscate.PeriodicHilbertAdjoint` | Packages the operator as a Mathlib LinearPMap, proves inclusion of the formal expression in its genuine Hilbert adjoint and agreement on H4, establishes adjoint closedness and density, and proves closability of the original operator |
| `Lemniscate.PeriodicEllipticBootstrap` | Proves a frequency estimate and gains two L2 weak derivatives from a fourth-order distributional equation with L2 data of order at most two |
| `Lemniscate.PeriodicAdjointFourier` | Computes the canonical H4 derivatives of every Fourier mode and derives the genuine adjoint's Fourier equation for arbitrary elements of its maximal domain |
| `Lemniscate.PeriodicAdjointRegularity` | Gains H2 and then H4 regularity, proves that the maximal Hilbert adjoint domain is exactly H4, and identifies the adjoint with the formal expression for real C2 coefficients |
| `Lemniscate.PeriodicOperatorClosed` | Proves the reverse adjoint identity by the same regularity argument and establishes closedness of the original operator on its stated H4 domain |
| `Lemniscate.PeriodicBoundedMultiplier` | Constructs bounded multipliers on the complete Fourier Hilbert basis of periodic L2 and proves the operator norm bound |
| `Lemniscate.PeriodicH4Fourier` | Characterizes H4 by square summability of the fourth Fourier multiplier, constructing the intermediate weak derivatives |
| `Lemniscate.PeriodicPrincipalResolvent` | Constructs the principal resolvent at every positive real parameter, proves its L2 norm bound, range in the actual H4 domain, and both inverse identities for lambda + 4 D^4 |
| `Lemniscate.PeriodicCompactMultiplier` | Shows that an absolutely summable Fourier symbol gives an operator norm convergent rank-one expansion and a compact L2 operator |
| `Lemniscate.PeriodicPrincipalCompact` | Proves summability of the principal symbol, including the zero mode, and compactness of the principal resolvent |
| `Lemniscate.PeriodicResolventSmoothing` | Bounds the first and second weak derivatives of the principal resolvent at p squared and identifies them with the H4 derivative witnesses |
| `Lemniscate.PeriodicResolventPerturbation` | Bounds the complete lower-order perturbation composed with the principal inverse and proves the full shifted-operator factorization on H4 |
| `Lemniscate.PeriodicFullResolvent` | Constructs a compact bounded two-sided inverse of the full variable-coefficient operator at an explicit positive parameter for every continuous coefficient triple |
| `Lemniscate.PeriodicComplexShift` | Factors every complex shift on the actual H4 domain through the constructed inverse and a compact bounded L2 operator |
| `Lemniscate.PeriodicFredholmAlternative` | Proves that every complex parameter either has a nonzero H4 eigenvector or a compact bounded two-sided inverse; identifies the unbounded-operator spectrum with its eigenvalues |
| `Lemniscate.RotationKernel` | The rotation-mode differential identity for functions satisfying the stated ODE and first integral |
| `Lemniscate.ComplexRows` | The weighted estimate for complex coefficients and Hermitian entry norms |
| `Lemniscate.PhysicalTime` | The exact logarithmic-time to physical-time decay identity and positive waiting time |

The local `audit/results/build.json` records which exact source hashes have successfully
compiled. A source file's presence is not evidence that it compiled. Failed or
not-yet-built files remain work in progress. Published snapshots contain
`audit/results/verification.json`, which records source hashes and exit codes
without machine-specific paths. These records describe only the listed modules.

## Build

The portable build is `lake build`. Lean and all transitive dependencies are
pinned in `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.
The [first successful Linux CI run](https://github.com/qumiha151-wq/lemniscate-stability-lean/actions/runs/38388577006)
built commit `cda497be4b429fe98bbc5c42d4c03b2f22ba3a93` and passed the axiom
audit. Each subsequent commit needs its own check. The local offline build
uses the already installed matching Mathlib cache:

```text
python scripts/build_cached.py
```

The local runner compiles in a temporary directory because Lean's module-path
check rejects the current Windows directory containing Chinese characters.
Source hashes, exit codes and logs are recorded. It does not use `sorry`,
`admit`, added mathematical axioms, or `native_decide` to stand in for proofs.

After building, check the key declarations' actual axiom dependencies:

```text
lake env lean Lemniscate/AxiomAudit.lean > axiom-audit.log
python scripts/check_axioms.py axiom-audit.log
```

The GitHub workflow performs these steps on Linux. It uses the
[official Lean action](https://github.com/leanprover/lean-action), pinned to a commit.
The workflow's success still does not establish the missing PDE theorem.

The independent, exact Python recomputations require only Python's standard
library and may be run as follows:

```text
python audit/recompute/audit_refined_all.py
python audit/recompute/verify_expanded_algebra.py
python audit/recompute/expand_arithmetic.py --output-dir tmp/current-trial-check
```

The first checks the original Galerkin trial; the third checks the fixed rational
trial in the current revised manuscript and its 177-times-residual error budget.
Generated decimal displays
are for reading only; inequality decisions use exact rational arithmetic.

## Remaining work

The following obligations are still required for the original goal:

- Complete kernel-checked arithmetic certificates and their soundness proofs,
  including actual Fourier coefficient enclosures, transformed matrices and
  every infinite tail.
- Identify the concrete Jacobi profile and its Fourier/theta parameters in the
  defined periodic operator; extend the completed conditional cosine energy
  connection to every required subspace. The sine coefficient domain is now
  identified with actual periodic H2, and its constraint with orthogonality to
  q q' under explicit profile Fourier hypotheses. The complete sine form is
  identified with the actual H2 differential energy, and its -75 bound is
  transferred to the H4 operator. Both even-frequency subspaces are complete,
  and their reflection splitting now gives -21/4 dissipation for their entire
  sum under the rotation constraint. The concrete Jacobi profile must still
  be shown to satisfy all Fourier and period hypotheses. The odd-frequency
  subspace now has -6 dissipation for the actual periodic H4 operator. Orthogonal
  frequency splitting combines it with the even subspaces to give -21/4
  coercivity on the whole rotation-orthogonal H4 complement. The nonzero
  rotation vector and this coercivity instantiate the neutral-mode argument;
  the proved Fredholm alternative then gives the single-period full spectral
  gap, still under the explicit profile Fourier and period hypotheses.
  All odd coefficient rows and their finite complex quadratic forms now have
  the stated gaps on the entire half interval, including their infinite row
  tails. Absolute convergence of the full double series and its extension to
  the infinite H2 coefficient form are also proved. That form is identified
  with the actual periodic energy at zero parameter. The actual Bloch matrix
  is now identified for all real parameters; four-derivative approximation
  transfers the -1 bound to every odd-subspace H4 function for parameters in
  [0,1/2]. The transformed even Bloch subspace remains.
- Establish sectoriality, the Bloch decomposition and the analytic perturbation
  argument in Lean. Closedness and equality of the
  maximal adjoint domain with H4 are proved for the stated real C2 coefficients.
  A compact bounded inverse of the full variable-coefficient operator is now
  constructed at an explicit positive parameter, with both inverse identities
  on H4. The Fredholm alternative connects this to the entire spectrum:
  every spectral point is an eigenvalue. A rank-one perturbation now constructs
  the exact normalized adjoint zero vector in H4. Its reflection parity,
  even Fourier support and reality are proved, as is the exact bounded neutral
  transform with its H4 inverse and orthogonal-compression formula.
  The actual Householder transform now has a proved positive denominator,
  involution and H4 preservation; its combination with the exact neutral
  transform has zero row and column corresponding to the fixed Fourier mode, also in the symmetric pairing.
  The actual quartic Bloch polynomial, its reflection parity and exact center
  and cross-factor cancellations are proved. The adjoint trial's L2 error is
  bounded by its residual norm divided by 75, and its angular H4 error by
  177 times that residual norm. The complete concrete residual and its resulting
  squared H4 error below 62658e-30 are now proved.
  Vector truncation estimates, complex angular resolvent estimates and uniform negativity of
  the transformed even Bloch subspace still need proof. The remaining
  argument may use the projection onto the fixed Fourier mode and quadratic forms directly; an
  explicit copy of the paper's basis-change matrix is not a requirement.
- Formalize the relevant parabolic existence, regularization and normal
  stability results, or use already proved Lean theorems with matching
  hypotheses; cited papers cannot be inserted as new axioms.
- Formalize curvature-to-graph control and the original geometric convergence
  theorem, including all quantifiers and rates.
- Verify the full project and its axiom dependencies, then publish to the
  user-authorized public GitHub repository `lemniscate-stability-lean`.
- Cross-check the paper against the completed Lean statements and their actual
  hypotheses; correct the paper further whenever the comparison reveals a
  mathematical discrepancy.

This is a work-in-progress formalization, not a completion certificate for the paper.

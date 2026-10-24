# Lemniscate stability: review and Lean formalization in progress

**The full PDE theorem is not yet formalized. This repository must not be
described as a complete Lean proof of the paper.**

The target is the 22-page PDF supplied by the user, titled *Local asymptotic
stability of Bernoulli lemniscates under the free elastic flow*. Its SHA-256 is
`36c9336c9f1e002cde61b856650ba22b6320b9fa3a5b72e30b338d5d6f13ee07`.
The matched original standalone TeX has SHA-256
`8e8e5f3419bd2c8a0be99e16dd4e980aaf4bc4dad247cc8b51018b6eddda7d84`.

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
| `Lemniscate.OddArithmetic` | All 84 odd-sector Bernstein comparisons and 12 zero-parameter comparisons, computed from rational formulas |
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
| `Lemniscate.OddFiniteForm` | Applies the full row bounds to every finite complex coefficient vector, with gaps 1 and 6; the infinite Sobolev form and nonzero Bloch operator connection remain |
| `Lemniscate.QuarticTail` | A general quartic estimate for every real argument beyond a cutoff |
| `Lemniscate.HighFrequency` | Instantiates that estimate with all four actual rational high-frequency quartics |
| `Lemniscate.GeometricTails` | Convergence and exact sums for the first three geometric moment tails |
| `Lemniscate.HigherGeometricMoments` | Convergence and exact rational sums for moments four through six |
| `Lemniscate.FourierEnclosure` | Monotonicity and rational enclosures for the positive Fourier coefficient formula, conditional on parameter bounds |
| `Lemniscate.FourierSeries` | Convergence and uniform tail bounds for that series, and the constant coefficient's full rational enclosure |
| `Lemniscate.CosineMatrix` | Connects the convergent coefficient formulas to the actual rational cosine-entry intervals, conditional on parameter bounds |
| `Lemniscate.NomeBounds` | Proves the coarse interval for exp(-pi) using pi bounds and the exponential series remainder |
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
| `Lemniscate.PeriodicSineSector` | Reconstructs every Fourier-defined even sine function from its first mode and l2 tail and proves the operator bound for the entire sector without an assumed representation |
| `Lemniscate.PeriodicCosineSector` | Reconstructs every Fourier-defined even cosine function, including the separately normalized constant mode, and proves -21/4 dissipation for the entire sector |
| `Lemniscate.PeriodicReflection` | Constructs Fourier reflection as an actual L2 isometry, proves that it preserves H4, and identifies its action on the weak derivatives |
| `Lemniscate.PeriodicReflectionOperator` | Proves reflection identities for multiplication on all of L2 and commutation with the actual H4 operator for an even C2 coefficient |
| `Lemniscate.PeriodicReflectionSplit` | Splits every L2 or H4 function into orthogonal reflection parts, identifies their Fourier sectors, and transfers the rotation constraint to the sine part |
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
| `Lemniscate.PeriodicH2Energy` | Identifies the actual weak-derivative energy with the convergent coefficient form and proves cosine-sector H2 dissipation under explicit coefficient hypotheses |
| `Lemniscate.PeriodicProfileEnergy` | Rewrites that H2 form in the paper's curvature-profile variables and proves its dissipation, retaining the profile ODE, Fourier formula and period relation as hypotheses |
| `Lemniscate.PeriodicSkewEnergy` | Proves symmetry of multiplication by a real coefficient on L2 and cancellation of the real energy of the classical periodic first-order skew correction |
| `Lemniscate.PeriodicLinearEnergy` | Splits the paper's linearized differential expression into symmetric and skew parts, identifies its classical real energy, and derives cosine-sector dissipation under the explicit profile and Fourier hypotheses |
| `Lemniscate.PeriodicWeakCalculus` | Proves integration by parts between L2 weak derivatives, the product rule for real C1 coefficients, and zero real energy of the corresponding first-order skew term |
| `Lemniscate.PeriodicWeakOperatorEnergy` | Defines the four-weak-derivative domain and proves symmetric and linear-expression energy identities and conditional cosine dissipation on four successive L2 weak derivatives |
| `Lemniscate.PeriodicH4Domain` | Constructs that H4 domain as a complex submodule of L2, proves uniqueness of all derivative witnesses, and bundles the four derivative maps as linear maps |
| `Lemniscate.PeriodicH4Operator` | Defines the symmetric and linearized expressions as linear maps from the explicit H4 domain to L2 and proves their energy identity and conditional cosine-sector dissipation |
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
python audit/recompute/expand_arithmetic.py
```

The first checks the original Galerkin trial; the third checks the later fixed
rational trial and reproduces its expanded appendix. Generated decimal displays
are for reading only; inequality decisions use exact rational arithmetic.

## Remaining work

The following obligations are still required for the original goal:

- Complete kernel-checked arithmetic certificates and their soundness proofs,
  including actual Fourier coefficient enclosures, transformed matrices and
  every infinite tail.
- Identify the concrete Jacobi profile and its Fourier/theta parameters in the
  defined periodic operator; extend the completed conditional cosine energy
  connection to every required sector. The sine coefficient domain is now
  identified with actual periodic H2, and its constraint with orthogonality to
  q q' under explicit profile Fourier hypotheses. The complete sine form is
  identified with the actual H2 differential energy, and its -75 bound is
  transferred to the H4 operator. Both even-frequency sectors are complete,
  and their reflection splitting now gives -21/4 dissipation for their entire
  sum under the rotation constraint. The concrete Jacobi profile must still
  be shown to satisfy all Fourier and period hypotheses; the odd-frequency
  and Bloch sectors must still be connected to the full spectral estimate.
  All odd coefficient rows and their finite complex quadratic forms now have
  the stated gaps on the entire half interval, including their infinite row
  tails. Their extension to the infinite H2 form domain and identification
  with the nonzero-parameter Bloch differential operator remain.
- Establish sectoriality, the Bloch decomposition and the analytic perturbation
  argument in Lean. Closedness and equality of the
  maximal adjoint domain with H4 are proved for the stated real C2 coefficients.
  A compact bounded inverse of the full variable-coefficient operator is now
  constructed at an explicit positive parameter, with both inverse identities
  on H4. The Fredholm alternative connects this to the entire spectrum:
  every spectral point is an eigenvalue. Estimates in complex angular
  regions and the Bloch and finite-rank modifications remain.
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

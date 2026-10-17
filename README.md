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
- Define the concrete periodic differential operator and its Sobolev domain;
  connect finite Fourier estimates to the infinite-dimensional quadratic form.
- Establish the operator-theoretic bridge, Bloch decomposition and analytic
  perturbation argument in Lean.
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

import Lemniscate.LemniscateStability
import Lemniscate.PeriodicCoverUpperBound
import Lemniscate.ShortCertificateSummary

/-! Geometric stability of finite Bernoulli lemniscate covers.

## Reproducing the complete proof

This repository contains Lean source only. Its `lakefile.lean` is the build
configuration, not a mathematical hypothesis. Install Git and elan (the Lean
toolchain manager), download and extract this repository's source ZIP, and run
the following commands from the extracted directory:

    elan toolchain install leanprover/lean4:v4.33.1
    lake +leanprover/lean4:v4.33.1 update
    lake +leanprover/lean4:v4.33.1 exe cache get
    lake +leanprover/lean4:v4.33.1 build

The explicit toolchain argument replaces a separate `lean-toolchain` file.
Mathlib is pinned in `lakefile.lean` to the revision stated below; its inherited
dependencies are resolved from that revision. The cache command downloads
compiled library dependencies only. The final command compiles this complete
project, including `Lemniscate/AxiomAudit.lean`. That file rejects any project
declaration depending on axioms other than `propext`, `Classical.choice`, and
`Quot.sound`; in particular `sorryAx` is rejected. A successful audit is printed
in the build output. No numerical exploration program, local manuscript,
unpublished source, or precompiled project artifact is required.

For a fixed version, use GitHub's `Code` -> `Download ZIP` on that commit, or
`https://github.com/qumiha151-wq/lemniscate-stability-lean/archive/COMMIT.zip`,
replacing COMMIT by the full commit hash. The ZIP contains the entire source
tree for that version. Keep its sources together when rebuilding.

## Manuscript-to-Lean correspondence

All declaration names below have prefix `Lemniscate.` unless otherwise stated.
File paths are relative to this repository. The correspondence uses statement
names rather than page numbers so that pagination does not affect it.

* Main theorem, "Local stability": `lemniscate_stability` in
  `Lemniscate/LemniscateStability.lean`. It constructs the actual arclength
  coordinate and proves `LemniscateStabilityStatement`, defined in
  `Lemniscate/LemniscateStabilityStatement.lean`. The latter definition is the
  target proposition, not an assumption that it holds. Its quantifiers fix
  the base radius, rate radii and uniform constants before the initial curve.
  The conclusion includes a global jointly smooth solution and identifies
  every given smooth geometric solution with the same initial immersion.

* Geometric definitions: `IsFreeElasticFlow` in `FreeElasticFlow.lean` uses
  the actual right time derivative, immersion condition and projected normal
  velocity. The plane is represented by the complex numbers. The reference
  curve is `bernoulliCurve`; `lemniscateReference` is its arclength form.
  `lemniscateLength`, `lemniscateCurvatureDeviation`, and
  `lemniscateInitialScale` are the paper's reference length, curvature-profile
  distance and initial scale. Increasing smooth real lifts with smooth inverses
  and the prescribed period shift represent the oriented circle
  diffeomorphisms. `ContDiffOn` on the closed time half-space includes the
  initial endpoint, whereas the convergence asserted is spatial C-infinity.

* Spectral theorem: `paper_periodic_cover_spectrum` in
  `PeriodicProfileCoverSpectrum.lean` proves the one-dimensional rotational
  kernel, absence of generalized zero eigenvectors and the nonzero spectral
  bound on every positive cover. `paper_cover_sharp_gap_bounds` in
  `PeriodicCoverUpperBound.lean` supplies actual nonzero eigenvalues and both
  bounds of order M^(-2). The profile identities in these analytic statements
  are constructed for the geometric reference in `BernoulliArclength.lean`,
  `BernoulliProfileIdentification.lean`, and `BernoulliReferenceLength.lean`;
  they are discharged in the closed main proof.

* Single-period coercivity: `paper_h4_operator_rotation_complement_dissipative`
  in `PeriodicFullEnergy.lean` and `paper_h4_operator_sine_dissipative` in
  `PeriodicSineOperatorEnergy.lean`. Both relevant negative bounds require
  orthogonality to the rotational mode; the sine estimate does not apply to
  that neutral vector itself.

* Exact-to-finite spectral comparison: `short_neutral_telescope_bounds`,
  `short_actual_component_form_errors`, and
  `short_reduced_bernstein_difference` in `ShortActualNeutralBounds.lean`,
  `ShortActualFormComparison.lean`, and
  `ShortActualReducedFormComparison.lean`. `short_actual_bernstein_form_error`
  in `ShortActualBernsteinComparison.lean` controls the actual forms.
  Integer interval arithmetic and the finite comparisons are in the
  `ShortSchur*.lean` modules; the namespace there is
  `Lemniscate.CoarseArithmetic`. `short_thirty_five_rows`,
  `short_finite_cross_square_bound`, and `short_finite_high_rows` certify the
  displayed block thresholds using kernel reduction. The five displayed
  outward-rounded summary rows and the worked second-row calculation are checked by
  `CoarseArithmetic.short_certificate_summary` in
  `ShortCertificateSummary.lean`. Infinite geometric tails,
  polynomial coercivity and H4 Fourier density are proved separately before
  `paper_uniform_bloch_spectral_bound` in `PeriodicBlochSpectrumBound.lean`.

* The proposition "Stability of the modulated equation" combines the following
  previously proved analytic conclusions. Mixed nonlinear estimate:
  `paper_periodic_cover_modulated_tame_data` in
  `BernoulliCoverModulationData.lean`. The real phase-constrained global
  solution and its all-time H2 exponential estimate are in
  `bernoulli_cover_modulated_real_global_solution`,
  `BernoulliParabolicGlobalSolution.lean`. Together with geometric entry this
  gives the paper's H2 orbital-stability consequence. The formal construction
  uses compatible local maximal-regularity solutions and energy estimates;
  the manuscript's weighted half-line formulation expresses the same
  small-data stability conclusion.

* Positive-time smoothing with constants controlled by low-order data:
  `bernoulli_parabolic_smoothing` and `bernoulli_parabolic_global_smoothing`
  in `BernoulliParabolicSmoothing.lean` and
  `BernoulliParabolicGlobalSmoothing.lean`. Initial-endpoint regularity for
  smooth data is separate: `bernoulli_parabolic_endpoint_smoothing`,
  `banach_scale_time_smooth`, and `bernoulli_evolution_joint_smooth` in
  `BernoulliParabolicEndpointSmoothing.lean`,
  `BanachScaleTimeRegularity.lean`, and
  `BernoulliEvolutionJointSmoothness.lean`.

* Geometric entry for immersed multiple covers:
  `periodic_normal_graph_h2_entry` in `PeriodicNormalGraphH2Entry.lean` and
  `bernoulli_initial_normal_graph` in `BernoulliInitialNormalGraph.lean`.
  These construct the parameter change, graph and phase condition and bound
  its H2 size by the curvature-profile error. They work on the parameter
  circle and do not assume that the reference image is embedded.

* Physical flow and limiting shape: `bernoulli_physical_graph_stability`
  in `BernoulliPhysicalGraphStability.lean` fixes one limiting rotation.
  `lemniscate_given_flow_identification` in `LemniscateGivenFlow.lean`
  identifies the normal graph with any given geometric flow.
  `lemniscate_convergence_actual_length` in `LemniscateLengthConvergence.lean`
  gives actual-length normalization. The main theorem combines these with
  the time change, the base-neighborhood rates and the uniform rates; all
  orders use the same translation, limiting rotation and reparametrizations.

The exact manuscript revision is identified by the SHA-256 below. Formal
verification establishes the propositions encoded by these definitions; the
definitions and this correspondence make their mathematical interpretation
available for independent inspection.

Current manuscript SHA-256: c9e958ea3d851958aefc2bbdb0f997a815b478f43ae3812b5908a2cc9fcff578
Checked environment: Lean 4.33.1 and Mathlib revision
0df444a360eaa60ab8c11dca51a86af692955474.
Only compiled Lean source is published.
-/

#check Lemniscate.lemniscate_stability

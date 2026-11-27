import Migration.IntrinsicForceMotion
import Migration.IntrinsicBendingPast
import Migration.MultiDiskFluxClassical
import Migration.VirialForwardDisk
import Migration.SublevelMigrationFloor
import Migration.SublevelFixedRadius
import Migration.LowDefectMaterialSlab
import Migration.LowDefectMaterialCorrection
import Migration.LowDefectDiskComparison
import Migration.DefectFourHull
import Migration.CubicTangencyFlux
import Migration.FlatProjectionZeros
import Migration.TrueEndpointTransit
import Migration.EndpointEnergyTransit
import Migration.AngularReconstruction
import Migration.AngularElasticFlow
import Migration.AngularMeshSeparation
import Migration.AngularWienerBound
import Migration.AngularSpectralExample
import Migration.AngularFirstVelocity
import Migration.AngularFourierResidual
import Migration.AngularSlabConstants
import Migration.AngularFourierSemantics
import Migration.AngularMeanDrift
import Migration.AngularMigrationTest
import Migration.AngularModeEnvelope
import Migration.AngularExcursionBarrier
import Migration.OrientedAreaTransit
import Migration.RotatingRadius
import Migration.ProjectedHeightTransit
import Migration.PhysicalViewingAngle
import Migration.UniformHullGap
import Migration.BernoulliPerturbation
import Migration.GapCapSweep
import Migration.RecurringMigration
import Migration.SimilarityHull
import Migration.SimilarityClock
import Migration.EscapingHulls
import Migration.SimilarityFlow
import Migration.DiskDissipation
import Migration.SelfSimilarEscape
import Migration.StressAngle
import Migration.SeparatedHeight
import Migration.ForwardShortCore
import Migration.RoundPartitionCost
import Migration.NearRoundDisk
import Migration.TranslatorCaps
import Migration.FiniteRotation
import Migration.CenterInterior
import Migration.EnergyTransit
import Migration.TwoEndpointCost
import Migration.EndpointMass
import Migration.DilationDefect
import Migration.Criterion

/-!
Migration question: PARTIAL RESULTS; GENERAL MIGRATION UNRESOLVED.

The main verified statement `FreeElasticFlow.boundedProfile_migration_iff`
characterizes translated homothetic crossing for a bounded scalar height
profile with attained maximum. It does not establish existence of a closed
free-elastic-flow expander with that profile.

The actual-coordinate geometry modules also derive the normal-distance
regression center, positive energy/support integrals, force balance and
the exact dilation-defect decomposition. On an actual normal free elastic
flow the cutoff modules bound the time and dissipation needed to change
two height-weighted lengths. Closedness supplies a lower bound for each
weighted length from two sampled heights on a slice. The explicit clipped sine cutoff and the bending dissipation identity give a necessary inequality for the widths and actual energies of two strictly separated endpoint curves. The forward-time theorem includes initial data by right continuity. A tangent excursion gives E W ≥ 2 for every slice. The energy-scale theorem therefore bounds T E(0)^3 (E(0)-E(T)) below by 16/(pi+2)^2.

For true closed homothetic expanders of rate a and centered radius at most R, the projected elastic stress proves that a R^4 ≤ 2 puts the center in the interior of the convex hull. This rules out migration in that radius range.

For a profile assembled from finitely many nontrivially rotated copies of an arclength block, every similarity slice has the same arclength centroid and contains it in its convex hull. Two such slices cannot occupy disjoint convex sets. The dense-pitch construction supplies these blocks as described in Research/RotatingProfiles.md.

For an actual closed free elastic flow with a translating portion, the force balance and the material arclength measure give a lower bound on the energy dissipated by the closing portion. The hypotheses and the distinction between the Lean results and the geometric arguments are listed in Research/TranslatorCaps.md.

Run this independent project from its own directory:
  lake +leanprover/lean4:v4.33.1 update
  lake +leanprover/lean4:v4.33.1 exe cache get
  lake +leanprover/lean4:v4.33.1 build

This project does not import the stability or length-growth projects.
-/

/-! The physical near-round fixed disk is proved in `Migration.NearRoundDisk`.
See `Research/FixedCore/FixedCoreFormalization.md` for the statements and bounds. -/

/-! The uniform short-time disk for arbitrary initial shapes and turning numbers is
proved in `Migration.ForwardShortCore`. See `Research/FixedCore/UniversalShortTimeDisk.md`. -/

/-! The centre-to-hull distance for a strictly separated pure expansion is less than one eighth of its perimeter. The directional integral, expansion-factor and elapsed-time bounds are proved in Migration.SeparatedHeight. See Research/SeparatedHeight.md for their geometric formulation and for the centre and angular-rate formula for rotating profiles. -/

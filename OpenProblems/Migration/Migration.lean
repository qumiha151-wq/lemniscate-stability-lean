import Migration.ForwardHalfplaneCost
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
weighted length from two sampled heights on a slice. The explicit clipped sine cutoff and the bending dissipation identity give a necessary inequality for the widths and actual energies of two strictly separated endpoint curves. The forward-time theorem includes initial data by right continuity.

Run this independent project from its own directory:
  lake +leanprover/lean4:v4.33.1 update
  lake +leanprover/lean4:v4.33.1 exe cache get
  lake +leanprover/lean4:v4.33.1 build

This project does not import the stability or length-growth projects.
-/

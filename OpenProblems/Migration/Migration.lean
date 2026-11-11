import Migration.Criterion

/-!
Migration question: PARTIAL REDUCTION ONLY.

The main verified statement `FreeElasticFlow.boundedProfile_migration_iff`
characterizes translated homothetic crossing for a bounded scalar height
profile with attained maximum. It does not establish existence of a closed
free-elastic-flow expander with that profile.

Run this independent project from its own directory:
  lake +leanprover/lean4:v4.33.1 update
  lake +leanprover/lean4:v4.33.1 exe cache get
  lake +leanprover/lean4:v4.33.1 build

This project does not import the stability or length-growth projects.
-/

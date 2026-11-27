import Lake
open Lake DSL

package bernoulli_migration_bridge

require migration_reduction from ".."
require lemniscate_stability from "../../.."

@[default_target]
lean_lib BernoulliBridge where
  globs := #[.andSubmodules `BernoulliBridge]

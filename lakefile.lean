import Lake
open Lake DSL

/-!
Portable Lean-only build configuration.

After installing Git and elan, extract the complete source ZIP and run:

  elan toolchain install leanprover/lean4:v4.33.1
  lake +leanprover/lean4:v4.33.1 update
  lake +leanprover/lean4:v4.33.1 exe cache get
  lake +leanprover/lean4:v4.33.1 build

The explicit toolchain selector avoids requiring a non-Lean toolchain file.
The Mathlib commit is immutable; its manifest fixes inherited dependencies.
The default target includes every project module and the enforced axiom audit.
See the comments in Lemniscate.lean for the manuscript correspondence.
-/

package lemniscate_stability

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

@[default_target]
lean_lib Lemniscate where
  globs := #[.andSubmodules `Lemniscate]

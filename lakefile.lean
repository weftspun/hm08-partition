import Lake
open Lake DSL

package «hm08-partition» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib Hm08Partition where
  roots := #[`Hm08Partition]

@[default_target]
lean_lib Main where
  roots := #[`Hm08Partition]

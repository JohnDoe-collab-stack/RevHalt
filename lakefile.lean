import Lake
open Lake DSL

package "RevHalt" where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩
  ]

require "mathlib" from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib "RevHalt" where

lean_lib "AddOn" where
  globs := #[.submodules `AddOn]

lean_lib "Complexity" where
  globs := #[.submodules `Complexity]

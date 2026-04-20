import Lake
open Lake DSL

package «fips-pub-180-4» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mdgen from git
  "https://github.com/Seasawher/mdgen" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0-rc1"

@[default_target]
lean_lib spec where

lean_lib tests where
  globs := #[.submodules `tests]

lean_exe cavp where
  root := `tests.CAVP

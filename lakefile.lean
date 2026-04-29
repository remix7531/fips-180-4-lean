import Lake
open Lake DSL

package «fips-pub-180-4» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    -- Mathlib style linters: prefixed with `weak.` so individual files can
    -- locally override via `set_option linter.style.longLine false in ...`.
    ⟨`weak.linter.style.longLine, true⟩,
    ⟨`weak.linter.style.lambdaSyntax, true⟩,
    ⟨`weak.linter.style.dollarSyntax, true⟩,
    ⟨`weak.linter.style.cdot, true⟩,
    ⟨`weak.linter.style.missingEnd, true⟩,
    ⟨`weak.linter.style.setOption, true⟩
  ]

require mdgen from git
  "https://github.com/Seasawher/mdgen" @ "v4.28.0-rc1"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.28.0-rc1"

@[default_target]
lean_lib spec where

lean_lib impl where
  globs := #[.submodules `impl]

lean_lib equiv where
  globs := #[.submodules `equiv]

lean_lib tests where
  globs := #[.submodules `tests]

lean_exe cavp where
  root := `tests.CAVPMain

lean_exe stress where
  root := `tests.Stress

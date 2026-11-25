import Lake
open Lake DSL

package «fips-pub-180-4» where
  version := v!"0.1.0"
  allowNonModules := true
  leanOptions := #[⟨`autoImplicit, false⟩]
  builtinLint := true

require mdgen from git
  "https://github.com/Seasawher/mdgen" @ "v4.36.0-rc2"

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

@[test_driver]
script testCavp args do
  let rootPackage ← getRootPackage
  let some cavp := rootPackage.findLeanExe? `cavp
    | error "The cavp test executable is missing."
  let runner ← runBuild cavp.fetch
  let rejectionChecks := rootPackage.dir / "tests" / "cavp-invalid.sh"
  let status ← Lake.env "bash" #[rejectionChecks.toString, runner.toString]
  if status != 0 then
    return status
  Lake.env runner.toString args.toArray

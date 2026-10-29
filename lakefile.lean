import Lake
open Lake DSL

def sodiumQuery (mode : String) : IO String := do
  let output ← IO.Process.output { cmd := "pkg-config", args := #[mode, "libsodium"] }
  unless output.exitCode == 0 do
    throw (IO.userError "Native crypto requires pkg-config and libsodium development files (brew install libsodium pkg-config / apt install libsodium-dev pkg-config).")
  return output.stdout.trim

-- pkg-config omits default system -L paths. Lean's bundled clang uses its own sysroot,
-- so pass the exact shared library rather than searching host directories globally.
def sodiumLinkFlags : Array String := run_io do
  let dir := System.FilePath.mk (← sodiumQuery "--variable=libdir")
  return #[(dir / nameToSharedLib "sodium").toString]

def sodiumCompileFlags : Array String := run_io do
  return ((← sodiumQuery "--cflags").splitOn " ").filter (· != "") |>.toArray

package «PlutusCore» where
  moreLinkArgs := sodiumLinkFlags
  -- add package configuration options here
  require Blaster from git "https://github.com/input-output-hk/Lean-blaster" @ "beta-lambda-cache-optimization"

extern_lib plutusCrypto pkg := do
  let dir := pkg.dir / "Cryptograph" / "FFI" / "c"
  let headers ← #["lean_plutus_crypto.h", "crypton/crypton_sha3.h", "crypton/crypton_ripemd.h",
    "crypton/crypton_bitfn.h", "crypton/crypton_align.h"].mapM fun (name : String) => inputTextFile (dir / name)
  let headerJob := Job.collectArray headers
  let objects ← #["lean_plutus_hash.c", "lean_plutus_ed25519.c", "crypton/crypton_sha3.c",
    "crypton/crypton_ripemd.c"].mapM fun (name : String) => do
      let source ← inputTextFile (dir / name)
      let source := source.zipWith (fun path _ => path) headerJob
      buildO (pkg.buildDir / "crypto" / (name ++ ".o")) source
        (#["-I", (← getLeanIncludeDir).toString] ++ sodiumCompileFlags)
        #["-O3", "-fPIC", "-fno-strict-aliasing", "-std=gnu11"] "cc" getLeanTrace
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "plutusCrypto") objects

@[default_target]
lean_lib «PlutusCore» where
  precompileModules := true
  moreLeancArgs := #["-O3"]

@[test_driver]
lean_lib «Tests» where
  -- add library configuration options here

lean_lib «Lemmas» where
  -- add library configuration options here

lean_lib «Cryptograph» where
  -- add library configuration options here

lean_exe «gen_conformance_tests» where
  srcDir := "scripts"
  root := `GenConformanceTests

-- `#prep_uplc` benchmark harness (see Benchmark/README.md).
-- Must not be precompiled: its generated cases import
-- `Tests.UPLC.ScriptEncoding.Tests`, whose native code would then have to be built.
lean_lib «Benchmark»

lean_exe «bench_prep_uplc» where
  root := `Benchmark.PrepUplc.Driver.Main

-- Standalone native evaluator: no elaboration or #prep_uplc in the timed operation.
lean_exe «bench_cek» where
  root := `Benchmark.Cek.Main
  moreLeancArgs := #["-O3"]

lean_exe «test_crypto_ffi» where
  root := `Benchmark.Cek.CryptoProbe
  moreLeancArgs := #["-O3"]

-- Differential parser checks compare ASTs without running generated programs.
lean_exe «test_flat_decode» where
  root := `Benchmark.Cek.DecodeProbe
  moreLeancArgs := #["-O3"]

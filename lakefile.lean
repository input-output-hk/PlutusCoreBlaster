import Lake
open Lake DSL System

package «PlutusCore» where
  -- Cryptograph.FFI needs the native crypto libraries at link/load time.
  moreLinkArgs := #["-lsodium", "-lsecp256k1", "-lblst"]

require Blaster from git "https://github.com/input-output-hk/Lean-blaster" @ "main"

@[default_target]
lean_lib «PlutusCore» where
  -- add library configuration options here

@[test_driver]
lean_lib «Tests» where
  -- add library configuration options here

lean_lib «Lemmas» where
  -- add library configuration options here

lean_lib «Cryptograph» where
  -- add library configuration options here

/-!
## Native C shims for `Cryptograph.FFI.*`

Four `extern_lib` targets compile the C shims under
`Cryptograph/FFI/c/` into static libraries and link them into any
`lean_exe` or precompiled module that imports `Cryptograph.FFI`.

Dependencies expected on the host (not built by Lake):
* `libsodium`        (dev headers + runtime)
* `libsecp256k1`     (dev headers + runtime)
* `libblst`          (dev headers + runtime, from supranational/blst)

The shims are built with the host's `cc` (`buildO`) rather than
`buildLeanO` so that system headers (`<sodium.h>`, `<secp256k1.h>`,
`<blst.h>`, libc) are on the include path. Lean's own headers are
added explicitly via `-I <lean include dir>` for the files that
include `<lean/lean.h>`.
-/

extern_lib leanPlutusHash pkg := do
  let ffiCDir := pkg.dir / "Cryptograph" / "FFI" / "c"
  let leanInc ← getLeanIncludeDir
  let weakArgs  := #["-I", leanInc.toString, "-I", ffiCDir.toString]
  let traceArgs := #["-O2", "-fPIC"]
  let s1 ← inputTextFile (ffiCDir / "lean_plutus_hash.c")
  let s2 ← inputTextFile (ffiCDir / "crypton" / "crypton_sha3.c")
  let s3 ← inputTextFile (ffiCDir / "crypton" / "crypton_ripemd.c")
  let o1 ← buildO (pkg.buildDir / "c" / "lean_plutus_hash.o") s1 weakArgs traceArgs
  let o2 ← buildO (pkg.buildDir / "c" / "crypton_sha3.o")     s2 weakArgs traceArgs
  let o3 ← buildO (pkg.buildDir / "c" / "crypton_ripemd.o")   s3 weakArgs traceArgs
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "leanPlutusHash") #[o1, o2, o3]

extern_lib leanPlutusEd25519 pkg := do
  let ffiCDir := pkg.dir / "Cryptograph" / "FFI" / "c"
  let leanInc ← getLeanIncludeDir
  let weakArgs  := #["-I", leanInc.toString, "-I", ffiCDir.toString]
  let traceArgs := #["-O2", "-fPIC"]
  let s ← inputTextFile (ffiCDir / "lean_plutus_ed25519.c")
  let o ← buildO (pkg.buildDir / "c" / "lean_plutus_ed25519.o") s weakArgs traceArgs
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "leanPlutusEd25519") #[o]

extern_lib leanPlutusSecp256k1 pkg := do
  let ffiCDir := pkg.dir / "Cryptograph" / "FFI" / "c"
  let leanInc ← getLeanIncludeDir
  let weakArgs  := #["-I", leanInc.toString, "-I", ffiCDir.toString]
  let traceArgs := #["-O2", "-fPIC"]
  let s ← inputTextFile (ffiCDir / "lean_plutus_secp256k1.c")
  let o ← buildO (pkg.buildDir / "c" / "lean_plutus_secp256k1.o") s weakArgs traceArgs
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "leanPlutusSecp256k1") #[o]

extern_lib leanPlutusBls12_381 pkg := do
  let ffiCDir := pkg.dir / "Cryptograph" / "FFI" / "c"
  let leanInc ← getLeanIncludeDir
  let weakArgs  := #["-I", leanInc.toString, "-I", ffiCDir.toString]
  let traceArgs := #["-O2", "-fPIC"]
  let s ← inputTextFile (ffiCDir / "lean_plutus_bls12_381.c")
  let o ← buildO (pkg.buildDir / "c" / "lean_plutus_bls12_381.o") s weakArgs traceArgs
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "leanPlutusBls12_381") #[o]

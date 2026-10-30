import PlutusCore.UPLC.BlueprintEncoding.Assurance

open PlutusCore.UPLC.BlueprintEncoding.Assurance.Internal

-- Cross a batch boundary, preserve duplicate input paths, and exercise filenames
-- whose escaped utility output must fall back to an unambiguous implementation.
#eval IO.FS.withTempDir fun root => do
  let mut paths := #[]
  let mut expected := #[]
  for i in [:67] do
    let name := if i == 65 then "escaped\nname" else s!"module {i}"
    let path := root / name
    let bytes := s!"module contents {i}".toUTF8
    IO.FS.writeBinFile path bytes
    paths := paths.push path
    expected := expected.push (sha256Hex bytes)
  paths := paths.push paths[0]!
  expected := expected.push expected[0]!
  unless (← sha256Files paths) == expected do
    throw <| IO.userError "batched hashing must preserve exact digests and input order"
  unless (← sha256Files #[]).isEmpty do throw <| IO.userError "empty batch"
  IO.FS.writeFile paths[0]! "changed after capture"
  unless (← sha256Files #[paths[0]!]) == #[sha256Hex "changed after capture".toUTF8] do
    throw <| IO.userError "hashes must not be reused across captures"
  let mut failed := false
  try
    discard <| sha256Files #[root / "missing"]
  catch _ => failed := true
  unless failed do throw <| IO.userError "missing files must fail"

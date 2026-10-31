
import Tests.Cryptograph.Blake2b.Blake2bTestVectors
import Tests.Cryptograph.BLS12_381.TestVectors
import Tests.Cryptograph.Keccak.Keccak256TestVectors
import Tests.Cryptograph.Ripemd.Ripemd160TestVectors
import Tests.Cryptograph.Sha2.Sha256TestVectors
import Tests.Cryptograph.Sha2.Sha512TestVectors
import Tests.Cryptograph.Sha3.Sha3_256TestVectors

import Tests.Bitwise.Tests
import Tests.Cbor.Tests
import Tests.UPLC.BlueprintEncoding.CtfTests
import Tests.UPLC.BlueprintEncoding.Tests
import Tests.UPLC.CekMachine.Tests
import Tests.UPLC.Costing
import Tests.UPLC.FlatEncoding.Tests
import Tests.UPLC.PreProcess.Tests
import Tests.UPLC.ScriptEncoding.Tests
import Tests.UPLC.TextEncoding.Tests
import Tests.CekRuns
import Tests.DataComparison
import Tests.DecidableEq
import Tests.StackIndependence

-- The conformance test suite (Tests.Conformance) is intentionally NOT imported
-- here. It is built and run only by the manual `ci-conformance` workflow,
-- which checks out IntersectMBO/plutus and (re)generates the suite first.

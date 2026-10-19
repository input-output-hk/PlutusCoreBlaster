-- This module serves as the root of the `Benchmark` library.
-- It imports everything the generated benchmark cases import, so that
-- `lake build Benchmark` prepares them all before any case runs.
import Benchmark.PrepUplc.Harness
import Benchmark.PrepUplc.Inputs
import PlutusCore.UPLC.ScriptEncoding.Tests

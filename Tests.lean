-- This module serves as the root of the `Tests` library.
-- Import modules here that should be built as part of the library.
import Tests.Basic
import Tests.BlueprintCodegen.Tests
import Tests.BlueprintVerify.Tests

-- Self-contained encoding tests; generated Game templates run in compiled-assurance.
import Tests.BlueprintVerify.NativeEncoding
import Tests.BlueprintVerify.BooleanCase
import Tests.BlueprintVerify.RecursiveSchema

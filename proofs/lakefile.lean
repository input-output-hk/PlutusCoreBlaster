import Lake
open Lake DSL

package PlutusCoreFacts where
  moreLeanArgs := #["--threads=2", "-s65536"]

require Blaster from git "https://github.com/colll78/Lean-blaster" @ "08002278c0fe6e8042c5e1380a12fb4511c79777"
require PlutusCore from ".."

@[default_target]
lean_lib PlutusCoreFacts

@[test_driver]
lean_lib FactTests

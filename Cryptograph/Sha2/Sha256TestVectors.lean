import Cryptograph.Sha2.Sha256

open Cryptograph.Sha2

namespace Cryptograph.Sha2.Sha256TestVectors

example : Sha256.hash ""    = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" := by native_decide
example : Sha256.hash "a"   = "ca978112ca1bbdcafac231b39a23dc4da786eff8147c4e72b9807785afee48bb" := by native_decide
example : Sha256.hash "abc" = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" := by native_decide

example : Sha256.hash "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"  = "a8ae6e6ee929abea3afcfc5258c8ccd6f85273e0d4626d26c7279f3250f77c8e" := by native_decide
example : Sha256.hash "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcde"   = "057ee79ece0b9a849552ab8d3c335fe9a5f1c46ef5f1d9b190c295728628299c" := by native_decide
example : Sha256.hash "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0" = "2a6ad82f3620d3ebe9d678c812ae12312699d673240d5be8fac0910a70000d93" := by native_decide
example : Sha256.hash "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"          = "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" := by native_decide
example : Sha256.hash "abcdbcdecdefdefgefghghfghighijhijkijkljklmklmnlmnomnopnopq"        = "0a6b5000da86d860f5937f919a8d81ed61aecc3d1caff95ef6b6fd670e911cdb" := by native_decide
example : Sha256.hash "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"
    = "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1" := by native_decide

-- Very slooow!
-- example : Sha256.hash ⟨List.replicate 1_000_000 'a'⟩ = "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0" := by native_decide

end Cryptograph.Sha2.Sha256TestVectors

import Cryptograph.Sha3.Sha3_256

namespace Cryptograph.Sha3.Sha3_256TestVectors

/-! ## Test Vectors for SHA3-256

These test vectors are from NIST FIPS 202 and other official SHA3 test suites.
-/

-- Empty string
/-- info: "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a" -/
#guard_msgs in
#eval Sha3_256.hash ""

-- "abc"
/-- info: "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532" -/
#guard_msgs in
#eval Sha3_256.hash "abc"

-- "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
/-- info: "41c0dba2a9d6240849100376a8235e2c82e1b9998a999e21db32dd97496d3376" -/
#guard_msgs in
#eval Sha3_256.hash "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"

-- "The quick brown fox jumps over the lazy dog"
/-- info: "69070dda01975c8c120c3aada1b282394e7f032fa9cf32f4cb2259a0897dfc04" -/
#guard_msgs in
#eval Sha3_256.hash "The quick brown fox jumps over the lazy dog"

-- "Hello, World!"
/-- info: "1af17a664e3fa8e419b8ba05c2a173169df76162a5a286e0c405b460d478f7ef" -/
#guard_msgs in
#eval Sha3_256.hash "Hello, World!"

-- "a" (single character)
/-- info: "80084bf2fba02475726feb2cab2d8215eab14bc6bdd8bfb2c8151257032ecd8b" -/
#guard_msgs in
#eval Sha3_256.hash "a"

-- Newline
/-- info: "a78f2c566b2439463a2e7ca515bbfa3f92948506583cbadaebdd507f277542bd" -/
#guard_msgs in
#eval Sha3_256.hash "\n"

-- Space
/-- info: "60e893e6d54d8526e55a81f98bfac5da236bb203e84ed5967a8f527d5bf3d4a4" -/
#guard_msgs in
#eval Sha3_256.hash " "

end Cryptograph.Sha3.Sha3_256TestVectors

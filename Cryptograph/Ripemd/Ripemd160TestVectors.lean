import Cryptograph.Ripemd.Ripemd160

namespace Cryptograph.Ripemd.Ripemd160TestVectors

/-! ## Test Vectors for RIPEMD-160-/

-- Empty string
/-- info: "9c1185a5c5e9fc54612808977ee8f548b2258d31" -/
#guard_msgs in
#eval Ripemd160.ripemd160_hash ""

-- "abc"
/-- info: "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc" -/
#guard_msgs in
#eval Ripemd160.ripemd160_hash "abc"

-- "message digest"
/-- info: "5d0689ef49d2fae572b881b123a85ffa21595f36" -/
#guard_msgs in
#eval Ripemd160.ripemd160_hash "message digest"

-- "abcdefghijklmnopqrstuvwxyz"
/-- info: "f71c27109c692c1b56bbdceb5b9d2865b3708dbc" -/
#guard_msgs in
#eval Ripemd160.ripemd160_hash "abcdefghijklmnopqrstuvwxyz"

-- "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
/-- info: "99681e20a62fa20f58234fc749e41d1084d455b4" -/
#guard_msgs in
#eval Ripemd160.ripemd160_hash "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"

-- "The quick brown fox jumps over the lazy dog"
/-- info: "37f332f68db77bd9d7edd4969571ad671cf9dd3b" -/
#guard_msgs in
#eval Ripemd160.ripemd160_hash "The quick brown fox jumps over the lazy dog"

-- Single "a"
/-- info: "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe" -/
#guard_msgs in
#eval Ripemd160.ripemd160_hash "a"

end Cryptograph.Ripemd.Ripemd160TestVectors

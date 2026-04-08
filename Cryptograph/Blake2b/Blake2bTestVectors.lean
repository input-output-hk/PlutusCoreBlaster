import Cryptograph.Blake2b.Blake2b

namespace Cryptograph.Blake2b.Blake2bTestVectors

/-! ## Test Vectors for Blake2b

These test vectors are from the official Blake2 test suite.
-/

/-! ### Blake2b-256 Test Vectors -/

-- Empty string
/-- info: "0e5751c026e543b2e8ab2eb06099daa1d1e5df47778f7787faab45cdf12fe3a8" -/
#guard_msgs in
#eval Blake2b.blake2b_256_hash ""

-- "abc"
/-- info: "bddd813c634239723171ef3fee98579b94964e3bb1cb3e427262c8c068d52319" -/
#guard_msgs in
#eval Blake2b.blake2b_256_hash "abc"

-- "The quick brown fox jumps over the lazy dog"
/-- info: "01718cec35cd3d796dd00020e0bfecb473ad23457d063b75eff29c0ffa2e58a9" -/
#guard_msgs in
#eval Blake2b.blake2b_256_hash "The quick brown fox jumps over the lazy dog"

-- "hello world"
/-- info: "256c83b297114d201b30179f3f0ef0cace9783622da5974326b436178aeef610" -/
#guard_msgs in
#eval Blake2b.blake2b_256_hash "hello world"

-- Single byte "a"
/-- info: "8928aae63c84d87ea098564d1e03ad813f107add474e56aedd286349c0c03ea4" -/
#guard_msgs in
#eval Blake2b.blake2b_256_hash "a"

/-! ### Blake2b-224 Test Vectors -/

-- Empty string
/-- info: "836cc68931c2e4e3e838602eca1902591d216837bafddfe6f0c8cb07" -/
#guard_msgs in
#eval Blake2b.blake2b_224_hash ""

-- "abc"
/-- info: "9bd237b02a29e43bdd6738afa5b53ff0eee178d6210b618e4511aec8" -/
#guard_msgs in
#eval Blake2b.blake2b_224_hash "abc"

-- "The quick brown fox jumps over the lazy dog"
/-- info: "477c3985751dd4d1b8c93827ea5310b33bb02a26463a050dffd3e857" -/
#guard_msgs in
#eval Blake2b.blake2b_224_hash "The quick brown fox jumps over the lazy dog"

-- "hello world"
/-- info: "42d1854b7d69e3b57c64fcc7b4f64171b47dff43fba6ac0499ff437f" -/
#guard_msgs in
#eval Blake2b.blake2b_224_hash "hello world"

end Cryptograph.Blake2b.Blake2bTestVectors

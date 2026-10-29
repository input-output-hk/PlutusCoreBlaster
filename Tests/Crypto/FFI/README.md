# Ed25519 test vectors

`ed25519_wycheproof.json` is copied unchanged from
[C2SP/wycheproof](https://github.com/C2SP/wycheproof/blob/d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9/testvectors_v1/ed25519_test.json),
revision `d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9`, under Apache-2.0.
`WYCHEPROOF_LICENSE` is the corresponding unmodified license.

The native test driver compares all 210 cases with the pure Lean reference. Valid and invalid
cases also have their expected result checked. `acceptable` cases require native/reference
agreement; libsodium determines the native acceptance policy. Wrong signature lengths are
checked as Plutus evaluation errors rather than the boolean failure of the lower-level API.

#ifndef LEAN_PLUTUS_CRYPTO_H
#define LEAN_PLUTUS_CRYPTO_H

#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

/* Borrowed ByteArray inputs; hash functions return fresh, owned ByteArrays.
 * Adapted from PR #13, cryptograph-ffi, b12153961f282a855d918a69fb05209a8f0786b6.
 */
LEAN_EXPORT lean_obj_res lean_plutus_crypto_initialize(lean_obj_arg world);
LEAN_EXPORT lean_obj_res lean_plutus_sha2_256(b_lean_obj_arg input);
LEAN_EXPORT lean_obj_res lean_plutus_sha3_256(b_lean_obj_arg input);
LEAN_EXPORT lean_obj_res lean_plutus_blake2b_256(b_lean_obj_arg input);
LEAN_EXPORT lean_obj_res lean_plutus_blake2b_224(b_lean_obj_arg input);
LEAN_EXPORT lean_obj_res lean_plutus_keccak_256(b_lean_obj_arg input);
LEAN_EXPORT lean_obj_res lean_plutus_ripemd_160(b_lean_obj_arg input);
LEAN_EXPORT uint8_t lean_plutus_ed25519_verify(b_lean_obj_arg pk, b_lean_obj_arg msg,
                                             b_lean_obj_arg sig);
#endif

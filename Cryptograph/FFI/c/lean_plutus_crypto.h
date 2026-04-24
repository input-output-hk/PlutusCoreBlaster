#ifndef LEAN_PLUTUS_CRYPTO_H
#define LEAN_PLUTUS_CRYPTO_H

/*
 * Shared prototypes for the Lean <-> C bridge used by Cryptograph.FFI.
 * All boundary functions operate on Lean sarray (ByteArray) objects.
 *
 * Each primitive binds to the same upstream C symbol that the Haskell
 * Plutus evaluator's `foreign import ccall` declaration binds to:
 *
 *   libsodium        -> SHA-256, Blake2b-224/256, Ed25519 verify
 *   crypton cbits    -> SHA3-256, Keccak-256, RIPEMD-160 (vendored in ./crypton)
 *   libsecp256k1     -> ECDSA verify, Schnorr verify
 *   blst             -> BLS12-381 G1/G2/pairing suite
 */

#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

/* Hashes */
LEAN_EXPORT lean_obj_res lean_plutus_sha2_256     (b_lean_obj_arg input);
LEAN_EXPORT lean_obj_res lean_plutus_blake2b_256  (b_lean_obj_arg input);
LEAN_EXPORT lean_obj_res lean_plutus_blake2b_224  (b_lean_obj_arg input);
LEAN_EXPORT lean_obj_res lean_plutus_sha3_256     (b_lean_obj_arg input);
LEAN_EXPORT lean_obj_res lean_plutus_keccak_256   (b_lean_obj_arg input);
LEAN_EXPORT lean_obj_res lean_plutus_ripemd_160   (b_lean_obj_arg input);

/* Signature verification */
LEAN_EXPORT uint8_t lean_plutus_ed25519_verify (b_lean_obj_arg pk,
                                                b_lean_obj_arg msg,
                                                b_lean_obj_arg sig);
LEAN_EXPORT uint8_t lean_plutus_ecdsa_verify   (b_lean_obj_arg pk,
                                                b_lean_obj_arg msg,
                                                b_lean_obj_arg sig);
LEAN_EXPORT uint8_t lean_plutus_schnorr_verify (b_lean_obj_arg pk,
                                                b_lean_obj_arg msg,
                                                b_lean_obj_arg sig);

/* BLS12-381 -- points/ml-results are wrapped via lean_alloc_external.
 *
 * Inputs for compress/uncompress are ByteArray; outputs of the point
 * constructors are opaque lean_object* carrying a heap-allocated
 * blst_p1 / blst_p2 / blst_fp12. Equality returns a Lean Bool (uint8_t).
 *
 * lean_plutus_bls_initialize registers the three external-object
 * classes with the Lean runtime; it must be called once from
 * `builtin_initialize`.
 */
LEAN_EXPORT lean_object *lean_plutus_bls_initialize(lean_object *w);

/* G1 */
LEAN_EXPORT lean_obj_res lean_plutus_bls_g1_add           (b_lean_obj_arg a, b_lean_obj_arg b);
LEAN_EXPORT lean_obj_res lean_plutus_bls_g1_neg           (b_lean_obj_arg p);
LEAN_EXPORT lean_obj_res lean_plutus_bls_g1_scalar_mul    (b_lean_obj_arg scalar_be, b_lean_obj_arg p);
LEAN_EXPORT uint8_t      lean_plutus_bls_g1_equal         (b_lean_obj_arg a, b_lean_obj_arg b);
LEAN_EXPORT lean_obj_res lean_plutus_bls_g1_compress      (b_lean_obj_arg p);            /* -> ByteArray(48) */
LEAN_EXPORT lean_obj_res lean_plutus_bls_g1_uncompress    (b_lean_obj_arg bytes);        /* -> Except String G1 */
LEAN_EXPORT lean_obj_res lean_plutus_bls_g1_hash_to_group (b_lean_obj_arg msg, b_lean_obj_arg dst);

/* G2 */
LEAN_EXPORT lean_obj_res lean_plutus_bls_g2_add           (b_lean_obj_arg a, b_lean_obj_arg b);
LEAN_EXPORT lean_obj_res lean_plutus_bls_g2_neg           (b_lean_obj_arg p);
LEAN_EXPORT lean_obj_res lean_plutus_bls_g2_scalar_mul    (b_lean_obj_arg scalar_be, b_lean_obj_arg p);
LEAN_EXPORT uint8_t      lean_plutus_bls_g2_equal         (b_lean_obj_arg a, b_lean_obj_arg b);
LEAN_EXPORT lean_obj_res lean_plutus_bls_g2_compress      (b_lean_obj_arg p);            /* -> ByteArray(96) */
LEAN_EXPORT lean_obj_res lean_plutus_bls_g2_uncompress    (b_lean_obj_arg bytes);        /* -> Except String G2 */
LEAN_EXPORT lean_obj_res lean_plutus_bls_g2_hash_to_group (b_lean_obj_arg msg, b_lean_obj_arg dst);

/* Pairing */
LEAN_EXPORT lean_obj_res lean_plutus_bls_miller_loop      (b_lean_obj_arg p1, b_lean_obj_arg p2);
LEAN_EXPORT lean_obj_res lean_plutus_bls_mul_ml_result    (b_lean_obj_arg a, b_lean_obj_arg b);
LEAN_EXPORT uint8_t      lean_plutus_bls_final_verify     (b_lean_obj_arg a, b_lean_obj_arg b);

#endif /* LEAN_PLUTUS_CRYPTO_H */

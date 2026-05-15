/*
 * Lean <-> C bridge for the Plutus UPLC hash builtins.
 *
 * Backends mirror the Haskell Plutus evaluator:
 *   - SHA2-256, Blake2b-224/256  -> libsodium (same FFI symbols as
 *     Cardano.Crypto.Libsodium.C)
 *   - SHA3-256, Keccak-256, RIPEMD-160 -> vendored crypton cbits
 *     (same C implementation Plutus reaches via the crypton Haskell
 *     package)
 */

#include "lean_plutus_crypto.h"

#include <sodium.h>
#include <stdlib.h>
#include <string.h>

#include "crypton/crypton_sha3.h"
#include "crypton/crypton_ripemd.h"

/* ------- helpers ------- */

/* Allocate a fresh Lean ByteArray of `n` bytes. */
static inline lean_object *alloc_sarray(size_t n) {
    /* element size 1, size=n, capacity=n */
    return lean_alloc_sarray(1, n, n);
}

/* ---------------------------------------------------------------- */
/* libsodium-backed hashes                                          */
/* ---------------------------------------------------------------- */

LEAN_EXPORT lean_obj_res lean_plutus_sha2_256(b_lean_obj_arg input) {
    const uint8_t *in_ptr = lean_sarray_cptr(input);
    size_t         in_len = lean_sarray_size(input);

    lean_object *out = alloc_sarray(32);
    crypto_hash_sha256(lean_sarray_cptr(out), in_ptr, in_len);
    return out;
}

LEAN_EXPORT lean_obj_res lean_plutus_blake2b_256(b_lean_obj_arg input) {
    const uint8_t *in_ptr = lean_sarray_cptr(input);
    size_t         in_len = lean_sarray_size(input);

    lean_object *out = alloc_sarray(32);
    crypto_generichash_blake2b(
        lean_sarray_cptr(out), 32,
        in_ptr, in_len,
        NULL, 0);
    return out;
}

LEAN_EXPORT lean_obj_res lean_plutus_blake2b_224(b_lean_obj_arg input) {
    const uint8_t *in_ptr = lean_sarray_cptr(input);
    size_t         in_len = lean_sarray_size(input);

    lean_object *out = alloc_sarray(28);
    crypto_generichash_blake2b(
        lean_sarray_cptr(out), 28,
        in_ptr, in_len,
        NULL, 0);
    return out;
}

/* ---------------------------------------------------------------- */
/* crypton-backed hashes (SHA3-256, Keccak-256, RIPEMD-160)         */
/* ---------------------------------------------------------------- */

/*
 * `struct sha3_ctx` has a trailing flexible array `buf[0]`; the caller
 * is responsible for allocating `SHA3_CTX_SIZE + SHA3_BUF_SIZE(bitsize)`
 * bytes. For the 256-bit variants that is 200 - 2*(256/8) = 136 bytes
 * of trailing buffer.
 */

LEAN_EXPORT lean_obj_res lean_plutus_sha3_256(b_lean_obj_arg input) {
    const uint8_t *in_ptr = lean_sarray_cptr(input);
    size_t         in_len = lean_sarray_size(input);

    unsigned char ctx_buf[SHA3_CTX_SIZE + SHA3_BUF_SIZE(256)];
    struct sha3_ctx *ctx = (struct sha3_ctx *)ctx_buf;

    crypton_sha3_init(ctx, 256);
    crypton_sha3_update(ctx, in_ptr, (uint32_t)in_len);

    lean_object *out = alloc_sarray(32);
    crypton_sha3_finalize(ctx, 256, lean_sarray_cptr(out));
    return out;
}

LEAN_EXPORT lean_obj_res lean_plutus_keccak_256(b_lean_obj_arg input) {
    const uint8_t *in_ptr = lean_sarray_cptr(input);
    size_t         in_len = lean_sarray_size(input);

    unsigned char ctx_buf[SHA3_CTX_SIZE + SHA3_BUF_SIZE(256)];
    struct sha3_ctx *ctx = (struct sha3_ctx *)ctx_buf;

    crypton_keccak_init(ctx, 256);
    crypton_keccak_update(ctx, (uint8_t *)in_ptr, (uint32_t)in_len);

    lean_object *out = alloc_sarray(32);
    crypton_keccak_finalize(ctx, 256, lean_sarray_cptr(out));
    return out;
}

LEAN_EXPORT lean_obj_res lean_plutus_ripemd_160(b_lean_obj_arg input) {
    const uint8_t *in_ptr = lean_sarray_cptr(input);
    size_t         in_len = lean_sarray_size(input);

    struct ripemd160_ctx ctx;
    crypton_ripemd160_init(&ctx);
    crypton_ripemd160_update(&ctx, in_ptr, (uint32_t)in_len);

    lean_object *out = alloc_sarray(20);
    crypton_ripemd160_finalize(&ctx, lean_sarray_cptr(out));
    return out;
}

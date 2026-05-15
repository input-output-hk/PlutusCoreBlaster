/*
 * Lean <-> C bridge for the Plutus secp256k1 signature-verification
 * builtins (VerifyEcdsaSecp256k1Signature, VerifySchnorrSecp256k1Signature).
 *
 * Binds the same libsecp256k1 symbols that Cardano.Crypto.SECP256K1.C
 * imports. A single verify-only context is created lazily on first use
 * (thread-safe: libsecp256k1 verify contexts are immutable after
 * creation).
 *
 * Plutus wire formats (same as cardano-crypto-class):
 *   ECDSA
 *     publicKey : 33 bytes, serialised compressed (SEC1)
 *     message   : 32 bytes, pre-hashed (Plutus hashes with SHA-256)
 *     signature : 64 bytes, compact (r || s), big-endian
 *   Schnorr (BIP-340)
 *     publicKey : 32 bytes, x-only
 *     message   : arbitrary length
 *     signature : 64 bytes
 *
 * Any size mismatch or parse failure yields False, matching Plutus'
 * total-function semantics.
 */

#include "lean_plutus_crypto.h"

#include <secp256k1.h>
#include <secp256k1_schnorrsig.h>
#include <secp256k1_extrakeys.h>
#include <stdatomic.h>
#include <stdlib.h>

#define ECDSA_PK_BYTES      33
#define ECDSA_MSG_BYTES     32
#define ECDSA_SIG_BYTES     64
#define SCHNORR_PK_BYTES    32
#define SCHNORR_SIG_BYTES   64

/* Lazily created verify-only context. Immutable after init, so reading
 * it from multiple threads post-init is safe. */
static _Atomic(secp256k1_context *) g_verify_ctx = NULL;

static secp256k1_context *get_verify_ctx(void) {
    secp256k1_context *ctx = atomic_load_explicit(&g_verify_ctx, memory_order_acquire);
    if (ctx != NULL) return ctx;

    secp256k1_context *fresh = secp256k1_context_create(SECP256K1_CONTEXT_VERIFY);
    if (fresh == NULL) return NULL;

    secp256k1_context *expected = NULL;
    if (!atomic_compare_exchange_strong_explicit(
            &g_verify_ctx, &expected, fresh,
            memory_order_acq_rel, memory_order_acquire)) {
        /* Another thread installed one first. Drop ours. */
        secp256k1_context_destroy(fresh);
        return expected;
    }
    return fresh;
}

/* ---------------------------------------------------------------- */
/* ECDSA                                                            */
/* ---------------------------------------------------------------- */

LEAN_EXPORT uint8_t lean_plutus_ecdsa_verify(b_lean_obj_arg pk,
                                             b_lean_obj_arg msg,
                                             b_lean_obj_arg sig) {
    if (lean_sarray_size(pk)  != ECDSA_PK_BYTES ||
        lean_sarray_size(msg) != ECDSA_MSG_BYTES ||
        lean_sarray_size(sig) != ECDSA_SIG_BYTES) {
        return 0;
    }

    secp256k1_context *ctx = get_verify_ctx();
    if (ctx == NULL) return 0;

    secp256k1_pubkey            pubkey;
    secp256k1_ecdsa_signature   signature;

    if (!secp256k1_ec_pubkey_parse(ctx, &pubkey,
                                   lean_sarray_cptr(pk), ECDSA_PK_BYTES)) {
        return 0;
    }
    if (!secp256k1_ecdsa_signature_parse_compact(ctx, &signature,
                                                 lean_sarray_cptr(sig))) {
        return 0;
    }

    int rc = secp256k1_ecdsa_verify(ctx, &signature,
                                    lean_sarray_cptr(msg),
                                    &pubkey);
    return rc == 1 ? 1 : 0;
}

/* ---------------------------------------------------------------- */
/* Schnorr (BIP-340)                                                */
/* ---------------------------------------------------------------- */

LEAN_EXPORT uint8_t lean_plutus_schnorr_verify(b_lean_obj_arg pk,
                                               b_lean_obj_arg msg,
                                               b_lean_obj_arg sig) {
    if (lean_sarray_size(pk)  != SCHNORR_PK_BYTES ||
        lean_sarray_size(sig) != SCHNORR_SIG_BYTES) {
        return 0;
    }

    secp256k1_context *ctx = get_verify_ctx();
    if (ctx == NULL) return 0;

    secp256k1_xonly_pubkey xonly;
    if (!secp256k1_xonly_pubkey_parse(ctx, &xonly, lean_sarray_cptr(pk))) {
        return 0;
    }

    int rc = secp256k1_schnorrsig_verify(
        ctx,
        lean_sarray_cptr(sig),
        lean_sarray_cptr(msg),
        lean_sarray_size(msg),
        &xonly);
    return rc == 1 ? 1 : 0;
}

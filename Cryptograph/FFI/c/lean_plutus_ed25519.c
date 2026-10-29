/*
 * Lean <-> C bridge for the Plutus VerifyEd25519Signature builtin.
 *
 * Binds `crypto_sign_ed25519_verify_detached` from libsodium, the same
 * symbol that Cardano.Crypto.DSIGN.Ed25519 uses via its foreign import.
 *
 * The public Lean wrapper preserves Plutus evaluation errors for bad lengths;
 * this lower-level byte-array boundary rejects bad lengths defensively.
 */

#include "lean_plutus_crypto.h"

#include <sodium.h>

#define ED25519_PK_BYTES   32
#define ED25519_SIG_BYTES  64

LEAN_EXPORT lean_obj_res lean_plutus_crypto_initialize(lean_obj_arg world) {
    (void)world;
    if (sodium_init() < 0) {
        return lean_io_result_mk_error(lean_mk_io_user_error(
            lean_mk_string("libsodium initialization failed")));
    }
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT uint8_t lean_plutus_ed25519_verify(b_lean_obj_arg pk,
                                               b_lean_obj_arg msg,
                                               b_lean_obj_arg sig) {
    size_t pk_len  = lean_sarray_size(pk);
    size_t sig_len = lean_sarray_size(sig);

    if (pk_len != ED25519_PK_BYTES || sig_len != ED25519_SIG_BYTES) {
        return 0;
    }

    const unsigned char *pk_ptr  = lean_sarray_cptr(pk);
    const unsigned char *sig_ptr = lean_sarray_cptr(sig);
    const unsigned char *msg_ptr = lean_sarray_cptr(msg);
    unsigned long long   msg_len = (unsigned long long)lean_sarray_size(msg);

    int rc = crypto_sign_ed25519_verify_detached(sig_ptr, msg_ptr, msg_len, pk_ptr);
    return rc == 0 ? 1 : 0;
}

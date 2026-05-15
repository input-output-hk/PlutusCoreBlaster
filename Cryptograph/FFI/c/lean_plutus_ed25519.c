/*
 * Lean <-> C bridge for the Plutus VerifyEd25519Signature builtin.
 *
 * Binds `crypto_sign_ed25519_verify_detached` from libsodium, the same
 * symbol that Cardano.Crypto.DSIGN.Ed25519 uses via its foreign import.
 *
 * Plutus convention: verifier returns False (not an error) on bad sizes.
 */

#include "lean_plutus_crypto.h"

#include <sodium.h>

#define ED25519_PK_BYTES   32
#define ED25519_SIG_BYTES  64

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

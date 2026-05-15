/*
 * Lean <-> C bridge for the Plutus BLS12-381 UPLC builtins.
 *
 * Binds the same blst (supranational/blst) symbols that the Haskell
 * Plutus evaluator reaches via
 * Cardano.Crypto.EllipticCurve.BLS12_381.Internal's `foreign import ccall`
 * declarations. Wire formats and semantics match Plutus:
 *
 *   G1 compressed : 48 bytes       G2 compressed : 96 bytes
 *   scalar        : 32 bytes, big-endian
 *   hashToGroup   : DST supplied by caller (Plutus does not pin it)
 *
 * Points are kept in jacobian form (matching cardano-crypto-class)
 * inside heap-allocated `blst_p1` / `blst_p2` structs referenced by
 * Lean via `lean_alloc_external`. The same treatment is given to
 * miller-loop outputs (`blst_fp12`).
 */

#include "lean_plutus_crypto.h"

#include <blst.h>
#include <stdlib.h>
#include <string.h>

/* ---------------------------------------------------------------- */
/* External-object classes for blst_p1 / blst_p2 / blst_fp12        */
/* ---------------------------------------------------------------- */

static void free_g1(void *p) { free(p); }
static void free_g2(void *p) { free(p); }
static void free_ml(void *p) { free(p); }

static void noop_foreach(void *p, b_lean_obj_arg f) {
    (void)p; (void)f;
}

static lean_external_class *g_bls_g1_class = NULL;
static lean_external_class *g_bls_g2_class = NULL;
static lean_external_class *g_bls_ml_class = NULL;

LEAN_EXPORT lean_object *lean_plutus_bls_initialize(lean_object *w) {
    if (g_bls_g1_class == NULL)
        g_bls_g1_class = lean_register_external_class(&free_g1, &noop_foreach);
    if (g_bls_g2_class == NULL)
        g_bls_g2_class = lean_register_external_class(&free_g2, &noop_foreach);
    if (g_bls_ml_class == NULL)
        g_bls_ml_class = lean_register_external_class(&free_ml, &noop_foreach);
    return lean_io_result_mk_ok(lean_box(0));
}

static inline blst_p1   *g1_unwrap(b_lean_obj_arg o) { return (blst_p1   *)lean_get_external_data(o); }
static inline blst_p2   *g2_unwrap(b_lean_obj_arg o) { return (blst_p2   *)lean_get_external_data(o); }
static inline blst_fp12 *ml_unwrap(b_lean_obj_arg o) { return (blst_fp12 *)lean_get_external_data(o); }

static inline lean_object *g1_wrap(blst_p1 *p) {
    return lean_alloc_external(g_bls_g1_class, p);
}
static inline lean_object *g2_wrap(blst_p2 *p) {
    return lean_alloc_external(g_bls_g2_class, p);
}
static inline lean_object *ml_wrap(blst_fp12 *p) {
    return lean_alloc_external(g_bls_ml_class, p);
}

static inline blst_p1 *g1_alloc(void) {
    blst_p1 *p = (blst_p1 *)malloc(sizeof(blst_p1));
    return p;
}
static inline blst_p2 *g2_alloc(void) {
    blst_p2 *p = (blst_p2 *)malloc(sizeof(blst_p2));
    return p;
}
static inline blst_fp12 *ml_alloc(void) {
    blst_fp12 *p = (blst_fp12 *)malloc(sizeof(blst_fp12));
    return p;
}

/* Build Except String α */
static lean_object *mk_except_ok   (lean_object *a) {
    lean_object *c = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(c, 0, a);
    return c;
}
static lean_object *mk_except_error(const char *msg) {
    lean_object *c = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(c, 0, lean_mk_string(msg));
    return c;
}

/* ---------------------------------------------------------------- */
/* G1 operations                                                    */
/* ---------------------------------------------------------------- */

#define G1_COMPRESSED_BYTES  48
#define SCALAR_BYTES         32

LEAN_EXPORT lean_obj_res lean_plutus_bls_g1_add(b_lean_obj_arg a, b_lean_obj_arg b) {
    blst_p1 *out = g1_alloc();
    blst_p1_add_or_double(out, g1_unwrap(a), g1_unwrap(b));
    return g1_wrap(out);
}

LEAN_EXPORT lean_obj_res lean_plutus_bls_g1_neg(b_lean_obj_arg p) {
    blst_p1 *out = g1_alloc();
    memcpy(out, g1_unwrap(p), sizeof(blst_p1));
    blst_p1_cneg(out, 1);
    return g1_wrap(out);
}

LEAN_EXPORT lean_obj_res lean_plutus_bls_g1_scalar_mul(b_lean_obj_arg scalar_be,
                                                       b_lean_obj_arg p) {
    size_t           slen = lean_sarray_size(scalar_be);
    const uint8_t   *sbuf = lean_sarray_cptr(scalar_be);

    /* Plutus stores the scalar big-endian. If shorter than 32 bytes,
     * left-pad with zeros; if longer, blst reduces mod group order. */
    uint8_t padded[SCALAR_BYTES] = {0};
    if (slen <= SCALAR_BYTES) {
        memcpy(padded + (SCALAR_BYTES - slen), sbuf, slen);
        sbuf = padded;
        slen = SCALAR_BYTES;
    }

    blst_scalar scalar;
    blst_scalar_from_bendian(&scalar, sbuf);

    blst_p1 *out = g1_alloc();
    blst_p1_mult(out, g1_unwrap(p), (const byte *)&scalar, slen * 8);
    return g1_wrap(out);
}

LEAN_EXPORT uint8_t lean_plutus_bls_g1_equal(b_lean_obj_arg a, b_lean_obj_arg b) {
    return blst_p1_is_equal(g1_unwrap(a), g1_unwrap(b)) ? 1 : 0;
}

LEAN_EXPORT lean_obj_res lean_plutus_bls_g1_compress(b_lean_obj_arg p) {
    lean_object *out = lean_alloc_sarray(1, G1_COMPRESSED_BYTES, G1_COMPRESSED_BYTES);
    blst_p1_compress(lean_sarray_cptr(out), g1_unwrap(p));
    return out;
}

LEAN_EXPORT lean_obj_res lean_plutus_bls_g1_uncompress(b_lean_obj_arg bytes) {
    if (lean_sarray_size(bytes) != G1_COMPRESSED_BYTES) {
        return mk_except_error("BLS12_381.G1.uncompress: expected 48 bytes");
    }
    blst_p1_affine affine;
    BLST_ERROR rc = blst_p1_uncompress(&affine, lean_sarray_cptr(bytes));
    if (rc != BLST_SUCCESS) {
        return mk_except_error("BLS12_381.G1.uncompress: invalid encoding");
    }
    if (!blst_p1_affine_in_g1(&affine)) {
        return mk_except_error("BLS12_381.G1.uncompress: point not in G1");
    }
    blst_p1 *out = g1_alloc();
    blst_p1_from_affine(out, &affine);
    return mk_except_ok(g1_wrap(out));
}

LEAN_EXPORT lean_obj_res lean_plutus_bls_g1_hash_to_group(b_lean_obj_arg msg,
                                                          b_lean_obj_arg dst) {
    blst_p1 *out = g1_alloc();
    blst_hash_to_g1(out,
                    lean_sarray_cptr(msg), lean_sarray_size(msg),
                    lean_sarray_cptr(dst), lean_sarray_size(dst),
                    NULL, 0);
    return g1_wrap(out);
}

/* ---------------------------------------------------------------- */
/* G2 operations                                                    */
/* ---------------------------------------------------------------- */

#define G2_COMPRESSED_BYTES  96

LEAN_EXPORT lean_obj_res lean_plutus_bls_g2_add(b_lean_obj_arg a, b_lean_obj_arg b) {
    blst_p2 *out = g2_alloc();
    blst_p2_add_or_double(out, g2_unwrap(a), g2_unwrap(b));
    return g2_wrap(out);
}

LEAN_EXPORT lean_obj_res lean_plutus_bls_g2_neg(b_lean_obj_arg p) {
    blst_p2 *out = g2_alloc();
    memcpy(out, g2_unwrap(p), sizeof(blst_p2));
    blst_p2_cneg(out, 1);
    return g2_wrap(out);
}

LEAN_EXPORT lean_obj_res lean_plutus_bls_g2_scalar_mul(b_lean_obj_arg scalar_be,
                                                       b_lean_obj_arg p) {
    size_t           slen = lean_sarray_size(scalar_be);
    const uint8_t   *sbuf = lean_sarray_cptr(scalar_be);

    uint8_t padded[SCALAR_BYTES] = {0};
    if (slen <= SCALAR_BYTES) {
        memcpy(padded + (SCALAR_BYTES - slen), sbuf, slen);
        sbuf = padded;
        slen = SCALAR_BYTES;
    }

    blst_scalar scalar;
    blst_scalar_from_bendian(&scalar, sbuf);

    blst_p2 *out = g2_alloc();
    blst_p2_mult(out, g2_unwrap(p), (const byte *)&scalar, slen * 8);
    return g2_wrap(out);
}

LEAN_EXPORT uint8_t lean_plutus_bls_g2_equal(b_lean_obj_arg a, b_lean_obj_arg b) {
    return blst_p2_is_equal(g2_unwrap(a), g2_unwrap(b)) ? 1 : 0;
}

LEAN_EXPORT lean_obj_res lean_plutus_bls_g2_compress(b_lean_obj_arg p) {
    lean_object *out = lean_alloc_sarray(1, G2_COMPRESSED_BYTES, G2_COMPRESSED_BYTES);
    blst_p2_compress(lean_sarray_cptr(out), g2_unwrap(p));
    return out;
}

LEAN_EXPORT lean_obj_res lean_plutus_bls_g2_uncompress(b_lean_obj_arg bytes) {
    if (lean_sarray_size(bytes) != G2_COMPRESSED_BYTES) {
        return mk_except_error("BLS12_381.G2.uncompress: expected 96 bytes");
    }
    blst_p2_affine affine;
    BLST_ERROR rc = blst_p2_uncompress(&affine, lean_sarray_cptr(bytes));
    if (rc != BLST_SUCCESS) {
        return mk_except_error("BLS12_381.G2.uncompress: invalid encoding");
    }
    if (!blst_p2_affine_in_g2(&affine)) {
        return mk_except_error("BLS12_381.G2.uncompress: point not in G2");
    }
    blst_p2 *out = g2_alloc();
    blst_p2_from_affine(out, &affine);
    return mk_except_ok(g2_wrap(out));
}

LEAN_EXPORT lean_obj_res lean_plutus_bls_g2_hash_to_group(b_lean_obj_arg msg,
                                                          b_lean_obj_arg dst) {
    blst_p2 *out = g2_alloc();
    blst_hash_to_g2(out,
                    lean_sarray_cptr(msg), lean_sarray_size(msg),
                    lean_sarray_cptr(dst), lean_sarray_size(dst),
                    NULL, 0);
    return g2_wrap(out);
}

/* ---------------------------------------------------------------- */
/* Pairing                                                          */
/* ---------------------------------------------------------------- */

LEAN_EXPORT lean_obj_res lean_plutus_bls_miller_loop(b_lean_obj_arg p1,
                                                     b_lean_obj_arg p2) {
    blst_p1_affine a1;
    blst_p2_affine a2;
    blst_p1_to_affine(&a1, g1_unwrap(p1));
    blst_p2_to_affine(&a2, g2_unwrap(p2));

    blst_fp12 *out = ml_alloc();
    blst_miller_loop(out, &a2, &a1);
    return ml_wrap(out);
}

LEAN_EXPORT lean_obj_res lean_plutus_bls_mul_ml_result(b_lean_obj_arg a,
                                                       b_lean_obj_arg b) {
    blst_fp12 *out = ml_alloc();
    blst_fp12_mul(out, ml_unwrap(a), ml_unwrap(b));
    return ml_wrap(out);
}

LEAN_EXPORT uint8_t lean_plutus_bls_final_verify(b_lean_obj_arg a,
                                                 b_lean_obj_arg b) {
    return blst_fp12_finalverify(ml_unwrap(a), ml_unwrap(b)) ? 1 : 0;
}

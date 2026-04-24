{ pkgs ? import <nixpkgs> {} }:

# Dev shell for building Cryptograph.FFI's extern_lib targets.
# The Lean toolchain itself is managed by elan; this shell only
# provides the native C libraries the FFI shims link against.

pkgs.mkShell {
  buildInputs = with pkgs; [
    libsodium         # SHA-256, Blake2b-224/256, Ed25519 verify
    secp256k1         # ECDSA + Schnorr (BIP-340) verification
    blst              # BLS12-381 G1/G2/pairing
    pkg-config        # used by cc to discover the above
  ];

  shellHook = ''
    echo "PlutusCoreBlaster dev shell:"
    echo "  libsodium    $(pkg-config --modversion libsodium)"
    echo "  libsecp256k1 $(pkg-config --modversion libsecp256k1)"
    echo "  libblst      $(pkg-config --modversion libblst 2>/dev/null || echo '(no .pc, headers on NIX_CFLAGS_COMPILE)')"
  '';
}

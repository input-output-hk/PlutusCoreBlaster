#!/usr/bin/env python3
"""Compare the public FFI and pure Lean APIs against independent crypto vectors."""

import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    rows = []
    hashes = {
        "sha2_256": hashlib.sha256,
        "sha3_256": hashlib.sha3_256,
        "blake2b_256": lambda data: hashlib.blake2b(data, digest_size=32),
        "blake2b_224": lambda data: hashlib.blake2b(data, digest_size=28),
        "ripemd_160": lambda data: hashlib.new("ripemd160", data),
    }
    # Cross padding/rate/chunk boundaries, exercise every byte value and embedded NULs.
    for size in [0, 1, 3, 31, 32, 55, 56, 63, 64, 65, 127, 128, 129, 135, 136, 137, 255, 256, 257, 1024]:
        data = bytes((i * 197 + 128) % 256 for i in range(size))
        for name, digest in hashes.items():
            rows.append([name, f"{name}-{size}", data.hex(), "", "", digest(data).hexdigest()])
        rows.append(["keccak_256", f"keccak-{size}", data.hex(), "", "", "either"])
    for name, digest in hashes.items():
        # The public ByteString uses character low bytes, not UTF-8 bytes.
        rows.append([name, f"{name}-unicode", "unicode", "", "", digest(bytes([233, 0, 66])).hexdigest()])
    # Keccak-256 and SHA3-256 must remain distinct (Ethereum/NIST empty-message vectors).
    rows += [["keccak_256", "keccak-empty-known", "", "", "",
              "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"],
             ["keccak_256", "keccak-abc-known", b"abc".hex(), "", "",
              "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"]]
    vectors = json.loads((ROOT / "Tests/Crypto/FFI/ed25519_wycheproof.json").read_text())
    for group in vectors["testGroups"]:
        pk = group["publicKey"]["pk"]
        for test in group["tests"]:
            expected = {"valid": "true", "invalid": "false", "acceptable": "either"}[test["result"]]
            if len(pk) != 64 or len(test["sig"]) != 128:
                expected = "error"  # Plutus wrapper errors, rather than Bool false.
            rows.append(["ed25519", f"wycheproof-{test['tcId']}", pk, test["msg"], test["sig"], expected])
    # Public API size failures and the previously accepted identity forgery.
    identity = "01" + "00" * 31
    for pk, sig in [("", "00" * 64), ("00" * 31, "00" * 64),
                    ("00" * 33, "00" * 64), (identity, "00" * 63), (identity, "00" * 65)]:
        rows.append(["ed25519", f"bad-length-{len(rows)}", pk, "80ff00", sig, "error"])
    rows.append(["ed25519", "identity-forgery", identity, "", identity + "00" * 32, "false"])
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "vectors.tsv"
        path.write_text("\n".join("\t".join(row) for row in rows) + "\n")
        subprocess.run([str(ROOT / ".lake/build/bin/test_crypto_ffi"), str(path)], check=True, timeout=120)


if __name__ == "__main__":
    main()

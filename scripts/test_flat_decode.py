#!/usr/bin/env python3
"""Differential Flat decoder checks. Generated programs are parsed, never evaluated."""
import argparse
import hashlib
import json
from pathlib import Path
import random
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / '.lake/build/bin/test_flat_decode'


class Writer:
    def __init__(self, version=(1, 1, 0), noncanonical=False):
        self.bits = ''
        for n in version:
            self.natural(n, 1 if noncanonical else 0)

    def uint(self, width, n):
        assert 0 <= n < 1 << width
        self.bits += f'{n:0{width}b}'

    def natural(self, n, zero_groups=0):
        assert n >= 0
        groups = []
        while True:
            groups.append(n & 127)
            n >>= 7
            if not n:
                break
        groups += [0] * zero_groups
        for i, group in enumerate(groups):
            self.uint(8, group | (128 if i + 1 < len(groups) else 0))

    def padding(self):
        self.bits += '0' * ((7 - len(self.bits)) % 8) + '1'

    def payload(self, data, unaligned=False):
        if unaligned:
            self.bits += '1'  # Reference accepts this even before a byte boundary.
        else:
            self.padding()
        for start in range(0, len(data), 255):
            chunk = data[start:start + 255]
            self.uint(8, len(chunk))
            for byte in chunk:
                self.uint(8, byte)
        self.uint(8, 0)

    def finish(self):
        self.padding()
        return int(self.bits, 2).to_bytes(len(self.bits) // 8, 'big')


def tags(t):
    if isinstance(t, int):
        return [t]
    if t[0] == 'list':
        return [7, 5] + tags(t[1])
    return [7, 7, 6] + tags(t[1]) + tags(t[2])


def value(w, t, rng, unaligned=False):
    if t == 0:
        n = rng.choice([0, -1, 1, 127, -128, 2**64 - 1, -(2**128)])
        w.natural(2 * n if n >= 0 else -2 * n - 1)
    elif t == 1:
        w.payload(bytes(rng.randrange(256) for _ in range(rng.randrange(35))), unaligned)
    elif t == 2:
        w.payload(rng.choice(['', 'abc', 'éĀ🙂', '\x00']).encode(), unaligned)
    elif t == 3:
        pass
    elif t == 4:
        w.uint(1, rng.randrange(2))
    elif t == 8:
        w.payload(rng.choice([b'\x00', b'\x20', b'\x80', b'\xa0', b'\x40',
            b'\x9f\x01\x20\xff', b'\xd8\x79\x80', b'\xbf\x01\x02\xff',
            b'\xc3\x49\x01' + b'\x00' * 8]), unaligned)
    elif t[0] == 'list':
        for _ in range(rng.randrange(4)):
            w.uint(1, 1)
            value(w, t[1], rng, unaligned)
        w.uint(1, 0)
    else:
        value(w, t[1], rng, unaligned)
        value(w, t[2], rng, unaligned)


def constant(w, t, rng, unaligned=False):
    w.uint(4, 4)
    for tag in tags(t):
        w.uint(1, 1)
        w.uint(4, tag)
    w.uint(1, 0)
    value(w, t, rng, unaligned)


def term(w, depth, rng):
    tag = rng.choice([0, 4, 6, 7] if depth == 0 else list(range(10)))
    if tag == 4:
        constant(w, rng.choice([0, 1, 2, 3, 4, 8, ('list', 8), ('pair', 8, 8)]), rng)
        return
    w.uint(4, tag)
    if tag == 0:
        w.natural(rng.randrange(17))
    elif tag in [1, 2, 5]:
        term(w, depth - 1, rng)
    elif tag == 3:
        term(w, depth - 1, rng)
        term(w, depth - 1, rng)
    elif tag == 7:
        w.uint(7, rng.randrange(128))
    elif tag in [8, 9]:
        if tag == 8:
            w.natural(rng.choice([0, 1, 2**64 - 1, 2**64]))
        else:
            term(w, depth - 1, rng)
        for _ in range(rng.randrange(4)):
            w.uint(1, 1)
            term(w, depth - 1, rng)
        w.uint(1, 0)


def cases(args):
    rng = random.Random(args.seed)
    result = []

    def add(label, data, expected=None):
        result.append((label, data, expected))

    add('empty', b'', False)
    types = [0, 1, 2, 3, 4, 8, ('list', 0), ('list', 3), ('list', 8),
        ('pair', 8, 8), ('list', ('pair', 8, 8)),
        ('pair', ('list', 8), ('pair', 0, 4))]
    for i, t in enumerate(types):
        for unaligned in [False, True]:
            for repeat in range(8):
                w = Writer(noncanonical=repeat % 2 == 1)
                constant(w, t, rng, unaligned)
                add(f'constant-{i}-{unaligned}-{repeat}', w.finish(), True)
    for size in [0, 1, 63, 64, 65, 254, 255, 256, 510, 511, 512]:
        for unaligned in [False, True]:
            w = Writer()
            w.uint(4, 4)
            w.uint(1, 1)
            w.uint(4, 1)
            w.uint(1, 0)
            w.payload(bytes(i % 256 for i in range(size)), unaligned)
            add(f'bytes-{size}-{unaligned}', w.finish(), True)
    w = Writer()
    w.uint(4, 4)
    w.uint(1, 1)
    w.uint(4, 2)
    w.uint(1, 0)
    w.payload(b'\xff')
    add('invalid-utf8', w.finish(), False)
    for version in [(1, 0, 0), (1, 1, 0), (2, 0, 0)]:
        for index in [0, 2**64 - 1, 2**64]:
            w = Writer(version)
            w.uint(4, 8)
            w.natural(index)
            w.uint(1, 0)
            add(f'constr-{version}-{index}', w.finish(), version >= (1, 1, 0) and index < 2**64)
    for index in range(128):
        w = Writer()
        w.uint(4, 7)
        w.uint(7, index)
        add(f'builtin-{index}', w.finish())
    for i in range(args.random_programs):
        w = Writer(rng.choice([(1, 0, 0), (1, 1, 0), (2, 0, 0)]))
        term(w, 4, rng)
        add(f'program-{i}', w.finish())
    # Truncate and corrupt structured encodings, where parsing often reaches deep
    # into constants or nested terms rather than rejecting at the version header.
    structured = list(result)
    for label, data, _ in structured:
        if data:
            add(label + '-short', data[:-1])
            add(label + '-trailing', data + b'\x00', False)
            mutated = bytearray(data)
            pos = rng.randrange(len(mutated))
            mutated[pos] ^= 1 << rng.randrange(8)
            add(label + '-flip', bytes(mutated))
    for i in range(args.random_bytes):
        size = rng.randrange(129)
        add(f'random-{i}', bytes(rng.randrange(256) for _ in range(size)))
    if args.benchmark_root:
        files = sorted((args.benchmark_root / 'data/plutus_use_cases').glob('*.flat'))
        if len(files) != 89:
            raise SystemExit('expected the 89-script reference corpus')
        for path in files:
            data = path.read_bytes()
            add('corpus-' + path.stem, data, True)
            add('corpus-' + path.stem + '-short', data[:-1])
            add('corpus-' + path.stem + '-trailing', data + b'\x00', False)
            for i in range(3):
                mutated = bytearray(data)
                pos = rng.randrange(len(mutated))
                mutated[pos] ^= 1 << rng.randrange(8)
                add(f'corpus-{path.stem}-flip-{i}', bytes(mutated))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--benchmark-root', type=Path)
    parser.add_argument('--seed', type=int, default=63064)
    parser.add_argument('--random-programs', type=int, default=500)
    parser.add_argument('--random-bytes', type=int, default=1000)
    parser.add_argument('--output', type=Path, default=ROOT / 'Benchmark/results/flat-decode/report.json')
    args = parser.parse_args()
    if not BINARY.is_file():
        parser.error("build the parser probe first: lake build test_flat_decode")
    vectors = cases(args)
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / 'vectors.tsv'
        path.write_text(''.join(f'{label}\t{data.hex()}\n' for label, data, _ in vectors))
        run = subprocess.run([str(BINARY), str(path)], capture_output=True, text=True, timeout=180)
    if run.returncode:
        raise SystemExit(run.stderr or 'parser probe failed')
    rows = [line.split('\t') for line in run.stdout.splitlines()]
    if len(rows) != len(vectors):
        raise SystemExit('missing parser probe rows')
    accepted = 0
    for (label, data, expected), row in zip(vectors, rows):
        if len(row) != 2 or row[0] != label or row[1] not in ['accepted', 'rejected']:
            raise SystemExit('invalid parser probe row')
        actual = row[1] == 'accepted'
        if expected is not None and actual != expected:
            raise SystemExit(f'{label}: expected accepted={expected}, got {actual}: {data.hex()}')
        accepted += actual
    report = {'cases': len(vectors), 'accepted': accepted, 'rejected': len(vectors) - accepted,
        'seed': args.seed, 'random_programs': args.random_programs, 'random_bytes': args.random_bytes,
        'vectors_sha256': hashlib.sha256(''.join(f'{label}\t{data.hex()}\n' for label, data, _ in vectors).encode()).hexdigest()}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(f"Complete AST/rejection equivalence: {report['cases']}/{report['cases']}; "
          f"{accepted} accepted, {len(vectors) - accepted} rejected")


if __name__ == '__main__':
    main()

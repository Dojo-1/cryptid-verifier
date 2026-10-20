"""Exact autonomous b-orbit, chunked via pv_mod and real_bridge.

Importing this module does no work. The b-orbit continues even when the associated
counter would halt; use the prediction monitor to report that event explicitly.
Python integers suffice; gmpy2 is an optional acceleration.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import time

try:
    from gmpy2 import mpz as _integer
except ImportError:
    _integer = int


def advance_chunk(b: int, length: int):
    """Return exactly length parities and T^length(b), including length=0."""
    if b < 0 or length < 0:
        raise ValueError("b and length must be nonnegative")
    x = int(b & ((1 << length) - 1))
    correction = 0
    parities = bytearray()
    for i in range(length):
        p = x & 1
        parities.append(p)
        correction = 3 * correction + (1 << i) * (4 - p)
        x = 3 * (x >> 1) + 2 + p
    numerator = _integer(3) ** length * _integer(b) + correction
    end, remainder = divmod(numerator, _integer(1) << length)
    if remainder:
        raise ArithmeticError("real_bridge numerator is not divisible by 2^length")
    return parities, end


def generate_parities(steps: int, start: int = 4, chunk_size: int = 4096):
    """Generate a byte per parity; return (parities, exact final b)."""
    if steps < 0 or start < 0 or chunk_size < 1:
        raise ValueError("steps/start must be nonnegative and chunk_size positive")
    out = bytearray()
    b = _integer(start)
    while len(out) < steps:
        word, b = advance_chunk(b, min(chunk_size, steps - len(out)))
        out.extend(word)
    return out, b


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("steps", type=int)
    parser.add_argument("--start", type=int, default=4)
    parser.add_argument("--chunk-size", type=int, default=4096)
    parser.add_argument("--output", type=Path, help="optional .npy parity array")
    args = parser.parse_args(argv)
    before = time.perf_counter()
    parities, b = generate_parities(args.steps, args.start, args.chunk_size)
    if args.output:
        import numpy as np
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("wb") as stream:
            np.save(stream, np.frombuffer(parities, dtype=np.uint8), allow_pickle=False)
    b_bytes = int(b).to_bytes(max(1, (int(b).bit_length() + 7) // 8), "big")
    print(json.dumps({
        "steps": args.steps, "start": args.start, "chunk_size": args.chunk_size,
        "backend": "gmpy2" if _integer is not int else "python-int",
        "parities_sha256": hashlib.sha256(parities).hexdigest(),
        "final_b_bits": int(b).bit_length(),
        "final_b_big_endian_sha256": hashlib.sha256(b_bytes).hexdigest(),
        "elapsed_seconds": time.perf_counter() - before,
        "output": str(args.output) if args.output else None,
    }, indent=2))


if __name__ == "__main__":
    main()

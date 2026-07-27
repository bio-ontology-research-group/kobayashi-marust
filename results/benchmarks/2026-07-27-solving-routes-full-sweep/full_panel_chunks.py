#!/usr/bin/env python3
"""Deterministic balanced chunks for the ORE full-panel Slurm array."""

from __future__ import annotations

import argparse


def chunk_bounds(total: int, chunks: int, chunk: int) -> tuple[int, int]:
    """Return the half-open item range assigned to ``chunk``.

    Remainder items are assigned one each to the first chunks.  Consequently,
    chunk sizes differ by at most one and every item occurs exactly once.
    """

    if total < 0:
        raise ValueError("total must be non-negative")
    if chunks <= 0:
        raise ValueError("chunks must be positive")
    if not 0 <= chunk < chunks:
        raise ValueError(f"chunk must be in [0, {chunks})")
    base, remainder = divmod(total, chunks)
    start = chunk * base + min(chunk, remainder)
    size = base + (1 if chunk < remainder else 0)
    return start, start + size


def chunk_for_index(total: int, chunks: int, index: int) -> int:
    """Return the unique chunk containing an item index."""

    if not 0 <= index < total:
        raise ValueError(f"index must be in [0, {total})")
    base, remainder = divmod(total, chunks)
    if base == 0:
        return index
    large_span = (base + 1) * remainder
    if index < large_span:
        return index // (base + 1)
    return remainder + (index - large_span) // base


def indices_for_chunk(total: int, chunks: int, chunk: int) -> range:
    start, stop = chunk_bounds(total, chunks, chunk)
    return range(start, stop)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--total", type=int, required=True)
    parser.add_argument("--chunks", type=int, required=True)
    parser.add_argument("--chunk", type=int, required=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    for index in indices_for_chunk(args.total, args.chunks, args.chunk):
        print(index)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

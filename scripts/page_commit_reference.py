#!/usr/bin/env python3
"""Reference implementation of page_commit (MIP-8 ISMC).

Source-of-truth for cross-checking the C++ implementation in
category/execution/monad/db/storage_page.cpp. Used for differential fuzzing.

CLI:
    python3 scripts/page_commit_reference.py            # run self-tests
    python3 scripts/page_commit_reference.py --hex ...  # commit a hex page
    python3 scripts/page_commit_reference.py --stdin    # read raw 4096B from stdin

Requires the `blake3` PyPI package.
"""

from __future__ import annotations

import argparse
import sys

import blake3 as blake3_lib

# ── BLAKE3 constants ────────────────────────────────────────────────────────

# Standard BLAKE3 IV: little-endian encodings of the 8 SHA-256-derived constants.
BLAKE3_IV = bytes.fromhex(
    "67e6096a"  # 0x6A09E667
    "85ae67bb"  # 0xBB67AE85
    "72f36e3c"  # 0x3C6EF372
    "3af54fa5"  # 0xA54FF53A
    "7f520e51"  # 0x510E527F
    "8c68059b"  # 0x9B05688C
    "abd9831f"  # 0x1F83D9AB
    "19cde05b"  # 0x5BE0CD19
)
assert len(BLAKE3_IV) == 32

CHUNK_START = 1
CHUNK_END = 2
DERIVE_KEY_MATERIAL = 64

MSG_PERMUTATION = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]

PAIR_LEAF_KEY = b"ultra_merkle_pair_leaf_domain___"
assert len(PAIR_LEAF_KEY) == 32

PAGE_SLOTS = 128
SLOT_SIZE = 32
PAGE_SIZE = PAGE_SLOTS * SLOT_SIZE  # 4096
NUM_PAIRS = PAGE_SLOTS // 2  # 64


# ── Single-block BLAKE3 compression ─────────────────────────────────────────


def _rotr(x: int, n: int) -> int:
    return ((x >> n) | (x << (32 - n))) & 0xFFFFFFFF


def _g(state: list[int], a: int, b: int, c: int, d: int, mx: int, my: int) -> None:
    state[a] = (state[a] + state[b] + mx) & 0xFFFFFFFF
    state[d] = _rotr(state[d] ^ state[a], 16)
    state[c] = (state[c] + state[d]) & 0xFFFFFFFF
    state[b] = _rotr(state[b] ^ state[c], 12)
    state[a] = (state[a] + state[b] + my) & 0xFFFFFFFF
    state[d] = _rotr(state[d] ^ state[a], 8)
    state[c] = (state[c] + state[d]) & 0xFFFFFFFF
    state[b] = _rotr(state[b] ^ state[c], 7)


def _round(state: list[int], m: list[int]) -> None:
    _g(state, 0, 4, 8, 12, m[0], m[1])
    _g(state, 1, 5, 9, 13, m[2], m[3])
    _g(state, 2, 6, 10, 14, m[4], m[5])
    _g(state, 3, 7, 11, 15, m[6], m[7])
    _g(state, 0, 5, 10, 15, m[8], m[9])
    _g(state, 1, 6, 11, 12, m[10], m[11])
    _g(state, 2, 7, 8, 13, m[12], m[13])
    _g(state, 3, 4, 9, 14, m[14], m[15])


def _permute(m: list[int]) -> list[int]:
    return [m[MSG_PERMUTATION[i]] for i in range(16)]


def blake3_compress(cv: bytes, block: bytes, flags: int) -> bytes:
    """BLAKE3 single-block compression with counter=0 and block_len=64.

    Returns the new 32-byte chaining value. Mirrors blake3_compress_in_place.
    """
    assert len(cv) == 32 and len(block) == 64

    cv_words = [int.from_bytes(cv[i:i + 4], "little") for i in range(0, 32, 4)]
    iv_words = [int.from_bytes(BLAKE3_IV[i:i + 4], "little") for i in range(0, 32, 4)]

    state = [
        cv_words[0], cv_words[1], cv_words[2], cv_words[3],
        cv_words[4], cv_words[5], cv_words[6], cv_words[7],
        iv_words[0], iv_words[1], iv_words[2], iv_words[3],
        0, 0, 64, flags,
    ]

    m = [int.from_bytes(block[i:i + 4], "little") for i in range(0, 64, 4)]
    for _ in range(6):
        _round(state, m)
        m = _permute(m)
    _round(state, m)

    out = [state[i] ^ state[i + 8] for i in range(8)]
    return b"".join(w.to_bytes(4, "little") for w in out)


# ── Cached LEAF_IV and the three building-block hashes ──────────────────────


def _derive_leaf_iv() -> bytes:
    block = PAIR_LEAF_KEY + b"\x00" * 32
    return blake3_compress(BLAKE3_IV, block, DERIVE_KEY_MATERIAL)


LEAF_IV = _derive_leaf_iv()


def hash_leaf(pair_64: bytes) -> bytes:
    return blake3_compress(LEAF_IV, pair_64, DERIVE_KEY_MATERIAL)


def hash_parent(left_32: bytes, right_32: bytes) -> bytes:
    return blake3_compress(BLAKE3_IV, left_32 + right_32, CHUNK_START | CHUNK_END)


def hash_seal(slot_bitmap: int, root_32: bytes | None) -> bytes:
    """BLAKE3(bitmap_le_16 [|| root_32])."""
    buf = slot_bitmap.to_bytes(16, "little")
    if root_32 is not None:
        buf += root_32
    return blake3_lib.blake3(buf).digest()


# ── ISMC commitment ─────────────────────────────────────────────────────────


def compute_slot_bitmap(page: bytes) -> int:
    bm = 0
    for i in range(PAGE_SLOTS):
        if page[i * SLOT_SIZE:(i + 1) * SLOT_SIZE] != b"\x00" * SLOT_SIZE:
            bm |= 1 << i
    return bm


def derive_pair_bitmap(slot_bitmap: int) -> int:
    pair = 0
    for i in range(NUM_PAIRS):
        if slot_bitmap & (0b11 << (2 * i)):
            pair |= 1 << i
    return pair


def page_commit(page: bytes) -> bytes:
    assert len(page) == PAGE_SIZE

    slot_bitmap = compute_slot_bitmap(page)
    if slot_bitmap == 0:
        return hash_seal(0, None)

    pair_bitmap = derive_pair_bitmap(slot_bitmap)

    # Phase 1: hash each active pair-leaf.
    scratch: dict[int, bytes] = {}
    bits = pair_bitmap
    while bits:
        idx = (bits & -bits).bit_length() - 1
        scratch[idx] = hash_leaf(page[idx * 64:(idx + 1) * 64])
        bits &= bits - 1

    # Phase 2: bitmap-driven bottom-up merge.
    bm = pair_bitmap
    for bit in range(6):
        if bin(bm).count("1") <= 1:
            break
        merges: list[tuple[int, int]] = []
        bits = bm
        prev = -1
        while bits:
            pos = (bits & -bits).bit_length() - 1
            bits &= bits - 1
            sibling = (
                prev != -1
                and (prev >> (bit + 1)) == (pos >> (bit + 1))
                and ((prev >> bit) & 1) == 0
            )
            if sibling:
                merges.append((prev, pos))
                prev = -1
            else:
                prev = pos
        for left, right in merges:
            scratch[left] = hash_parent(scratch[left], scratch[right])
            del scratch[right]
            bm &= ~(1 << right)

    # Phase 3: seal.
    root_idx = (bm & -bm).bit_length() - 1
    return hash_seal(slot_bitmap, scratch[root_idx])


# ── Reference vectors (must match the C++ implementation) ───────────────────


def _slot0_one() -> bytes:
    # bytes32_t{0x01} invokes the uint64_t ctor (literal 0x01 is int) which
    # stores the value big-endian in the last 8 bytes of the slot, so byte
    # 31 of slot 0 = 0x01.
    page = bytearray(PAGE_SIZE)
    page[31] = 0x01
    return bytes(page)


def _slot127_one() -> bytes:
    # Same as above; byte 31 of slot 127 = page byte 127*32 + 31 = 4095.
    page = bytearray(PAGE_SIZE)
    page[127 * SLOT_SIZE + 31] = 0x01
    return bytes(page)


def _full_page() -> bytes:
    # full_page[i] = bytes32_t{static_cast<uint64_t>(i + 1)} stores (i+1)
    # big-endian in the last 8 bytes of the slot.
    page = bytearray(PAGE_SIZE)
    for i in range(PAGE_SLOTS):
        page[i * SLOT_SIZE + 24:(i + 1) * SLOT_SIZE] = (i + 1).to_bytes(8, "big")
    return bytes(page)


REFERENCE_VECTORS: dict[str, tuple[bytes, str]] = {
    "zero_page": (
        b"\x00" * PAGE_SIZE,
        "e572dff82304700b856a555ac3a4558d0df3646a3727816500270a93c66aac1e",
    ),
    "slot0_one": (
        _slot0_one(),
        "80218c63919cd8c68aa9a5c0117bb8b46eb02099a7ce0b47a36e7b21658cc9f9",
    ),
    "slot127_one": (
        _slot127_one(),
        "39a2175f8fac8fbf447383b46ff40e03673b388c05c87e50ed7b3f1a810c98d8",
    ),
    "full_page": (
        _full_page(),
        "e5a642261a2c2dedebd68ebd42237f2210d1eee94553d677d425dc3a46c7a687",
    ),
}


# ── CLI ─────────────────────────────────────────────────────────────────────


def selftest() -> int:
    failures = 0
    for name, (page, expected) in REFERENCE_VECTORS.items():
        got = page_commit(page).hex()
        ok = got == expected
        print(f"[{'OK' if ok else 'FAIL'}] {name}: {got}")
        if not ok:
            print(f"        expected: {expected}")
            failures += 1
    return 0 if failures == 0 else 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    g = parser.add_mutually_exclusive_group()
    g.add_argument("--hex", help="page bytes encoded as 8192 hex chars")
    g.add_argument("--stdin", action="store_true", help="read 4096 raw bytes from stdin")
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args()

    if args.hex is not None:
        page = bytes.fromhex(args.hex)
    elif args.stdin:
        page = sys.stdin.buffer.read()
    else:
        return selftest()

    if len(page) != PAGE_SIZE:
        print(f"error: expected {PAGE_SIZE}-byte page, got {len(page)}", file=sys.stderr)
        return 2

    print(page_commit(page).hex())
    return 0


if __name__ == "__main__":
    sys.exit(main())

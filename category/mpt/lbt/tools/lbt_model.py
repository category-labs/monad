# Copyright (C) 2025-26 Category Labs, Inc.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

"""An independent model of the binary-trie commitment in docs/binary_trie.md.

Written from the document, not the C++, with its own BLAKE3 compression. It
prints the commitments the C++ tests pin, for every pin whose inputs do not
depend on libstdc++'s shuffle.
"""

import struct

M32 = 0xFFFFFFFF
M64 = 0xFFFFFFFFFFFFFFFF
IV = [0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
      0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]
PERM = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]
CHUNK_START, CHUNK_END, ROOT, KEYED_HASH, DERIVE_KEY_MATERIAL = 1, 2, 8, 16, 64


def rotr(x, n):
    return ((x >> n) | (x << (32 - n))) & M32


def g(s, a, b, c, d, x, y):
    s[a] = (s[a] + s[b] + x) & M32
    s[d] = rotr(s[d] ^ s[a], 16)
    s[c] = (s[c] + s[d]) & M32
    s[b] = rotr(s[b] ^ s[c], 12)
    s[a] = (s[a] + s[b] + y) & M32
    s[d] = rotr(s[d] ^ s[a], 8)
    s[c] = (s[c] + s[d]) & M32
    s[b] = rotr(s[b] ^ s[c], 7)


def compress(cv, block, block_len, counter, flags):
    m = list(struct.unpack('<16I', block))
    s = list(cv) + IV[:4] + [counter & M32, counter >> 32, block_len, flags]
    for _ in range(7):
        g(s, 0, 4, 8, 12, m[0], m[1])
        g(s, 1, 5, 9, 13, m[2], m[3])
        g(s, 2, 6, 10, 14, m[4], m[5])
        g(s, 3, 7, 11, 15, m[6], m[7])
        g(s, 0, 5, 10, 15, m[8], m[9])
        g(s, 1, 6, 11, 12, m[10], m[11])
        g(s, 2, 7, 8, 13, m[12], m[13])
        g(s, 3, 4, 9, 14, m[14], m[15])
        m = [m[i] for i in PERM]
    return [s[i] ^ s[i + 8] for i in range(8)]


def cv_bytes(cv):
    return struct.pack('<8I', *cv)


def derive_iv(domain):
    return compress(IV, domain + bytes(32), 64, 0, DERIVE_KEY_MATERIAL)


LEAF_IV = derive_iv(b'monad_lbt_leaf_domain___________')
VALUE_KEY = derive_iv(b'monad_lbt_value_domain__________')
ZERO = bytes(32)


def value_hash(data):
    assert len(data) <= 1024
    cv = VALUE_KEY
    blocks = [data[i:i + 64] for i in range(0, len(data), 64)] or [b'']
    for i, block in enumerate(blocks):
        flags = KEYED_HASH
        if i == 0:
            flags |= CHUNK_START
        if i == len(blocks) - 1:
            flags |= CHUNK_END | ROOT
        cv = compress(cv, block.ljust(64, b'\0'), len(block), 0, flags)
    return cv_bytes(cv)


def merge_hash(left, right):
    return cv_bytes(compress(IV, left + right, 64, 0, CHUNK_START | CHUNK_END))


def leaf_hash(nibbles, value):
    key = bytearray(32)
    for i, n in enumerate(nibbles):
        key[i // 2] |= (n << 4) if i % 2 == 0 else n
    return cv_bytes(compress(LEAF_IV, bytes(key) + value, 64, len(nibbles),
                             CHUNK_START | CHUNK_END))


# A commitment is (hash, is_leaf); the type is carried beside the hash.
def leaf(h):
    return (h, True)


def internal(h):
    return (h, False)


def merge(left, right):
    return internal(merge_hash(left[0], right[0]))


def merge_one_sided(child, child_is_right):
    assert not child[1]
    if child_is_right:
        return internal(merge_hash(ZERO, child[0]))
    return internal(merge_hash(child[0], ZERO))


def branch_commit(entries, bits):
    """entries: [(index, commitment)] ascending; reduces top-down."""
    def reduce(es, bit):
        if len(es) == 1 and (bit < 0 or es[0][1][1]):
            return es[0][1]
        left = [e for e in es if not (e[0] >> bit) & 1]
        right = [e for e in es if (e[0] >> bit) & 1]
        if not left or not right:
            return merge_one_sided(reduce(es, bit - 1), not left)
        return merge(reduce(left, bit - 1), reduce(right, bit - 1))
    return reduce(entries, bits - 1)


def commit_path(units, node):
    for u in reversed(units):
        for bit in range(4):
            node = merge_one_sided(node, (u >> bit) & 1 == 1)
    return node


def nibbles_of(bs):
    return [n for b in bs for n in (b >> 4, b & 0xF)]


def trie_root(leaves):
    """leaves: {32-byte key: 32-byte leaf value}; the bit-by-bit trie."""
    if not leaves:
        return ZERO
    keys = sorted(leaves)

    def bit_of(k, i):
        return (k[i // 8] >> (7 - i % 8)) & 1

    def sub(ks, bit):
        if len(ks) == 1:
            return leaf(leaf_hash(nibbles_of(ks[0]), leaves[ks[0]]))
        left = [k for k in ks if not bit_of(k, bit)]
        right = [k for k in ks if bit_of(k, bit)]
        if not left or not right:
            return merge_one_sided(sub(ks, bit + 1), not left)
        return merge(sub(left, bit + 1), sub(right, bit + 1))
    return sub(keys, 0)[0]


class MT19937_64:
    def __init__(self, seed):
        self.mt = [seed & M64]
        for i in range(1, 312):
            prev = self.mt[-1]
            self.mt.append((6364136223846793005 * (prev ^ (prev >> 62)) + i)
                           & M64)
        self.index = 312

    def __call__(self):
        if self.index == 312:
            for i in range(312):
                x = ((self.mt[i] & 0xFFFFFFFF80000000)
                     | (self.mt[(i + 1) % 312] & 0x7FFFFFFF))
                xa = x >> 1
                if x & 1:
                    xa ^= 0xB5026F5AA96619E9
                self.mt[i] = self.mt[(i + 156) % 312] ^ xa
            self.index = 0
        y = self.mt[self.index]
        self.index += 1
        y ^= (y >> 29) & 0x5555555555555555
        y ^= (y << 17) & 0x71D67FFFEB880000
        y ^= (y << 37) & 0xFFF7EEE000000000
        y ^= y >> 43
        return y & M64


def h(x):
    # bytes32_t{uint64_t}: big-endian in the last 8 bytes.
    return x.to_bytes(32, 'big')


def random_key(rng):
    return bytes(rng() & 0xFF for _ in range(32))


def value_of(x):
    # The oracle tests' values: 33 bytes, so every one is hashed.
    return value_hash(bytes([x & 0xFF]) * 32 + bytes([(x >> 8) & 0xFF]))


def key_with(**byte_values):
    k = bytearray(32)
    for name, v in byte_values.items():
        k[int(name[1:])] = v
    return bytes(k)


def oracle_pins():
    pins = {}
    rng = MT19937_64(1)
    a, b = random_key(rng), random_key(rng)
    pins['SINGLE_AND_TWO_KEYS'] = trie_root({a: value_of(1), b: value_of(2)})

    pins['LONG_SHARED_PREFIX'] = trie_root({
        bytes([0x77] * 32): value_of(1),
        bytes([0x77] * 31 + [0x78]): value_of(2),
        bytes([0x77] * 31 + [0x87]): value_of(3)})

    pins['ERASE_LEAVES_LONE_BRANCH_CHILD'] = trie_root({
        key_with(b0=0x56, b1=0x71): value_of(1),
        key_with(b0=0x56, b1=0x72): value_of(2)})

    rng = MT19937_64(3)
    first = random_key(rng)
    pins['ERASE_TO_SINGLE_KEY'] = trie_root({first: value_of(0)})

    rng = MT19937_64(4)
    random_key(rng)
    b = random_key(rng)
    pins['ERASE_ALL_THEN_REINSERT'] = trie_root({b: value_of(5)})

    pins['BINDS_BITS_ABOVE_ATTACH_POINT'] = trie_root({
        key_with(b0=0x15): value_of(1), key_with(b0=0x80): value_of(2)})

    pins['ERASE_LIFTS_LEAF_FROM_DISK'] = trie_root({
        key_with(b0=0x2e): value_of(2), key_with(b0=0x70): value_of(3)})

    pins['ERASE_LIFTS_LEAF_ACROSS_LEVELS'] = trie_root({
        bytes([0x33] * 32): value_of(1), key_with(b0=0x90): value_of(3)})

    rng = MT19937_64(6)
    pins['DB_ROOT_200_KEYS'] = trie_root(
        {random_key(rng): value_of(i) for i in range(200)})
    return pins


def commit_pins():
    return {
        'LEAF_FOUR_NIBBLES': leaf_hash(nibbles_of(bytes([0x12, 0x34])), h(7)),
        'VALUE_HASH_ABC': value_hash(b'abc'),
        'FULL_KEY_LEAF': leaf_hash(nibbles_of(bytes(range(32))), h(7)),
        'ADJACENT_LEAVES': branch_commit(
            [(0, leaf(h(1))), (1, leaf(h(2)))], 4)[0],
        'ADJACENT_INTERNALS': branch_commit(
            [(0, internal(h(1))), (1, internal(h(2)))], 4)[0],
        'SPLIT_LEAVES': branch_commit(
            [(0, leaf(h(1))), (8, leaf(h(2)))], 4)[0],
        'LEAF_AND_INTERNAL': branch_commit(
            [(0, leaf(h(1))), (8, internal(h(2)))], 4)[0],
        'LONE_INTERNAL': branch_commit([(11, internal(h(4)))], 4)[0],
        'PATH_ONE_UNIT': commit_path([0x5], internal(h(9)))[0],
        'PATH_TWO_UNITS': commit_path([0x1, 0x2], internal(h(9)))[0],
    }


if __name__ == '__main__':
    for name, value in {**commit_pins(), **oracle_pins()}.items():
        print(f'PIN_{name} 0x{value.hex()}')

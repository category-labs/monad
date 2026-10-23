#!/usr/bin/env python3
"""Generates a MONAD_NINE blockchain test for the graph eval precompile's
evalGraph and evalGraphInto from a short text description of a graph and of
calls to it.

The graph is compiled to graphcode and deployed as an account's code in the
genesis state. Each call is a transaction to a caller contract of its own,
which forwards evalGraph(graph address, inputs), or evalGraphInto(graph
address, inputs, outputs), to the precompile and records the outcome in
storage. The expected outcomes are computed here by a reference evaluator,
independently of the C++ implementation: the outputs if the graph runs,
otherwise the error message the precompile reverts with, and for evalGraphInto
the caller's storage afterwards. Opcodes, dtype ids, tags, error messages, the
selectors and the magic number are read from the C++ sources rather than
copied, so they can't drift.

One statement per line. `#` starts a comment, and a statement with unclosed
brackets, or ending in a comma, continues onto the next line. Comment lines at
the very top become the fixture's description.

    input x: int8[2, 3]             a graph input, in calldata order; int8[]
                                    is a scalar
    y = add(x, x)                   an op, whose result is the node y
    output y, x                     the graph's outputs, in order
    call example                    a call, with CALL, followed by a value for
                                    each input:
        x = [[1, 2, 3], [4, 5, 6]]  a literal, with the declared dtype and the
                                    shape of the nesting, or
        x = int16[2, 3] [[...]]     with both explicit, e.g. to check that the
                                    precompile rejects a mismatch
        x = code(0xda7a, 1)         the tensor at an offset in an account's
                                    code, as tensorref reads it
        x = storage(256)            the tensor in the caller's storage, in the
                                    contiguous slots from a slot on: in order,
                                    32 bytes to a slot, each slot's first byte
                                    its most significant
        x = raw(0, 3, 0x00ff)       a byte order, location and payload as they
                                    are, e.g. to check that the precompile
                                    rejects invalid ones
                                    A reference's header is the declared type,
                                    or a type before it, as for literals. Any
                                    value but raw can start with `little`, for
                                    little-endian elements
        storage 256 = int8[2] [1, 2]
                                    before the call, the caller's slots from a
                                    slot on hold a tensor's elements, as above,
                                    big-endian unless after `little`, or
                                    0x<hex>, these bytes
        into storage(512), little storage(768), literal
                                    the call is evalGraphInto, with these
                                    output references, raw ones too: stored
                                    from a slot, or returned, for literal,
                                    big-endian unless after `little`
    call example staticcall         a call with STATICCALL, or delegatecall, or
                                    static delegatecall: a DELEGATECALL from a
                                    static context. Under DELEGATECALL, storage
                                    references are to the caller's storage,
                                    whose slots from 0 also record the call
    data 0xda7a: int8[2] [1, 2], int64[] 7
                                    an account in the genesis state whose code
                                    holds tensors, for tensorref: a 0x00 byte,
                                    then each tensor encoded as a literal is,
                                    one after another; here the first is at
                                    offset 1 and the second at offset 7
    data 0xda7b: 0x00ff             an account with exactly this code

Ops, whose arguments are nodes unless noted; ops.hpp has the details. add, sub,
mul, qmul, qdiv, max, min, greater, ge, equal and where broadcast their
operands' shapes together as numpy does. The q ops read their operands as fixed
point, with the number of fractional bits given, at most 63.

    literal(int8[2] [1, 2])         a constant
    tensorref(int8[2], 0xda7a, 1)   the tensor at a byte offset in an account's
                                    code, counted from the code's start, as a
                                    data statement puts it there; fails unless
                                    the code starts with 0x00 and a tensor of
                                    the type given is at the offset
    add(a, b)  sub(a, b)            same dtype; wraps on overflow
    mul(a, b)                       same dtype; the product in the type twice as
                                    wide, or wrapping for 64-bit types
    max(a, b)  min(a, b)            same dtype
    greater(a, b)  ge(a, b)  equal(a, b)
                                    same dtype; uint8 0 or 1
    where(condition, a, b)          uint8 condition; a and b the same dtype
    div(a, 16)                      a nonzero int64 denominator; truncates
                                    toward zero, and wraps on overflow
    matmul(a, b)                    int8 matrices; an int32 product
    argmax(a)                       the row-major index of the first largest
                                    element, a scalar of a's dtype
    reshape(a, [3, 2])              a shape with the same element count
    saturate(a, uint8)              a dtype to convert to, clamping
    expand(a, [4, 2, 3])            a shape to broadcast to, as
                                    numpy.broadcast_to does
    cumsum(a, 0)                    an axis to sum along; wraps on overflow
    reducesum(a, 1)  reducemax(a, 1)
                                    an axis to reduce, which stays, with length
                                    1; reducesum wraps on overflow, and is 0
                                    along an empty axis, where reducemax fails
    qmul(a, b, 48)                  same dtype; a * b / 2^48, rounding down and
                                    wrapping on overflow
    qdiv(a, b, 48)                  same dtype; a * 2^48 / b, truncating toward
                                    zero and wrapping; fails if b has a zero
    qmatmul(a, b, 48, int64)        matrices of the same dtype; each element's
                                    products summed, wrapping at 128 bits, then
                                    divided by 2^48, rounding down, and wrapped
                                    to the dtype given
    qexp(a, 48)  qinvsqrt(a, 48)    e^a and 1/sqrt(a), rounding down and
                                    saturating; qinvsqrt fails if a has an
                                    element that isn't positive
    gather(a, indices, 0)           the slices of a along an axis at each of
                                    indices, of any dtype, as numpy.take does;
                                    fails if an index isn't in [0, length)
    concat(a, b, 0)                 a and b joined along an axis; same dtype and
                                    rank, and the same dimensions but that one

Usage:
    ./graph_fixture.py example.graph [-o example.json]
    ./graph_fixture.py --from-json mnist.json [-o mnist.graph]

The second form converts a graph in the JSON form of mnist.json, with op names
as in graph.hpp, to this format instead, naming node i t{i}. It still needs
calls added before it can make a fixture.
"""

import argparse
import ast
import functools
import hashlib
import hmac
import itertools
import json
import math
import operator
import re
import struct
from collections import namedtuple
from pathlib import Path

#
# Ethereum: Keccak-256, RLP, tries, transaction signing, EVM assembly, ABI
# encoding and blockchain tests
#

# This script is in the repository's scripts/
REPO_ROOT = Path(__file__).resolve().parent.parent

# Prague system contracts (EIP-2935, 4788, 6110, 7002, 7251) are copied from
# an existing Monad fixture so they match what the filler deploys
SYSTEM_CONTRACTS_FIXTURE = (
    REPO_ROOT / "build/src/MonadSpecTestFixtures/blockchain_tests/for_monad_nine"
    "/monad_nine/mip4_checkreservebalance/transfers"
    "/smoke_checkreservebalance.json"
)
HISTORY_STORAGE_ADDRESS = "0x0000f90827f1c53a10cb7a02335b175320002935"
BEACON_ROOTS_ADDRESS = "0x000f3df6d732807ef1319fb7b8bb8522d0beac02"
SYSTEM_CONTRACT_ADDRESSES = [
    HISTORY_STORAGE_ADDRESS,
    "0x0000bbddc7ce488642fb579f8b00f3a590007251",
    "0x00000961ef480eb55e80d19ad83579a64c007002",
    "0x00000000219ab540356cbb839cbe05303d7705fa",
    BEACON_ROOTS_ADDRESS,
]
HISTORY_SERVE_WINDOW = 8191
BEACON_ROOTS_HISTORY_BUFFER_LENGTH = 8191

CHAIN_ID = 143
NETWORK = "MONAD_NINE"
COINBASE = bytes.fromhex("2adc25665018aa1fe0e6bc666dac8fc2697ff9ba")
BLOCK_GAS_LIMIT = 0x07270E00
BASE_FEE = 7
TIMESTAMP = 12

SENDER_KEY = 0x45A915E4D060149EB4365960E6A7A45F334393093061116B197E3240065FF2D8
SENDER_BALANCE = 10**19
GAS_PRICE = 10
GRAPH_EVAL_ADDRESS = 0x1002
# Gas forwarded to the precompile. Fixed rather than GAS so a failing call
# (which consumes everything it is given) leaves enough to record the result.
PRECOMPILE_CALL_GAS = 100_000

EMPTY_TRIE_ROOT = bytes.fromhex(
    "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
)
EMPTY_LIST_HASH = bytes.fromhex(
    "1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"
)
# EIP-7685 hash of an empty request list
EMPTY_REQUESTS_HASH = hashlib.sha256(b"").digest()

_MASK64 = (1 << 64) - 1
_KECCAK_RC = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A,
    0x8000000080008000, 0x000000000000808B, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008A,
    0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
    0x000000000000800A, 0x800000008000000A, 0x8000000080008081,
    0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]
# Rotation offsets, indexed [x][y]
_KECCAK_ROT = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
]


def _rotl64(v, n):
    return ((v << n) | (v >> (64 - n))) & _MASK64


def _keccak_f(a):
    # Lane (x, y) is at index x + 5 * y
    for rc in _KECCAK_RC:
        c = [a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20]
             for x in range(5)]
        d = [c[(x - 1) % 5] ^ _rotl64(c[(x + 1) % 5], 1) for x in range(5)]
        a = [a[i] ^ d[i % 5] for i in range(25)]
        b = [0] * 25
        for x in range(5):
            for y in range(5):
                b[y + 5 * ((2 * x + 3 * y) % 5)] = _rotl64(
                    a[x + 5 * y], _KECCAK_ROT[x][y])
        a = [b[i] ^ (~b[(i + 1) % 5 + i - i % 5] & b[(i + 2) % 5 + i - i % 5])
             for i in range(25)]
        a[0] ^= rc
    return a


def keccak256(data):
    rate = 136
    pad = rate - len(data) % rate
    padded = bytes(data) + (b"\x81" if pad == 1
                            else b"\x01" + b"\x00" * (pad - 2) + b"\x80")
    state = [0] * 25
    for offset in range(0, len(padded), rate):
        for i in range(rate // 8):
            state[i] ^= int.from_bytes(
                padded[offset + 8 * i:offset + 8 * i + 8], "little")
        state = _keccak_f(state)
    return b"".join(lane.to_bytes(8, "little") for lane in state[:4])

def be(n):
    """Minimal big-endian encoding of a non-negative int; 0 is empty"""
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def _rlp_length_prefix(length, offset):
    if length < 56:
        return bytes([offset + length])
    encoded = be(length)
    return bytes([offset + 55 + len(encoded)]) + encoded


class Rlp(bytes):
    """Already RLP-encoded; embedded as is"""


def rlp(item):
    if isinstance(item, Rlp):
        return bytes(item)
    if isinstance(item, int):
        item = be(item)
    if isinstance(item, (bytes, bytearray)):
        if len(item) == 1 and item[0] < 0x80:
            return bytes(item)
        return _rlp_length_prefix(len(item), 0x80) + bytes(item)
    payload = b"".join(rlp(x) for x in item)
    return _rlp_length_prefix(len(payload), 0xC0) + payload

def _hex_prefix(nibbles, leaf):
    flag = 2 if leaf else 0
    if len(nibbles) % 2:
        first, nibbles = [(flag + 1) << 4 | nibbles[0]], nibbles[1:]
    else:
        first = [flag << 4]
    return bytes(first + [nibbles[i] << 4 | nibbles[i + 1]
                          for i in range(0, len(nibbles), 2)])


def _trie_node(items):
    """Node for a list of (nibbles, value) with distinct keys"""
    if len(items) == 1:
        key, value = items[0]
        return [_hex_prefix(key, leaf=True), value]
    prefix = 0
    shortest = min(len(key) for key, _ in items)
    while prefix < shortest and len({key[prefix] for key, _ in items}) == 1:
        prefix += 1
    if prefix:
        child = _trie_node([(key[prefix:], value) for key, value in items])
        return [_hex_prefix(items[0][0][:prefix], leaf=False),
                _trie_ref(child)]
    branch = [b""] * 17
    for nibble in range(16):
        children = [(key[1:], value) for key, value in items
                    if key and key[0] == nibble]
        if children:
            branch[nibble] = _trie_ref(_trie_node(children))
    for key, value in items:
        if not key:
            branch[16] = value
    return branch


def _trie_ref(node):
    """Nodes shorter than 32 bytes are embedded rather than hashed"""
    encoded = rlp(node)
    return Rlp(encoded) if len(encoded) < 32 else keccak256(encoded)


def trie_root(mapping):
    if not mapping:
        return EMPTY_TRIE_ROOT
    items = [([n for b in key for n in (b >> 4, b & 0xF)], value)
             for key, value in mapping.items()]
    return keccak256(rlp(_trie_node(items)))


def list_trie_root(values):
    """Transactions/receipts trie: keyed by rlp(index)"""
    return trie_root({rlp(i): v for i, v in enumerate(values)})


@functools.lru_cache(maxsize=None)
def code_hash(code_hex):
    # Cached: the big fixture's data contracts are ~1 MB of code, hashed for
    # both pre and post state
    return keccak256(bytes.fromhex(code_hex.removeprefix("0x")))


def state_root(accounts):
    """Plain Ethereum state root of fixture-format accounts"""
    leaves = {}
    for address, account in accounts.items():
        storage = {
            keccak256(word(int(k, 16))): rlp(int(v, 16))
            for k, v in account["storage"].items() if int(v, 16) != 0}
        leaves[keccak256(bytes.fromhex(address.removeprefix("0x")))] = rlp([
            int(account["nonce"], 16), int(account["balance"], 16),
            trie_root(storage), code_hash(account["code"])])
    return trie_root(leaves)

_P = 2**256 - 2**32 - 977
_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
_G = (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
      0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)


def _point_add(p, q):
    if p is None:
        return q
    if q is None:
        return p
    if p[0] == q[0] and (p[1] + q[1]) % _P == 0:
        return None
    if p == q:
        slope = 3 * p[0] * p[0] * pow(2 * p[1], -1, _P) % _P
    else:
        slope = (q[1] - p[1]) * pow(q[0] - p[0], -1, _P) % _P
    x = (slope * slope - p[0] - q[0]) % _P
    return x, (slope * (p[0] - x) - p[1]) % _P


def _point_mul(k, p=_G):
    result = None
    while k:
        if k & 1:
            result = _point_add(result, p)
        p = _point_add(p, p)
        k >>= 1
    return result


def _rfc6979_nonce(key, digest):
    x = key.to_bytes(32, "big")
    h = (int.from_bytes(digest, "big") % _N).to_bytes(32, "big")
    v = b"\x01" * 32
    k = b"\x00" * 32
    k = hmac.new(k, v + b"\x00" + x + h, hashlib.sha256).digest()
    v = hmac.new(k, v, hashlib.sha256).digest()
    k = hmac.new(k, v + b"\x01" + x + h, hashlib.sha256).digest()
    v = hmac.new(k, v, hashlib.sha256).digest()
    while True:
        v = hmac.new(k, v, hashlib.sha256).digest()
        nonce = int.from_bytes(v, "big")
        if 1 <= nonce < _N:
            return nonce
        k = hmac.new(k, v + b"\x00", hashlib.sha256).digest()
        v = hmac.new(k, v, hashlib.sha256).digest()


def sign(key, digest):
    """Deterministic (RFC 6979), low-s ECDSA; returns (r, s, recovery id)"""
    nonce = _rfc6979_nonce(key, digest)
    point = _point_mul(nonce)
    r = point[0] % _N
    s = pow(nonce, -1, _N) * (int.from_bytes(digest, "big") + r * key) % _N
    assert r != 0 and s != 0 and point[0] < _N
    recovery_id = point[1] & 1
    if s > _N // 2:
        s = _N - s
        recovery_id ^= 1
    return r, s, recovery_id


def address_of(key):
    x, y = _point_mul(key)
    return keccak256(x.to_bytes(32, "big") + y.to_bytes(32, "big"))[12:]

def assemble(program):
    """Assembles a list of opcode bytes, (push opcode, value or label) pairs,
    label definitions (strings) and raw data (bytes)"""
    labels = {}
    offset = 0
    for item in program:
        if isinstance(item, str):
            labels[item] = offset
        elif isinstance(item, tuple):
            offset += 1 + item[0] - 0x5F
        elif isinstance(item, bytes):
            offset += len(item)
        else:
            offset += 1
    code = bytearray()
    for item in program:
        if isinstance(item, tuple):
            push, arg = item
            width = push - 0x5F
            value = labels[arg] if isinstance(arg, str) else arg
            code += bytes([push]) + value.to_bytes(width, "big")
        elif isinstance(item, bytes):
            code += item
        elif not isinstance(item, str):
            code.append(item)
    return bytes(code)


PUSH0, PUSH1, PUSH2, PUSH3, PUSH20 = 0x5F, 0x60, 0x61, 0x62, 0x73


def push(value):
    """The narrowest PUSHn of `value`"""
    return (PUSH0 + max(1, (value.bit_length() + 7) // 8), value)

# Forwards its calldata to the graph eval precompile and records the call:
# slot 0 = success, slot 1 = return data size, slot 2 + i = return data word i
CALLER_CODE = assemble([
    0x36, PUSH0, PUSH0, 0x37,           # CALLDATACOPY(0, 0, CALLDATASIZE)
    PUSH0, PUSH0, 0x36, PUSH0, PUSH0,   # out 0/0, in 0/CALLDATASIZE, value 0
    (PUSH2, GRAPH_EVAL_ADDRESS),
    (PUSH3, PRECOMPILE_CALL_GAS),
    0xF1,                               # CALL
    PUSH0, 0x55,                        # SSTORE(0, success)
    0x3D, (PUSH1, 1), 0x55,             # SSTORE(1, RETURNDATASIZE)
    0x3D, PUSH0, PUSH0, 0x3E,           # RETURNDATACOPY(0, 0, RETURNDATASIZE)
    PUSH0,                              # i = 0 (byte offset)
    "loop", 0x5B,
    0x3D, 0x81, 0x10, 0x15,             # !(i < RETURNDATASIZE)
    (PUSH1, "end"), 0x57,               # JUMPI end
    0x80, 0x51,                         # MLOAD(i)
    0x81, (PUSH1, 5), 0x1C,             # i >> 5
    (PUSH1, 2), 0x01, 0x55,             # SSTORE(2 + i / 32, word)
    (PUSH1, 32), 0x01,                  # i += 32
    (PUSH1, "loop"), 0x56,              # JUMP loop
    "end", 0x5B, 0x00,
])

def word(n):
    return n.to_bytes(32, "big")


def pad32(data):
    return data + b"\x00" * (-len(data) % 32)


def tensor_tuple_head(dtype, dims, data_size):
    """The part of a Tensor's ABI tuple, (uint8 dtype, uint16[] dims, bytes
    data), before the data itself"""
    dims_offset = 3 * 32
    data_offset = dims_offset + 32 * (1 + len(dims))
    return (word(dtype) + word(dims_offset) + word(data_offset)
            + word(len(dims)) + b"".join(word(d) for d in dims)
            + word(data_size))


def encode_tensor_tuple(dtype, dims, data):
    return tensor_tuple_head(dtype, dims, len(data)) + pad32(data)


def tensor_array_offsets(tuples):
    """The offsets that start a Tensor[]'s elements, given their encodings.
    Tensor is dynamic, so each element's offset from the end of the array's
    length word comes before the elements themselves."""
    offsets, offset = b"", 32 * len(tuples)
    for t in tuples:
        offsets += word(offset)
        offset += len(t)
    return offsets

def hex_int(n):
    """Hex with an even number of digits, as the filler writes integers"""
    digits = f"{n:x}"
    return "0x" + "0" * (len(digits) % 2) + digits


def hex_bytes(data):
    return "0x" + data.hex()


HEADER_FIELDS = [
    ("parentHash", hex_bytes), ("uncleHash", hex_bytes),
    ("coinbase", hex_bytes), ("stateRoot", hex_bytes),
    ("transactionsTrie", hex_bytes), ("receiptTrie", hex_bytes),
    ("bloom", hex_bytes), ("difficulty", hex_int), ("number", hex_int),
    ("gasLimit", hex_int), ("gasUsed", hex_int), ("timestamp", hex_int),
    ("extraData", hex_bytes), ("mixHash", hex_bytes), ("nonce", hex_bytes),
    ("baseFeePerGas", hex_int), ("withdrawalsRoot", hex_bytes),
    ("blobGasUsed", hex_int), ("excessBlobGas", hex_int),
    ("parentBeaconBlockRoot", hex_bytes), ("requestsHash", hex_bytes),
]


def header(**fields):
    defaults = dict(
        parentHash=bytes(32), uncleHash=EMPTY_LIST_HASH, coinbase=bytes(20),
        stateRoot=bytes(32), transactionsTrie=EMPTY_TRIE_ROOT,
        receiptTrie=EMPTY_TRIE_ROOT, bloom=bytes(256), difficulty=0,
        number=0, gasLimit=BLOCK_GAS_LIMIT, gasUsed=0, timestamp=0,
        extraData=b"", mixHash=bytes(32), nonce=bytes(8),
        baseFeePerGas=BASE_FEE, withdrawalsRoot=EMPTY_TRIE_ROOT,
        blobGasUsed=0, excessBlobGas=0, parentBeaconBlockRoot=bytes(32),
        requestsHash=EMPTY_REQUESTS_HASH)
    defaults.update(fields)
    return defaults


def header_rlp(h):
    return rlp([h[name] for name, _ in HEADER_FIELDS])


def header_json(h):
    j = {name: fmt(h[name]) for name, fmt in HEADER_FIELDS}
    j["hash"] = hex_bytes(keccak256(header_rlp(h)))
    return j


def storage_json(storage):
    return {hex_int(k): hex_int(v) for k, v in storage.items() if v != 0}


def account_json(balance, nonce, code=b"", storage=None):
    return {"nonce": hex_int(nonce), "balance": hex_int(balance),
            "code": hex_bytes(code), "storage": storage_json(storage or {})}


def logs_bloom(logs):
    """The bloom filter of `logs`, (address, topics, data): for each address
    and topic, the three bits of 2048 its hash's first three pairs of bytes
    give, modulo 2048, counted from the least significant"""
    bloom = bytearray(256)
    for address, topics, _ in logs:
        for value in [address, *topics]:
            digest = keccak256(value)
            for i in (0, 2, 4):
                bit = int.from_bytes(digest[i:i + 2], "big") % 2048
                bloom[255 - bit // 8] |= 1 << (bit % 8)
    return bytes(bloom)


def blockchain_test(name, description, contracts, calls, genesis_storage=None,
                    network=NETWORK, genesis_state_root=None,
                    post_state_root=None):
    """A single-block test in which the sender makes `calls`, a list of
    (to, calldata, gas limit), in order, each with the logs it emits after
    them if it emits any, (address, topics, data). `contracts` maps each
    contract's address to its code and its expected storage afterwards, and
    `genesis_storage` the address of each contract with storage beforehand to
    that storage. The state roots, before and after the block, are the plain
    trie's unless given, which is right only before MONAD_TEN: from there on,
    MIP-8 encodes storage in pages."""
    with open(SYSTEM_CONTRACTS_FIXTURE) as f:
        system_pre = next(iter(json.load(f).values()))["pre"]
    system_contracts = {a: system_pre[a] for a in SYSTEM_CONTRACT_ADDRESSES}
    sender = address_of(SENDER_KEY)

    tx_rlps, receipt_rlps, transactions, receipts = [], [], [], []
    gas_used = 0
    block_bloom = bytes(256)
    for nonce, (to, calldata, gas_limit, *emitted) in enumerate(calls):
        logs = emitted[0] if emitted else []
        # Legacy EIP-155 transaction
        unsigned = [nonce, GAS_PRICE, gas_limit, to, 0, calldata]
        r, s, recovery_id = sign(
            SENDER_KEY, keccak256(rlp(unsigned + [CHAIN_ID, 0, 0])))
        v = recovery_id + 35 + 2 * CHAIN_ID
        tx_rlp = rlp(unsigned + [v, r, s])
        # Monad charges the full gas limit
        gas_used += gas_limit
        bloom = logs_bloom(logs)
        block_bloom = bytes(a | b for a, b in zip(block_bloom, bloom))
        receipt_rlp = rlp([1, gas_used, bloom, [
            [address, list(topics), data] for address, topics, data in logs]])

        tx_rlps.append(tx_rlp)
        receipt_rlps.append(receipt_rlp)
        transactions.append({
            "type": "0x00", "chainId": hex_int(CHAIN_ID),
            "nonce": hex_int(nonce), "gasPrice": hex_int(GAS_PRICE),
            "gasLimit": hex_int(gas_limit), "to": hex_bytes(to),
            "value": "0x00", "data": hex_bytes(calldata), "v": hex_int(v),
            "r": hex_int(r), "s": hex_int(s), "sender": hex_bytes(sender),
        })
        receipts.append({
            "transactionHash": hex_bytes(keccak256(tx_rlp)), "type": "0x00",
            "cumulativeGasUsed": hex_int(gas_used),
            "bloom": hex_bytes(bloom), "logs": [
                {"address": hex_bytes(address),
                 "topics": [hex_bytes(topic) for topic in topics],
                 "data": hex_bytes(data)}
                for address, topics, data in logs],
            "status": True, "rlp": hex_bytes(receipt_rlp),
        })

    pre = dict(system_contracts)
    pre[hex_bytes(sender)] = account_json(SENDER_BALANCE, 0)
    for address, (code, _) in contracts.items():
        pre[hex_bytes(address)] = account_json(
            0, 1, code, (genesis_storage or {}).get(address))

    genesis = header(extraData=b"\x00",
                     stateRoot=genesis_state_root or state_root(pre))
    genesis_hash = keccak256(header_rlp(genesis))

    # EIP-2935 and EIP-4788 system calls at the start of block 1
    post = json.loads(json.dumps(system_contracts))
    post[HISTORY_STORAGE_ADDRESS]["storage"] = storage_json(
        {0 % HISTORY_SERVE_WINDOW: int.from_bytes(genesis_hash, "big")})
    post[BEACON_ROOTS_ADDRESS]["storage"] = storage_json(
        {TIMESTAMP % BEACON_ROOTS_HISTORY_BUFFER_LENGTH: TIMESTAMP})
    post[hex_bytes(sender)] = account_json(
        SENDER_BALANCE - gas_used * GAS_PRICE, len(calls))
    for address, (code, storage) in contracts.items():
        post[hex_bytes(address)] = account_json(0, 1, code, storage)
    post[hex_bytes(COINBASE)] = account_json(
        gas_used * (GAS_PRICE - BASE_FEE), 0)

    block = header(
        parentHash=genesis_hash, coinbase=COINBASE,
        stateRoot=post_state_root or state_root(post),
        transactionsTrie=list_trie_root(tx_rlps),
        receiptTrie=list_trie_root(receipt_rlps), bloom=block_bloom,
        number=1, gasUsed=gas_used, timestamp=TIMESTAMP)
    block_hash = keccak256(header_rlp(block))

    return {f"{name}[fork_{network}-blockchain_test]": {
        "network": network,
        "genesisBlockHeader": header_json(genesis),
        "pre": pre,
        "postState": post,
        "lastblockhash": hex_bytes(block_hash),
        "config": {"network": network, "chainid": hex_int(CHAIN_ID)},
        "genesisRLP": hex_bytes(rlp([Rlp(header_rlp(genesis)), [], [], []])),
        "blocks": [{
            "blockHeader": header_json(block),
            "transactions": transactions,
            "uncleHeaders": [],
            "withdrawals": [],
            "receipts": receipts,
            "blocknumber": "1",
            "rlp": hex_bytes(rlp([Rlp(header_rlp(block)),
                                  [Rlp(tx) for tx in tx_rlps], [], []])),
        }],
        "sealEngine": "NoProof",
        "_info": {
            "fixture-format": "blockchain_test",
            "comment": "Hand-built by graph_fixture.py",
            "description": description,
        },
    }}


#
# Graphs
#

GRAPH_EVAL_DIR = REPO_ROOT / "category/execution/monad/graph_eval"
GRAPH_ADDRESS = bytes.fromhex("0000000000000000000000000000000000006a40")
# The caller contract for call n is at CALLER_BASE_ADDRESS + n. For a static
# delegatecall, it makes a static call to a contract at INNER_BASE_ADDRESS + n,
# which makes the DELEGATECALL
CALLER_BASE_ADDRESS = 0xC0FFEE00
INNER_BASE_ADDRESS = 0x1A1E0000
MAX_RANK = 8
MAX_DIMENSION = 0xFFFF
MAX_NODES = 0xFFFF

#
# Definitions read from the C++ sources
#


def _find(pattern, file_name):
    source = (GRAPH_EVAL_DIR / file_name).read_text()
    match = re.search(pattern, source, re.S)
    if not match:
        raise RuntimeError(
            f"no match for {pattern!r} in {file_name}; graph_fixture.py needs "
            "updating")
    return match


def _enum(name, file_name):
    """Enumerator -> value for `enum class name`, aliases included"""
    body = _find(r"enum class " + name + r"\b[^{]*\{(.*?)\}", file_name)[1]
    body = re.sub(r"//[^\n]*", "", body)
    values, next_value = {}, 0
    for entry in filter(None, (e.strip() for e in body.split(","))):
        key, _, value = (s.strip() for s in entry.partition("="))
        if value:
            next_value = values[value] if value in values else int(value, 0)
        values[key] = next_value
        next_value += 1
    return values


OP_IDS = _enum("Op", "graph.hpp")
ERROR_MESSAGES = dict(re.findall(
    r'\{GraphEvalError::(\w+),\s*"([^"]*)"',
    (GRAPH_EVAL_DIR / "graph_eval_error.cpp").read_text()))
EVAL_GRAPH_SIGNATURE = _find(
    r'EVAL_GRAPH\s*=\s*abi_encode_selector\(\s*"([^"]+)"',
    "graph_eval.cpp")[1].encode()
# Split over adjacent string literals
EVAL_GRAPH_INTO_SIGNATURE = "".join(re.findall(r'"([^"]*)"', _find(
    r'EVAL_GRAPH_INTO\s*=\s*abi_encode_selector\(\s*((?:"[^"]*"\s*)+)\)',
    "graph_eval.cpp")[1])).encode()
BYTE_ORDERS = _enum("ByteOrder", "tensor.hpp")
LOCATIONS = _enum("Location", "tensor.hpp")
BIG_ENDIAN = BYTE_ORDERS["BigEndian"]
LITTLE_ENDIAN = BYTE_ORDERS["LittleEndian"]
LITERAL, CODE, STORAGE = (LOCATIONS[n] for n in ("Literal", "Code", "Storage"))
MAGIC = int(_find(r"GRAPH_MAGIC = (0x[0-9a-fA-F]+)", "constants.hpp")[1], 16)
MAX_GRAPH_INPUTS = int(_find(r"MAX_GRAPH_INPUTS = (\d+)", "constants.hpp")[1])
MAX_GRAPH_OUTPUTS = int(
    _find(r"MAX_GRAPH_OUTPUTS = (\d+)", "constants.hpp")[1])
MAX_FRACTIONAL_BITS = int(
    _find(r"MAX_FRACTIONAL_BITS = (\d+)", "constants.hpp")[1])
LN2_Q64 = int(_find(r"LN2_Q64 = (0x[0-9a-fA-F]+)", "fixed_point.hpp")[1], 16)
EXP_TERMS = int(_find(r"EXP_TERMS = (\d+)", "fixed_point.hpp")[1])
EXP_LIMIT = int(_find(r"EXP_LIMIT = (\d+)", "fixed_point.hpp")[1])


class Dtype(namedtuple("Dtype", "name id size signed")):
    @property
    def min(self):
        return -(1 << (8 * self.size - 1)) if self.signed else 0

    @property
    def max(self):
        return (1 << (8 * self.size - self.signed)) - 1

    def wrap(self, value):
        """Two's complement wrapping, as Add and Sub do"""
        return (value - self.min) % (1 << (8 * self.size)) + self.min

    def clamp(self, value):
        return min(max(value, self.min), self.max)

    def encode(self, values, byteorder):
        return b"".join(v.to_bytes(self.size, byteorder, signed=self.signed)
                        for v in values)


DTYPES = {}
for _name, _id in _enum("Dtype", "types.hpp").items():
    if _match := re.fullmatch(r"(u?)int(8|16|32|64)", _name):
        DTYPES[_name] = Dtype(_name, _id, int(_match[2]) // 8, not _match[1])
UINT8 = DTYPES["uint8"]

#
# Reference evaluator
#

# Row-major values as Python ints, and dims as a tuple
Tensor = namedtuple("Tensor", "dtype dims values")


class GraphError(Exception):
    """An error the precompile reverts with, named as in GraphEvalError"""


class RunError(Exception):
    """An error an op only finds from its operands' values, named as in
    GraphEvalError. The interpreter checks the whole graph before running it,
    so any error the checks find comes first. `placeholder` is a result of the
    right type, for checking the ops that follow"""

    def __init__(self, name, placeholder):
        super().__init__(name)
        self.placeholder = placeholder


def _zeros(dtype, dims):
    return Tensor(dtype, dims, [0] * math.prod(dims))


def _broadcast_dims(*shapes):
    """The shape numpy broadcasts `shapes` to"""
    rank = max(map(len, shapes))
    dims = []
    for d in range(rank):
        size = 1
        for shape in shapes:
            i = d - (rank - len(shape))
            dim = shape[i] if i >= 0 else 1
            if dim != 1:
                if size not in (1, dim):
                    raise GraphError("ShapeError")
                size = dim
        dims.append(size)
    return tuple(dims)


def _broadcast_values(a, dims):
    """a's values, repeated to fill `dims`, which a's shape broadcasts to"""
    lead = len(dims) - len(a.dims)
    values = []
    for index in itertools.product(*map(range, dims)):
        offset = 0
        for d, i in zip(a.dims, index[lead:]):
            offset = offset * d + (0 if d == 1 else i)
        values.append(a.values[offset])
    return values


def _arithmetic(f):
    def evaluate(a, b):
        if a.dtype != b.dtype:
            raise GraphError("TypeError")
        dims = _broadcast_dims(a.dims, b.dims)
        return Tensor(a.dtype, dims, [a.dtype.wrap(f(x, y)) for x, y in zip(
            _broadcast_values(a, dims), _broadcast_values(b, dims))])
    return evaluate


def _comparison(f):
    def evaluate(a, b):
        if a.dtype != b.dtype:
            raise GraphError("TypeError")
        dims = _broadcast_dims(a.dims, b.dims)
        return Tensor(UINT8, dims, [int(f(x, y)) for x, y in zip(
            _broadcast_values(a, dims), _broadcast_values(b, dims))])
    return evaluate


def _where(condition, a, b):
    if condition.dtype != UINT8 or a.dtype != b.dtype:
        raise GraphError("TypeError")
    dims = _broadcast_dims(condition.dims, a.dims, b.dims)
    return Tensor(a.dtype, dims, [x if c else y for c, x, y in zip(
        _broadcast_values(condition, dims), _broadcast_values(a, dims),
        _broadcast_values(b, dims))])


def _reshape(dims, a):
    if math.prod(dims) != math.prod(a.dims):
        raise GraphError("ShapeError")
    return Tensor(a.dtype, dims, a.values)


def _saturate(dtype, a):
    return Tensor(dtype, a.dims, [dtype.clamp(v) for v in a.values])


def _widened(dtype):
    """The dtype twice as wide, with the same signedness; 64-bit ones stay"""
    if dtype.size == 8:
        return dtype
    return DTYPES[f"{'' if dtype.signed else 'u'}int{16 * dtype.size}"]


def _widening_mul(a, b):
    if a.dtype != b.dtype:
        raise GraphError("TypeError")
    dims = _broadcast_dims(a.dims, b.dims)
    out = _widened(a.dtype)
    return Tensor(out, dims, [out.wrap(x * y) for x, y in zip(
        _broadcast_values(a, dims), _broadcast_values(b, dims))])


def _div(denominator, a):
    if denominator == 0:
        raise GraphError("GraphValidationError")

    def divide(x):
        quotient = abs(x) // abs(denominator)
        return a.dtype.wrap(
            -quotient if (x < 0) != (denominator < 0) else quotient)
    return Tensor(a.dtype, a.dims, [divide(x) for x in a.values])


def _matmul(a, b):
    if a.dtype != DTYPES["int8"] or b.dtype != DTYPES["int8"]:
        raise GraphError("TypeError")
    if len(a.dims) != 2 or len(b.dims) != 2:
        raise GraphError("RankError")
    (m, k), (k_b, n) = a.dims, b.dims
    if k_b != k:
        raise GraphError("ShapeError")
    return Tensor(DTYPES["int32"], (m, n), [
        sum(a.values[i * k + p] * b.values[p * n + j] for p in range(k))
        for i in range(m) for j in range(n)])


def _argmax(a):
    if not a.values:
        raise GraphError("ShapeError")
    largest = max(range(len(a.values)), key=lambda i: (a.values[i], -i))
    return Tensor(a.dtype, (), [a.dtype.wrap(largest)])


def _expand(dims, a):
    if len(a.dims) > len(dims):
        raise GraphError("RankError")
    if _broadcast_dims(dims, a.dims) != dims:
        raise GraphError("ShapeError")
    return Tensor(a.dtype, dims, _broadcast_values(a, dims))


def _cumsum(axis, a):
    if axis >= len(a.dims):
        raise GraphError("RankError")
    inner = math.prod(a.dims[axis + 1:])
    values = list(a.values)
    for i in range(len(values)):
        # Not the first along the axis
        if i // inner % a.dims[axis]:
            values[i] = a.dtype.wrap(values[i - inner] + values[i])
    return Tensor(a.dtype, a.dims, values)


def _reduce(f, empty_is_zero):
    """An op combining a's elements along an axis with f, keeping the axis"""
    def evaluate(axis, a):
        if axis >= len(a.dims):
            raise GraphError("RankError")
        if not empty_is_zero and a.dims[axis] == 0:
            raise GraphError("ShapeError")
        outer = math.prod(a.dims[:axis])
        length = a.dims[axis]
        inner = math.prod(a.dims[axis + 1:])
        values = [a.dtype.wrap(f(a.values[(block * length + row) * inner + i]
                                 for row in range(length)))
                  for block in range(outer) for i in range(inner)]
        dims = a.dims[:axis] + (1,) + a.dims[axis + 1:]
        return Tensor(a.dtype, dims, values)
    return evaluate


def _check_bits(bits):
    if bits > MAX_FRACTIONAL_BITS:
        raise GraphError("GraphValidationError")


def _q_div(x, y, bits):
    quotient = abs(x << bits) // abs(y)
    return -quotient if (x < 0) != (y < 0) else quotient


def _fixed_point(f, check=lambda b: None):
    """An op applying f(x, y, bits) to operands of the same dtype, broadcast
    together, wrapping to that dtype. check(b) raises the error the operands'
    values give, if any"""
    def evaluate(bits, a, b):
        _check_bits(bits)
        if a.dtype != b.dtype:
            raise GraphError("TypeError")
        dims = _broadcast_dims(a.dims, b.dims)
        if error := check(b):
            raise RunError(error, _zeros(a.dtype, dims))
        return Tensor(a.dtype, dims, [
            a.dtype.wrap(f(x, y, bits)) for x, y in zip(
                _broadcast_values(a, dims), _broadcast_values(b, dims))])
    return evaluate


def _qmatmul(bits, dtype, a, b):
    _check_bits(bits)
    if a.dtype != b.dtype:
        raise GraphError("TypeError")
    if len(a.dims) != 2 or len(b.dims) != 2:
        raise GraphError("RankError")
    (m, k), (k_b, n) = a.dims, b.dims
    if k_b != k:
        raise GraphError("ShapeError")

    def element(i, j):
        total = sum(a.values[i * k + p] * b.values[p * n + j]
                    for p in range(k)) % (1 << 128)
        if a.dtype.signed and total >> 127:
            total -= 1 << 128
        return dtype.wrap(total >> bits)
    return Tensor(dtype, (m, n), [element(i, j)
                                  for i in range(m) for j in range(n)])


# q_exp's coefficients: 1 / n! with 63 fractional bits, rounded down
_EXP_COEFFICIENTS = [(1 << 63) // math.factorial(n) for n in range(EXP_TERMS)]


def _exp(x, bits, dtype):
    """e^(x / 2^bits) * 2^bits as fixed_point.hpp's q_exp computes it"""
    if x >= EXP_LIMIT << bits:
        return dtype.max
    if x <= -(EXP_LIMIT << bits):
        return 0
    k, r = divmod(x << (64 - bits), LN2_Q64)
    r63 = r >> 1
    p = _EXP_COEFFICIENTS[-1]
    for coefficient in reversed(_EXP_COEFFICIENTS[:-1]):
        p = coefficient + (p * r63 >> 63)
    shift = k + bits - 63
    return dtype.max if shift > 0 else min(p >> -shift, dtype.max)


def _qexp(bits, a):
    _check_bits(bits)
    return Tensor(a.dtype, a.dims, [_exp(x, bits, a.dtype) for x in a.values])


def _qinvsqrt(bits, a):
    _check_bits(bits)
    for x in a.values:
        if x <= 0:
            raise RunError("DivisionByZero" if x == 0 else "DomainError",
                           _zeros(a.dtype, a.dims))
    # floor(2^bits / sqrt(x / 2^bits)), exactly
    return Tensor(a.dtype, a.dims, [
        min(math.isqrt((1 << 3 * bits) // x), a.dtype.max) for x in a.values])


def _gather(axis, data, indices):
    if axis >= len(data.dims):
        raise GraphError("RankError")
    dims = data.dims[:axis] + indices.dims + data.dims[axis + 1:]
    if len(dims) > MAX_RANK:
        raise GraphError("RankError")
    length = data.dims[axis]
    if not all(0 <= i < length for i in indices.values):
        raise RunError("IndexError", _zeros(data.dtype, dims))
    outer = math.prod(data.dims[:axis])
    inner = math.prod(data.dims[axis + 1:])
    return Tensor(data.dtype, dims, [
        data.values[(block * length + i) * inner + j]
        for block in range(outer) for i in indices.values
        for j in range(inner)])


def _concat(axis, a, b):
    if a.dtype != b.dtype:
        raise GraphError("TypeError")
    if len(a.dims) != len(b.dims) or axis >= len(a.dims):
        raise GraphError("RankError")
    if any(x != y for d, (x, y) in enumerate(zip(a.dims, b.dims))
           if d != axis):
        raise GraphError("ShapeError")
    length = a.dims[axis] + b.dims[axis]
    if length > MAX_DIMENSION:
        raise GraphError("ShapeError")
    outer = math.prod(a.dims[:axis])
    a_block = a.dims[axis] * math.prod(a.dims[axis + 1:])
    b_block = b.dims[axis] * math.prod(b.dims[axis + 1:])
    values = []
    for block in range(outer):
        values += a.values[block * a_block:(block + 1) * a_block]
        values += b.values[block * b_block:(block + 1) * b_block]
    return Tensor(a.dtype, a.dims[:axis] + (length,) + a.dims[axis + 1:],
                  values)


def _decode_tensor(data, byteorder="little"):
    """The tensor at the start of `data`, encoded as a literal is, with its
    elements in `byteorder`, ignoring whatever follows it, or None if there
    isn't a whole one"""
    dtypes = {dtype.id: dtype for dtype in DTYPES.values()}
    if len(data) < 2 or data[0] not in dtypes or data[1] > MAX_RANK:
        return None
    dtype, rank = dtypes[data[0]], data[1]
    if len(data) < 2 + 2 * rank:
        return None
    dims = struct.unpack_from(f"<{rank}H", data, 2)
    size = math.prod(dims) * dtype.size
    values = data[2 + 2 * rank:2 + 2 * rank + size]
    if len(values) != size:
        return None
    return Tensor(dtype, dims, _decode_values(dtype, values, byteorder))


def _decode_values(dtype, data, byteorder):
    return [int.from_bytes(data[i:i + dtype.size], byteorder,
                           signed=dtype.signed)
            for i in range(0, len(data), dtype.size)]


def _code_tensor(accounts, dtype, dims, address, offset, byteorder):
    """The tensor at `offset` in the code of the account at `address`,
    counted from the code's start, encoded as a literal is, with its elements
    in `byteorder`, as references to code read it. The code must start with a
    0x00 byte, so the offset is at least 1, and the tensor must have the type
    dtype[dims]"""
    code = accounts.get(address, b"")
    tensor = (_decode_tensor(code[offset:], byteorder)
              if offset >= 1 and code[:1] == b"\0" else None)
    if tensor is None or tensor.dtype != dtype or tensor.dims != dims:
        raise RunError("InvalidTensorRef", _zeros(dtype, dims))
    return tensor


def _tensorref(accounts, declared, address, offset):
    """TensorRef, which the interpreter handles ad hoc, as it reads the state:
    the tensor in an account's code, with little-endian elements"""
    return _code_tensor(accounts, *declared, address, offset, "little")


# DSL name -> (Op enumerator, argument kinds, reference evaluator). Parameters,
# the arguments that aren't nodes, are encoded before the input node ids, as
# the interpreter reads them, and the evaluator takes them in that order too.
# tensorref's evaluator is _tensorref, which `evaluate` calls with the accounts
OPS = {
    "literal": ("Literal", ["tensor"], lambda tensor: tensor),
    "tensorref": ("TensorRef", ["type", "address", "offset"], None),
    "add": ("Add", ["node", "node"], _arithmetic(operator.add)),
    "sub": ("Sub", ["node", "node"], _arithmetic(operator.sub)),
    "mul": ("Mul", ["node", "node"], _widening_mul),
    "max": ("Max", ["node", "node"], _arithmetic(max)),
    "min": ("Min", ["node", "node"], _arithmetic(min)),
    "greater": ("Greater", ["node", "node"], _comparison(operator.gt)),
    "ge": ("Ge", ["node", "node"], _comparison(operator.ge)),
    "equal": ("Equal", ["node", "node"], _comparison(operator.eq)),
    "where": ("Where", ["node", "node", "node"], _where),
    "reshape": ("Reshape", ["node", "shape"], _reshape),
    "saturate": ("Saturate", ["node", "dtype"], _saturate),
    "expand": ("Expand", ["node", "shape"], _expand),
    "cumsum": ("CumSum", ["node", "axis"], _cumsum),
    "div": ("Div", ["node", "int64"], _div),
    "matmul": ("MatMul", ["node", "node"], _matmul),
    "argmax": ("ArgMax", ["node"], _argmax),
    "reducesum": ("ReduceSum", ["node", "axis"], _reduce(sum, True)),
    "reducemax": ("ReduceMax", ["node", "axis"], _reduce(max, False)),
    "qmul": ("QMul", ["node", "node", "bits"],
             _fixed_point(lambda x, y, bits: x * y >> bits)),
    "qdiv": ("QDiv", ["node", "node", "bits"], _fixed_point(
        _q_div, lambda b: "DivisionByZero" if 0 in b.values else None)),
    "qmatmul": ("QMatMul", ["node", "node", "bits", "dtype"], _qmatmul),
    "qexp": ("QExp", ["node", "bits"], _qexp),
    "qinvsqrt": ("QInvSqrt", ["node", "bits"], _qinvsqrt),
    "gather": ("Gather", ["node", "node", "axis"], _gather),
    "concat": ("Concat", ["node", "node", "axis"], _concat),
}


def evaluate(graph, args, ref_error=None, output_count=None):
    """The graph's outputs for `args`, given in input order, checked as the
    interpreter checks them; raises GraphError if the precompile reverts.
    `ref_error` is the error the first input reference whose data didn't match
    its type gave, which comes after the static errors, as the interpreter
    reads the inputs after checking the graph, and `output_count` is
    evalGraphInto's number of outputs, which must be the graph's"""
    for (_, dtype, dims), arg in zip(graph.inputs, args):
        if arg.dtype != dtype:
            raise GraphError("TypeError")
        if len(arg.dims) != len(dims):
            raise GraphError("RankError")
        if arg.dims != dims:
            raise GraphError("ShapeError")
    values = list(args)
    run_error = None
    for node in graph.nodes:
        try:
            if node.op == "tensorref":
                value = _tensorref(graph.accounts, *node.params)
            else:
                value = OPS[node.op][2](
                    *node.params, *(values[i] for i in node.inputs))
        except RunError as e:
            run_error = run_error or e.args[0]
            value = e.placeholder
        values.append(value)
    if output_count is not None and output_count != len(graph.outputs):
        raise GraphError("ArityError")
    if ref_error or run_error:
        raise GraphError(ref_error or run_error)
    return [values[i] for i in graph.outputs]

#
# Parser
#


class DslError(Exception):
    def __init__(self, line, message):
        super().__init__(f"line {line}: {message}")


# An op's result. `params` are its non-node arguments and `inputs` the node ids
# of the rest, each in argument order
Node = namedtuple("Node", "op params inputs")

# A call's TensorInput as the calldata has it: a header, dtype[dims], then a
# byte order, a location and a payload, which the reference evaluator decodes
# as the precompile does. `tensor` is a literal's value, and None for the rest
TensorInput = namedtuple("TensorInput",
                         "dtype dims order location payload tensor")
# One of evalGraphInto's TensorOutputs
TensorOutput = namedtuple("TensorOutput", "order location payload")


class Call:
    def __init__(self, label, mode):
        self.label = label
        # "call", "staticcall", "delegatecall" or "static delegatecall"
        self.mode = mode
        self.inputs = {}  # input name -> TensorInput
        self.storage = []  # (slot, bytes): what the slots from slot hold
        self.outputs = None  # TensorOutputs, for evalGraphInto

    def genesis_storage(self):
        """The caller's storage before the call, slot -> word"""
        storage = {}
        for slot, data in self.storage:
            store_slots(storage, slot, data)
        return storage


class Graph:
    def __init__(self):
        self.inputs = []  # (name, dtype, dims)
        self.nodes = []
        self.outputs = None  # node ids
        self.ids = {}  # name -> node id, the graph inputs' first
        self.calls = []  # Calls
        self.accounts = {}  # address -> code, from the data statements


def _statements(text):
    """(line number, statement) pairs, without comments, joining a statement
    that has unclosed brackets with the lines that follow"""
    pending, start = "", 0
    for number, line in enumerate(text.splitlines(), 1):
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        if not pending:
            start = number
        pending = f"{pending} {line}".strip()
        depth = (sum(map(pending.count, "([")) -
                 sum(map(pending.count, ")]")))
        if depth < 0:
            raise DslError(number, "unbalanced brackets")
        if depth == 0 and not pending.endswith(","):
            yield start, pending
            pending = ""
    if pending:
        raise DslError(start, "unclosed bracket")


def _description(text):
    """The comment lines at the top of `text`"""
    lines = []
    for line in text.splitlines():
        if not line.lstrip().startswith("#"):
            break
        lines.append(line.lstrip()[1:].strip())
    return " ".join(filter(None, lines))


def _split_args(text):
    """Splits on the commas that aren't inside brackets"""
    args, depth, start = [], 0, 0
    for i, c in enumerate(text):
        depth += (c in "([") - (c in ")]")
        if c == "," and depth == 0:
            args.append(text[start:i].strip())
            start = i + 1
    args.append(text[start:].strip())
    return [] if args == [""] else args


def _check_dims(dims, line):
    if len(dims) > MAX_RANK:
        raise DslError(line, f"rank {len(dims)} is more than {MAX_RANK}")
    if not all(0 <= d <= MAX_DIMENSION for d in dims):
        raise DslError(line, f"dimensions must be in [0, {MAX_DIMENSION}]")
    return tuple(dims)


def _parse_dims(text, line):
    try:
        dims = ast.literal_eval(text)
    except (ValueError, SyntaxError):
        dims = None
    if not isinstance(dims, list) or not all(type(d) is int for d in dims):
        raise DslError(line, f"expected a shape like [2, 3], not {text!r}")
    return _check_dims(dims, line)


_TYPE = re.compile(r"(\w+)\s*\[([^\]]*)\]")


def _parse_type(text, line):
    match = _TYPE.fullmatch(text.strip())
    if not match or match[1] not in DTYPES:
        raise DslError(line, f"expected a type like int8[2, 3], not {text!r}")
    return DTYPES[match[1]], _parse_dims(f"[{match[2]}]", line)


def _flatten(value, dims, line):
    if not dims:
        if type(value) is not int:
            raise DslError(line, f"expected an integer, not {value!r}")
        return [value]
    if not isinstance(value, list) or len(value) != dims[0]:
        raise DslError(line, f"{value!r} doesn't have shape {list(dims)}")
    return [v for item in value for v in _flatten(item, dims[1:], line)]


def _parse_value(text, line, dtype=None):
    """A tensor from a nested list of integers, or a single integer for a
    scalar, preceded by its type. Without the type, the dtype is `dtype` and
    the shape is the nesting's."""
    match = _TYPE.match(text)
    if match and match[1] in DTYPES:
        dtype, dims = _parse_type(match[0], line)
        text = text[match.end():]
    elif dtype is None:
        raise DslError(line, "expected a type before the value, as in "
                       "int8[2] [1, 2]")
    else:
        dims = None
    try:
        value = ast.literal_eval(text.strip())
    except (ValueError, SyntaxError):
        raise DslError(line, f"invalid value {text.strip()!r}") from None
    if dims is None:
        dims, nested = [], value
        while isinstance(nested, list):
            dims.append(len(nested))
            nested = nested[0] if nested else None
        dims = _check_dims(dims, line)
    values = _flatten(value, dims, line)
    if not all(dtype.min <= v <= dtype.max for v in values):
        raise DslError(line, f"values must be in [{dtype.min}, {dtype.max}] "
                       f"for {dtype.name}")
    return Tensor(dtype, dims, values)


def _parse_address(text, line):
    if not re.fullmatch(r"0x[0-9a-fA-F]{1,40}", text):
        raise DslError(line, f"expected an address like 0xda7a, not {text!r}")
    return int(text, 16).to_bytes(20, "big")


def _parse_int(text, line, limit, what):
    if not re.fullmatch(r"\d+|0x[0-9a-fA-F]+", text) or int(text, 0) >= limit:
        raise DslError(line, f"expected {what}, not {text!r}")
    return int(text, 0)


def _parse_slot(text, line):
    return _parse_int(text, line, 1 << 256, "a storage slot")


def _parse_hex(text, line):
    if not re.fullmatch(r"0x([0-9a-fA-F]{2})*", text):
        raise DslError(line, f"expected bytes like 0x00ff, not {text!r}")
    return bytes.fromhex(text[2:])


def _parse_byte_order(text):
    """The byte order a leading `little` or `big` gives, by default
    big-endian, and the rest of `text`"""
    match = re.match(r"(little|big)\s+", text)
    if not match:
        return BIG_ENDIAN, text
    order = LITTLE_ENDIAN if match[1] == "little" else BIG_ENDIAN
    return order, text[match.end():]


def _byteorder(order):
    """A byte order tag as Python names it"""
    return "little" if order == LITTLE_ENDIAN else "big"


def _parse_reference(text, line, order, explicit_order):
    """(byte order, location, payload) for storage(slot), code(address,
    offset) or raw(byte order, location, 0x<payload>), or None if `text` is
    none of them"""
    match = re.fullmatch(r"(code|storage|raw)\s*\((.*)\)", text)
    if not match:
        return None
    args = _split_args(match[2])
    if match[1] == "storage":
        if len(args) != 1:
            raise DslError(line, "storage takes a slot")
        return order, STORAGE, word(_parse_slot(args[0], line))
    if match[1] == "code":
        if len(args) != 2:
            raise DslError(line, "code takes an address and an offset")
        address = _parse_address(args[0], line)
        offset = _parse_int(args[1], line, 1 << 32, "an offset in [0, 2^32)")
        return (order, CODE,
                word(int.from_bytes(address, "big")) + word(offset))
    if len(args) != 3:
        raise DslError(line, "raw takes a byte order, a location and a payload")
    if explicit_order:
        raise DslError(line, "raw gives its own byte order")
    return (_parse_int(args[0], line, 256, "a byte order in [0, 255]"),
            _parse_int(args[1], line, 256, "a location in [0, 255]"),
            _parse_hex(args[2], line))


def _parse_input(text, line, dtype, dims):
    """A call's TensorInput for an input of type dtype[dims], which is its
    header unless `text` gives one"""
    order, rest = _parse_byte_order(text.strip())
    explicit_order = rest != text.strip()
    match = _TYPE.match(rest)
    if match and match[1] in DTYPES:
        header = _parse_type(match[0], line)
        reference = rest[match.end():].strip()
    else:
        header, reference = (dtype, dims), rest
    parsed = _parse_reference(reference, line, order, explicit_order)
    if parsed is not None:
        return TensorInput(*header, *parsed, None)
    tensor = _parse_value(rest, line, dtype)
    payload = tensor.dtype.encode(tensor.values, _byteorder(order))
    return TensorInput(tensor.dtype, tensor.dims, order, LITERAL, payload,
                       tensor)


def _parse_output(text, line):
    """One of evalGraphInto's TensorOutputs: storage(slot), literal, for a
    returned one, or raw(...)"""
    order, rest = _parse_byte_order(text.strip())
    if rest == "literal":
        return TensorOutput(order, LITERAL, b"")
    parsed = _parse_reference(rest, line, order, rest != text.strip())
    if parsed is None or rest.startswith("code"):
        raise DslError(line, f"expected an output reference like storage(512), "
                       f"not {text!r}")
    return TensorOutput(*parsed)


def _parse_storage_value(text, line):
    """The bytes of a storage statement's value: a tensor's elements, after
    `little` for little-endian ones, or 0x<hex> bytes"""
    if re.fullmatch(r"0x[0-9a-fA-F]*", text.strip()):
        return _parse_hex(text.strip(), line)
    order, rest = _parse_byte_order(text.strip())
    tensor = _parse_value(rest, line)
    return tensor.dtype.encode(tensor.values, _byteorder(order))


def _define(graph, line, name):
    if name in graph.ids:
        raise DslError(line, f"{name} is already defined")
    graph.ids[name] = len(graph.ids)


def _node_id(graph, line, name):
    if name not in graph.ids:
        raise DslError(line, f"unknown node {name!r}")
    return graph.ids[name]


def _parse_op(graph, line, name, op, args_text):
    if op not in OPS:
        raise DslError(line, f"unknown op {op!r}")
    kinds = OPS[op][1]
    args = _split_args(args_text)
    if len(args) != len(kinds):
        raise DslError(line, f"{op} takes {len(kinds)} arguments")
    params, inputs = [], []
    for kind, arg in zip(kinds, args):
        if kind == "node":
            inputs.append(_node_id(graph, line, arg))
        elif kind == "shape":
            params.append(_parse_dims(arg, line))
        elif kind == "dtype":
            if arg not in DTYPES:
                raise DslError(line, f"unknown dtype {arg!r}")
            params.append(DTYPES[arg])
        elif kind == "axis":
            if not re.fullmatch(r"\d+", arg) or int(arg) > 0xFF:
                raise DslError(line, f"expected an axis in [0, 255], not "
                               f"{arg!r}")
            params.append(int(arg))
        elif kind == "bits":
            if not re.fullmatch(r"\d+", arg) or int(arg) > 0xFF:
                raise DslError(line, f"expected a number of fractional bits "
                               f"in [0, 255], not {arg!r}")
            params.append(int(arg))
        elif kind == "int64":
            if not re.fullmatch(r"-?\d+", arg) or not (
                    -(1 << 63) <= int(arg) < 1 << 63):
                raise DslError(line, f"expected an int64, not {arg!r}")
            params.append(int(arg))
        elif kind == "type":
            params.append(_parse_type(arg, line))
        elif kind == "address":
            params.append(_parse_address(arg, line))
        elif kind == "offset":
            if not re.fullmatch(r"\d+", arg) or int(arg) > 0xFFFFFFFF:
                raise DslError(line, f"expected an offset in [0, 2^32), not "
                               f"{arg!r}")
            params.append(int(arg))
        else:
            params.append(_parse_value(arg, line))
    _define(graph, line, name)
    graph.nodes.append(Node(op, params, inputs))


def parse(text):
    graph = Graph()
    call = None
    line = 0
    for line, statement in _statements(text):
        if match := re.fullmatch(r"(\w+)\s*=\s*(.+)", statement):
            name, rhs = match[1], match[2]
            if call is not None:
                input_types = {n: (dtype, dims)
                               for n, dtype, dims in graph.inputs}
                if name not in input_types:
                    raise DslError(line, f"{name} isn't a graph input")
                if name in call.inputs:
                    raise DslError(line, f"{name} is already given")
                call.inputs[name] = _parse_input(rhs, line, *input_types[name])
            elif op := re.fullmatch(r"(\w+)\s*\((.*)\)", rhs):
                if graph.outputs is not None:
                    raise DslError(line, "ops must come before the outputs")
                _parse_op(graph, line, name, op[1], op[2])
            else:
                raise DslError(line, f"expected an op call, not {rhs!r}")
        elif match := re.fullmatch(r"input\s+(\w+)\s*:\s*(.+)", statement):
            if graph.nodes or graph.outputs is not None or call is not None:
                raise DslError(line, "inputs must come before everything else")
            _define(graph, line, match[1])
            graph.inputs.append((match[1], *_parse_type(match[2], line)))
        elif match := re.fullmatch(r"output\s+(.+)", statement):
            if graph.outputs is not None or call is not None:
                raise DslError(line, "there must be one output statement, "
                               "before the calls")
            graph.outputs = [_node_id(graph, line, n.strip())
                             for n in match[1].split(",")]
        elif match := re.fullmatch(
                r"call\s+(\w+)(?:\s+(staticcall|delegatecall|static\s+"
                r"delegatecall))?", statement):
            if graph.outputs is None:
                raise DslError(line, "calls must come after the outputs")
            if any(c.label == match[1] for c in graph.calls):
                raise DslError(line, f"call {match[1]} is already defined")
            call = Call(match[1], " ".join((match[2] or "call").split()))
            graph.calls.append(call)
        elif match := re.fullmatch(r"storage\s+(\w+)\s*=\s*(.+)", statement):
            if call is None:
                raise DslError(line, "storage statements belong to calls")
            call.storage.append((_parse_slot(match[1], line),
                                 _parse_storage_value(match[2], line)))
        elif match := re.fullmatch(r"into\s+(.+)", statement):
            if call is None:
                raise DslError(line, "into statements belong to calls")
            if call.outputs is not None:
                raise DslError(line, f"call {call.label} already has outputs")
            call.outputs = [_parse_output(arg, line)
                            for arg in _split_args(match[1])]
        elif match := re.fullmatch(r"data\s+(\w+)\s*:\s*(.+)", statement):
            address = _parse_address(match[1], line)
            if address in graph.accounts:
                raise DslError(line, f"{match[1]} already has data")
            if re.fullmatch(r"0x([0-9a-fA-F]{2})*", match[2]):
                graph.accounts[address] = bytes.fromhex(match[2][2:])
            else:
                graph.accounts[address] = data_code(*(
                    _parse_value(arg, line) for arg in _split_args(match[2])))
        else:
            raise DslError(line, f"unrecognized statement {statement!r}")

    if graph.outputs is None or not graph.calls:
        raise DslError(line, "expected an output statement and calls")
    if len(graph.inputs) > MAX_GRAPH_INPUTS:
        raise DslError(line, f"more than {MAX_GRAPH_INPUTS} inputs")
    if len(graph.outputs) > MAX_GRAPH_OUTPUTS:
        raise DslError(line, f"more than {MAX_GRAPH_OUTPUTS} outputs")
    if len(graph.ids) > MAX_NODES:
        raise DslError(line, f"more than {MAX_NODES} nodes")
    for call in graph.calls:
        missing = [n for n, _, _ in graph.inputs if n not in call.inputs]
        if missing:
            raise DslError(line, f"call {call.label} has no value for "
                           f"{', '.join(missing)}")
    return graph

#
# Graphcode
#


def _u16(n):
    """The interpreter reads graphcode with memcpy, so in host order, which is
    little-endian on x86"""
    return struct.pack("<H", n)


def _shape_bytes(dims):
    return bytes([len(dims)]) + b"".join(map(_u16, dims))


def _param_bytes(kind, param):
    if kind == "shape":
        return _shape_bytes(param)
    if kind == "dtype":
        return bytes([param.id])
    if kind in ("axis", "bits"):
        return bytes([param])
    if kind == "int64":
        return struct.pack("<q", param)
    if kind == "type":
        return bytes([param[0].id]) + _shape_bytes(param[1])
    if kind == "address":
        return param
    if kind == "offset":
        return struct.pack("<I", param)
    return (bytes([param.dtype.id]) + _shape_bytes(param.dims)
            + param.dtype.encode(param.values, "little"))


def data_code(*tensors):
    """The code of an account holding `tensors` for tensorref: a 0x00 byte, so
    that a call to the account stops at once, then each tensor encoded as a
    literal is, one after another"""
    return b"\0" + b"".join(_param_bytes("tensor", t) for t in tensors)


def graphcode(graph):
    code = _u16(MAGIC) + bytes([len(graph.inputs)])
    for _, dtype, dims in graph.inputs:
        code += bytes([dtype.id]) + _shape_bytes(dims)
    code += bytes([len(graph.outputs)]) + b"".join(map(_u16, graph.outputs))
    code += _u16(len(graph.nodes))
    for node in graph.nodes:
        op, kinds, _ = OPS[node.op]
        code += _u16(OP_IDS[op])
        param_kinds = [k for k in kinds if k != "node"]
        code += b"".join(_param_bytes(kind, param)
                         for kind, param in zip(param_kinds, node.params))
        code += b"".join(map(_u16, node.inputs))
    return code

#
# JSON graphs
#

# Op names in JSON graphs, as in graph.hpp, and the DSL's for them
_JSON_OPS = {
    "Literal": "literal", "Add": "add", "Sub": "sub", "Mul": "mul",
    "Max": "max", "Min": "min", "Greater": "greater", "Ge": "ge",
    "Equal": "equal", "Where": "where", "Reshape": "reshape",
    "Saturate": "saturate", "Expand": "expand", "CumSum": "cumsum",
    "Div": "div", "MatMul": "matmul", "ArgMax": "argmax",
}


def _nest(values, dims):
    """Row-major `values` as lists nested to `dims`"""
    if not dims:
        return values[0]
    step = len(values) // dims[0] if dims[0] else 0
    return [_nest(values[i * step:(i + 1) * step], dims[1:])
            for i in range(dims[0])]


def json_to_dsl(text):
    """The statements for a graph in the JSON form of mnist.json"""
    graph = json.loads(text)
    lines = [f"input t{i}: {tensor['dtype']}{tensor['shape']}"
             for i, tensor in enumerate(graph["inputs"])]
    for id, node in enumerate(graph["nodes"], len(graph["inputs"])):
        op, params = node["op"], node.get("parameters", {})
        if op not in _JSON_OPS:
            raise ValueError(f"node {id}: unsupported op {op}")
        args = [f"t{i}" for i in node["inputs"]]
        try:
            if op == "Literal":
                args = [f"{params['dtype']}{params['shape']} "
                        f"{_nest(params['data'], params['shape'])}"]
            elif op in ("Reshape", "Expand"):
                args.append(str(params["shape"]))
            elif op == "Saturate":
                args.append(params["output_dtype"])
            elif op == "CumSum":
                args.append(str(params["axis"]))
            elif op == "Div":
                args.append(str(params["denominator"]))
        except KeyError as e:
            raise ValueError(f"node {id}: {op} has no parameter {e}") from None
        lines.append(f"t{id} = {_JSON_OPS[op]}({', '.join(args)})")
    lines.append("output " + ", ".join(f"t{i}" for i in graph["outputs"]))
    return "\n".join(lines) + "\n"

#
# Fixture
#


def _abi_tensor(tensor, byteorder="big"):
    return encode_tensor_tuple(tensor.dtype.id, tensor.dims,
                               tensor.dtype.encode(tensor.values, byteorder))


def _abi_tensor_input(spec):
    """abi.encode of a TensorInput tuple, (uint8 dtype, uint16[] dimensions,
    uint8 byteOrder, uint8 location, bytes payload)"""
    dims_offset = 5 * 32
    payload_offset = dims_offset + 32 * (1 + len(spec.dims))
    return (word(spec.dtype.id) + word(dims_offset)
            + word(spec.order) + word(spec.location)
            + word(payload_offset) + word(len(spec.dims))
            + b"".join(word(d) for d in spec.dims)
            + word(len(spec.payload)) + pad32(spec.payload))


def _abi_tensor_output(spec):
    """abi.encode of a TensorOutput tuple, (uint8 byteOrder, uint8 location,
    bytes payload)"""
    return (word(spec.order) + word(spec.location) + word(3 * 32)
            + word(len(spec.payload)) + pad32(spec.payload))


def _abi_array(tuples):
    """The tail of an array of dynamic tuples, given their encodings"""
    return (word(len(tuples)) + tensor_array_offsets(tuples)
            + b"".join(tuples))


def call_calldata(graph, call):
    """evalGraph(graph, inputs), or evalGraphInto(graph, inputs, outputs)"""
    graph_word = word(int.from_bytes(GRAPH_ADDRESS, "big"))
    inputs = _abi_array([_abi_tensor_input(call.inputs[name])
                         for name, _, _ in graph.inputs])
    if call.outputs is None:
        return (keccak256(EVAL_GRAPH_SIGNATURE)[:4] + graph_word
                + word(0x40) + inputs)
    outputs = _abi_array([_abi_tensor_output(o) for o in call.outputs])
    return (keccak256(EVAL_GRAPH_INTO_SIGNATURE)[:4] + graph_word
            + word(0x60) + word(0x60 + len(inputs)) + inputs + outputs)


#
# Tensors in storage
#


def _slots(size):
    """The number of 32-byte slots `size` bytes take"""
    return (size + 31) // 32


def load_slots(storage, slot, size):
    """The first `size` bytes in the contiguous slots from `slot` on, as the
    precompile's load_storage_tensor reads a tensor's elements: in order, 32
    bytes to a slot, each slot's first byte its most significant"""
    return b"".join(storage.get((slot + i) % (1 << 256), 0).to_bytes(32, "big")
                    for i in range(_slots(size)))[:size]


def store_slots(storage, slot, data):
    """Stores `data` in the contiguous slots from `slot` on, as the
    precompile's store_storage_tensor does, with the bytes past it in the last
    slot zero"""
    for i in range(_slots(len(data))):
        storage[(slot + i) % (1 << 256)] = int.from_bytes(
            data[32 * i:32 * i + 32].ljust(32, b"\0"), "big")


def _slots_overlap(a, a_size, b, b_size):
    """Whether the slots `a_size` and `b_size` bytes take from slots `a` and
    `b` overlap; slots wrap around at 2^256"""
    return ((b - a) % (1 << 256) < _slots(a_size)
            or (a - b) % (1 << 256) < _slots(b_size))


#
# Calls
#


def _check_input(spec):
    """Raises GraphError for a TensorInput the precompile can't decode, as
    abi_decode_tensor_input does"""
    if (spec.order > BYTE_ORDERS["Last_valid"]
            or spec.location > LOCATIONS["Last_valid"]):
        raise GraphError("InvalidInput")
    size = math.prod(spec.dims) * spec.dtype.size
    if size >= 1 << 64:
        raise GraphError("ShapeError")
    if spec.location == LITERAL and len(spec.payload) != size:
        raise GraphError("ShapeError")
    # abi.encode(address, uint32), each a word, with its high bytes zero
    if spec.location == CODE and (
            len(spec.payload) != 64 or any(spec.payload[:12])
            or any(spec.payload[32:60])):
        raise GraphError("InvalidInput")
    if spec.location == STORAGE and len(spec.payload) != 32:
        raise GraphError("InvalidInput")


def _check_output(spec):
    """Raises GraphError for a TensorOutput the precompile can't decode, as
    abi_decode_tensor_output does: it's returned, as a literal, with an empty
    payload, or stored, with a slot, but can't go to code"""
    if (spec.order > BYTE_ORDERS["Last_valid"]
            or spec.location not in (LITERAL, STORAGE)
            or len(spec.payload) != (0 if spec.location == LITERAL else 32)):
        raise GraphError("InvalidInput")


def _resolve_input(spec, accounts, storage):
    """A checked TensorInput's value: a literal's, or a reference's, from an
    account's code or `storage`. Raises RunError for a reference to code whose
    data doesn't match its header"""
    dtype, dims, byteorder = spec.dtype, spec.dims, _byteorder(spec.order)
    if spec.location == LITERAL:
        return Tensor(dtype, dims,
                      _decode_values(dtype, spec.payload, byteorder))
    if spec.location == CODE:
        return _code_tensor(accounts, dtype, dims, spec.payload[12:32],
                            int.from_bytes(spec.payload[60:], "big"),
                            byteorder)
    data = load_slots(storage, int.from_bytes(spec.payload, "big"),
                      math.prod(dims) * dtype.size)
    return Tensor(dtype, dims, _decode_values(dtype, data, byteorder))


def run_call(graph, call):
    """The call's outcome: whether it succeeds, its return data, and the
    storage, slot -> word, of the contract that called the precompile
    afterwards, before it records the call. The checks come in the
    precompile's order: decoding, then the references' places, then the
    graph's checks, with evalGraphInto's number of outputs after its static
    ones, then the references' data, then the graph's run errors, then, for
    evalGraphInto, overlapping stored outputs, which takes their sizes"""
    storage = call.genesis_storage()
    delegatecall = call.mode in ("delegatecall", "static delegatecall")
    is_static = call.mode in ("staticcall", "static delegatecall")
    specs = [call.inputs[name] for name, _, _ in graph.inputs]
    try:
        for spec in specs:
            _check_input(spec)
        for spec in call.outputs or []:
            _check_output(spec)
        stored = [o for o in call.outputs or [] if o.location == STORAGE]
        slots = [o.payload for o in stored]
        if len(set(slots)) != len(slots):
            raise GraphError("InvalidInput")
        if not delegatecall and (stored or any(
                spec.location == STORAGE for spec in specs)):
            raise GraphError("StorageRefOutsideDelegateCall")
        if is_static and stored:
            raise GraphError("StorageWriteInStaticCall")

        args, ref_error = [], None
        for spec in specs:
            try:
                args.append(_resolve_input(spec, graph.accounts, storage))
            except RunError as e:
                ref_error = ref_error or e.args[0]
                args.append(e.placeholder)
        outputs = evaluate(graph, args, ref_error,
                           None if call.outputs is None else len(call.outputs))
    except GraphError as e:
        return False, ERROR_MESSAGES[e.args[0]].encode(), storage

    # abi.encode of the returned outputs, as Solidity returns a Tensor[]: the
    # offset of the array, its length, the tensors' offsets, then the tensors.
    # evalGraph returns them all, big-endian, and evalGraphInto those with
    # literal references, in their byte orders
    if call.outputs is None:
        return True, (word(0x20) + _abi_array(
            [_abi_tensor(output) for output in outputs])), storage
    stored = [(int.from_bytes(spec.payload, "big"), spec, output)
              for spec, output in zip(call.outputs, outputs)
              if spec.location == STORAGE]
    sizes = [len(output.values) * output.dtype.size for _, _, output in stored]
    if any(_slots_overlap(stored[i][0], sizes[i], stored[j][0], sizes[j])
           for i in range(len(stored)) for j in range(i)):
        return False, ERROR_MESSAGES["InvalidInput"].encode(), storage
    for slot, spec, output in stored:
        store_slots(storage, slot,
                    output.dtype.encode(output.values, _byteorder(spec.order)))
    returned = [_abi_tensor(output, _byteorder(spec.order))
                for spec, output in zip(call.outputs, outputs)
                if spec.location == LITERAL]
    return True, word(0x20) + _abi_array(returned), storage


def caller_storage(calldata, success, return_data):
    """What the caller contracts store: slot 0 = success, slot 1 = return data
    size, slot 2 + i = memory word i, for each word the return data reaches.
    Memory holds the calldata with the return data copied over it, so a
    partial last word ends with calldata bytes."""
    memory = return_data + calldata[len(return_data):]
    storage = {0: int(success), 1: len(return_data)}
    for i in range(0, len(return_data), 32):
        storage[2 + i // 32] = int.from_bytes(
            memory[i:i + 32].ljust(32, b"\x00"), "big")
    return storage


#
# Caller contracts
#

CALL, DELEGATECALL, STATICCALL = 0xF1, 0xF4, 0xFA


def _record_loop(push_end):
    """Stores the word at memory offset i at slot 2 + i / 32, for i from 0
    up to the value `push_end` pushes, with i on the stack, by 32"""
    return [
        PUSH0,                          # i = 0 (byte offset)
        "loop", 0x5B,
        push_end, 0x81, 0x10, 0x15,     # !(i < end)
        (PUSH1, "end"), 0x57,           # JUMPI end
        0x80, 0x51,                     # MLOAD(i)
        0x81, (PUSH1, 5), 0x1C,         # i >> 5
        (PUSH1, 2), 0x01, 0x55,         # SSTORE(2 + i / 32, word)
        (PUSH1, 32), 0x01,              # i += 32
        (PUSH1, "loop"), 0x56,          # JUMP loop
        "end", 0x5B, 0x00,
    ]


def _forwarder(call_opcode, target=GRAPH_EVAL_ADDRESS,
               gas=PRECOMPILE_CALL_GAS):
    """Forwards its calldata to `target`, by default the precompile, with
    CALL, STATICCALL or DELEGATECALL, passing it `gas`, and records the call as
    caller_storage says"""
    value = [PUSH0] if call_opcode == CALL else []
    return assemble([
        0x36, PUSH0, PUSH0, 0x37,           # CALLDATACOPY(0, 0, CALLDATASIZE)
        PUSH0, PUSH0, 0x36, PUSH0, *value,  # out 0/0, in 0/CALLDATASIZE
        push(target),
        push(gas),
        call_opcode,
        PUSH0, 0x55,                        # SSTORE(0, success)
        0x3D, (PUSH1, 1), 0x55,             # SSTORE(1, RETURNDATASIZE)
        0x3D, PUSH0, PUSH0, 0x3E,           # RETURNDATACOPY(0, 0, size)
    ] + _record_loop(0x3D))                 # up to RETURNDATASIZE


# Forwards its calldata to the precompile with DELEGATECALL, and returns
# whether that succeeded, as a word, then its return data. In a static
# context, it can't record the call itself
DELEGATE_RETURNER_CODE = assemble([
    0x36, PUSH0, PUSH0, 0x37,               # CALLDATACOPY(0, 0, CALLDATASIZE)
    PUSH0, PUSH0, 0x36, PUSH0,              # out 0/0, in 0/CALLDATASIZE
    (PUSH2, GRAPH_EVAL_ADDRESS),
    (PUSH3, PRECOMPILE_CALL_GAS),
    DELEGATECALL,
    0x3D, PUSH0, (PUSH1, 32), 0x3E,         # RETURNDATACOPY(32, 0, size)
    PUSH0, 0x52,                            # MSTORE(0, success)
    0x3D, (PUSH1, 32), 0x01, PUSH0, 0xF3,   # RETURN(0, 32 + RETURNDATASIZE)
])


def _static_recorder(inner):
    """Calls `inner`, a DELEGATE_RETURNER_CODE contract, with STATICCALL,
    forwarding its calldata, and records the precompile call it returns as
    caller_storage says"""
    return assemble([
        0x36, PUSH0, PUSH0, 0x37,           # CALLDATACOPY(0, 0, CALLDATASIZE)
        PUSH0, PUSH0, 0x36, PUSH0,          # out 0/0, in 0/CALLDATASIZE
        (PUSH20, int.from_bytes(inner, "big")),
        0x5A,                               # GAS
        STATICCALL, 0x50,
        (PUSH1, 32), PUSH0, PUSH0, 0x3E,    # RETURNDATACOPY(0, 0, 32)
        PUSH0, 0x51, PUSH0, 0x55,           # SSTORE(0, MLOAD(0)), success
        (PUSH1, 32), PUSH0, PUSH0, 0x37,    # CALLDATACOPY(0, 0, 32), back
        (PUSH1, 32), 0x3D, 0x03,            # end = RETURNDATASIZE - 32
        0x80, (PUSH1, 1), 0x55,             # SSTORE(1, end)
        0x80, (PUSH1, 32), PUSH0, 0x3E,     # RETURNDATACOPY(0, 32, end)
    ] + _record_loop(0x81))                 # up to end, under i


assert _forwarder(CALL) == CALLER_CODE


def build_fixture(graph, name, description, source_name):
    """The fixture, and a line describing each call's expected outcome"""
    contracts = {GRAPH_ADDRESS: (graphcode(graph), {})}
    genesis_storage = {}
    calls, outcomes = [], []
    for n, call in enumerate(graph.calls):
        calldata = call_calldata(graph, call)
        success, return_data, storage = run_call(graph, call)
        into = "" if call.outputs is None else " into"
        if success and call.outputs is None:
            result = f"returns {graph.outputs and len(graph.outputs)} outputs"
        elif success:
            returned = sum(o.location == LITERAL for o in call.outputs)
            result = (f"returns {returned} and stores "
                      f"{len(call.outputs) - returned} outputs")
        else:
            error = next(e for e, m in ERROR_MESSAGES.items()
                         if m == return_data.decode())
            result = f"reverts with \"{return_data.decode()}\" ({error})"
        mode = "" if call.mode == "call" else f" ({call.mode})"
        outcomes.append(f"call {call.label}{mode}{into}: {result}")

        caller = (CALLER_BASE_ADDRESS + n).to_bytes(20, "big")
        records = caller_storage(calldata, success, return_data)
        genesis = call.genesis_storage()
        if call.mode == "static delegatecall":
            # The call runs for the inner contract, whose storage stays as it
            # is, as the call is static
            inner = (INNER_BASE_ADDRESS + n).to_bytes(20, "big")
            contracts[caller] = (_static_recorder(inner), records)
            contracts[inner] = (DELEGATE_RETURNER_CODE, storage)
            genesis_storage[inner] = genesis
        else:
            overlap = sorted(set(records) & (set(genesis) | set(storage)))
            if overlap:
                raise ValueError(
                    f"call {call.label}'s storage at slots {overlap} would "
                    f"overlap the slots that record the call")
            opcode = {"call": CALL, "staticcall": STATICCALL,
                      "delegatecall": DELEGATECALL}[call.mode]
            contracts[caller] = (_forwarder(opcode), {**storage, **records})
            genesis_storage[caller] = genesis
        # Generous, since Monad charges the whole limit either way: the
        # precompile's gas, calldata, and a storage write per slot
        gas_limit = (500_000 + PRECOMPILE_CALL_GAS + 16 * len(calldata)
                     + 50_000 * (len(records) + len(storage)))
        calls.append((caller, calldata, gas_limit))
    for address, code in graph.accounts.items():
        if address in contracts:
            raise ValueError(f"data at 0x{address.hex()} would replace the "
                             f"graph or a caller")
        contracts[address] = (code, {})
    if sum(gas for _, _, gas in calls) > BLOCK_GAS_LIMIT:
        raise ValueError("the calls need more than the block gas limit")

    fixture = blockchain_test(name, description, contracts, calls,
                              genesis_storage)
    for test in fixture.values():
        test["_info"]["comment"] = (
            f"Generated by graph_fixture.py from {source_name}")
    return fixture, outcomes


def _is_fixture(path):
    """Whether `path` holds a fixture this script wrote, which it may replace"""
    try:
        tests = json.loads(path.read_text())
        return all(test["_info"]["comment"].startswith(
            "Generated by graph_fixture.py") for test in tests.values())
    except (ValueError, KeyError, TypeError, AttributeError):
        return False


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("graph", type=Path, help="the graph and calls to it")
    parser.add_argument("-o", "--output", type=Path,
                        help="default: the graph file with a .json suffix, "
                        "or standard output with --from-json")
    parser.add_argument("--from-json", action="store_true",
                        help="convert a JSON graph to this format instead")
    args = parser.parse_args()

    text = args.graph.read_text()
    if args.from_json:
        try:
            dsl = json_to_dsl(text)
        except (ValueError, KeyError) as e:
            parser.exit(1, f"{args.graph}: {e}\n")
        if args.output:
            args.output.write_text(dsl)
        else:
            print(dsl, end="")
        return
    try:
        fixture, outcomes = build_fixture(
            parse(text), f"graph_eval/graph_{args.graph.stem}",
            _description(text) or f"evalGraph calls of {args.graph.name}",
            args.graph.name)
    except (DslError, ValueError) as e:
        parser.exit(1, f"{args.graph}: {e}\n")
    output = args.output or args.graph.with_suffix(".json")
    if not args.output and output.exists() and not _is_fixture(output):
        parser.exit(1, f"{output} exists and isn't a fixture from "
                    f"graph_fixture.py; name the output with -o\n")
    output.write_text(json.dumps(fixture, indent=2) + "\n")
    for outcome in outcomes:
        print(outcome)
    print(f"Wrote {output}")


if __name__ == "__main__":
    main()

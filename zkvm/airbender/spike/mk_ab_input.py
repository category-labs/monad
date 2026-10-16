#!/usr/bin/env python3
"""The Airbender guest's input for a witnessed block, its trie blob laid out
for word copies.

The ZisK guest's input (run/w/rpc_<b>.in) is work/aot/convert_witness.py's
offset-format blob for run/w/rpc_<b>.witness. This builds the same blob, with
filler bytes (Tag::PAD, which the guest's walk steps over) where they make a
copy move whole words on rv32, which has no unaligned access:

- before each run of a branch's consecutive digest children: the guest copies
  the run straight into the branch's RLP (a digest node is already the RLP of
  its reference), which it writes back from the end of a word-aligned buffer;
  the run's place there is the end less the value byte and the references of
  the children after it, all known here. The run then sits at the offset in a
  word it is copied to.
- before each branch node: its sixteen child ids, read by words when aligned.
- before an extension's digest child: copied to the end of its RLP less 33.

The blob's own offset in the guest's input buffer (word-aligned) is the
envelope's lead, which depends on the blob's length: built twice when the
first guess is off.

usage: mk_ab_input.py <block>... [--plain]   -> out/abin/rpc_<b>.in
  --plain: no filler; the output must equal run/w/rpc_<b>.in"""
import os
import struct
import sys

# MONAD_ZKVM_WORK holds airbender/ (stack/, out/, build-rv32/) and run/w/
# (the witnesses); by default the directory two above this checkout (from
# argv[0]: the scripts that exec this file's helpers sit beside it).
W = os.environ.get("MONAD_ZKVM_WORK") or os.path.abspath(
    os.path.join(os.path.dirname(os.path.abspath(sys.argv[0])), *[".."] * 5))
OUT = f"{W}/airbender/out/abin"
PAD = ord("P")


# ── RLP (as convert_witness.py) ──────────────────────────────────────────────
def rlp_item(b, i):
    x = b[i]
    if x < 0x80:
        return False, i, 1, i + 1
    if x < 0xB8:
        return False, i + 1, x - 0x80, i + 1 + x - 0x80
    if x < 0xC0:
        ll = x - 0xB7
        n = int.from_bytes(b[i + 1:i + 1 + ll], "big")
        return False, i + 1 + ll, n, i + 1 + ll + n
    if x < 0xF8:
        return True, i + 1, x - 0xC0, i + 1 + x - 0xC0
    ll = x - 0xF7
    n = int.from_bytes(b[i + 1:i + 1 + ll], "big")
    return True, i + 1 + ll, n, i + 1 + ll + n


def rlp_list(b):
    is_list, s, n, end = rlp_item(b, 0)
    assert is_list and end == len(b)
    out, i = [], s
    while i < s + n:
        _, _, _, j = rlp_item(b, i)
        out.append(b[i:j])
        i = j
    return out


def rlp_payload(enc):
    is_list, s, n, _ = rlp_item(enc, 0)
    return is_list, enc[s:s + n]


def rlp_len_prefix(n, base):
    if n < 56:
        return bytes([base + n])
    nb = n.to_bytes((n.bit_length() + 7) // 8, "big")
    return bytes([base + 55 + len(nb)]) + nb


def rlp_str(b):
    if len(b) == 1 and b[0] < 0x80:
        return b
    return rlp_len_prefix(len(b), 0x80) + b


def rlp_uint(n):
    return rlp_str(n.to_bytes((n.bit_length() + 7) // 8, "big") if n else b"")


# keccak only to index the witness's nodes by hash: the pure-Python one the
# runner scripts use
_src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "ab_run.py")).read()
_ns = {}
exec(_src.split("\ndef main():")[0], _ns)
keccak256 = _ns["keccak256"]


def hp_decode(b):
    nibs = []
    for x in b:
        nibs += [x >> 4, x & 15]
    flag = nibs[0]
    return (nibs[1:] if flag & 1 else nibs[2:]), bool(flag & 2)


def path_bytes(nibs):
    out = bytearray([len(nibs)]) + bytearray((len(nibs) + 1) // 2)
    for i, n in enumerate(nibs):
        out[1 + i // 2] |= n << (4 if i % 2 == 0 else 0)
    return bytes(out)


class Builder:
    """convert_witness.py's builder, with PAD bytes where they align a copy
    (when `base` is not None: the blob's offset in a word of the input)."""

    def __init__(self, by_hash, base):
        self.by_hash = by_hash
        self.base = base
        self.buf = bytearray(b"MZW\x01\x00\x00\x00\x00")
        self.digests = 0
        self.pads = 0

    def emit(self, data):
        off = len(self.buf)
        self.buf += data
        return off

    def pad_to(self, want):
        """Filler until the next byte's address is `want` mod 4."""
        if self.base is None:
            return
        k = (want - self.base - len(self.buf)) % 4
        self.buf += bytes([PAD]) * k
        self.pads += k

    def is_digest(self, ref):
        """Whether a parent's child reference becomes a digest node."""
        is_list, payload = rlp_payload(ref)
        return not is_list and len(payload) == 32 and payload not in self.by_hash

    def child(self, ref, storage):
        is_list, payload = rlp_payload(ref)
        if is_list:
            return self.node(ref, storage)
        if len(payload) == 0:
            return 0
        assert len(payload) == 32
        return self.by_ref(payload, storage)

    def by_ref(self, h, storage):
        node = self.by_hash.get(h)
        if node is None:
            self.digests += 1
            return self.emit(b"\xa0" + h)
        return self.node(node, storage)

    def root(self, h, storage):
        if h == bytes.fromhex("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"):
            return 0
        return self.by_ref(h, storage)

    def node(self, rlp, storage):
        items = rlp_list(rlp)
        if len(items) == 17:
            assert rlp_payload(items[16])[1] == b"", "branch with value"
            # The guest writes the branch's RLP back from a word-aligned end:
            # the value's byte, then child 15's reference down to child 0's.
            # Child i's reference starts after[i] bytes before the end.
            after, acc = [0] * 16, 1
            for i in range(15, -1, -1):
                acc += len(items[i])
                after[i] = acc
            kids = []
            for i in range(16):
                if self.is_digest(items[i]) and (i == 0 or not self.is_digest(items[i - 1])):
                    self.pad_to(-after[i] % 4)
                kids.append(self.child(items[i], storage))
            self.pad_to(3)  # the payload, after the tag byte, on a word
            return self.emit(b"\x00" + struct.pack("<16I", *kids))
        assert len(items) == 2
        nibs, leaf = hp_decode(rlp_payload(items[0])[1])
        if not leaf:
            if self.is_digest(items[1]):
                self.pad_to(-33 % 4)  # the reference closes the extension's RLP
            c = self.child(items[1], storage)
            return self.emit(b"\x01" + struct.pack("<I", c) + path_bytes(nibs))
        value = rlp_payload(items[1])[1]
        if storage:
            v = rlp_payload(value)[1] if value and value[0] >= 0x80 else value
            assert len(v) <= 32
            return self.emit(b"\x03" + v.rjust(32, b"\x00") + path_bytes(nibs))
        nonce, balance, sroot, chash = (rlp_payload(x)[1] for x in rlp_list(value))
        s = self.root(sroot, True)
        nb = rlp_uint(int.from_bytes(nonce, "big")) + rlp_uint(int.from_bytes(balance, "big"))
        assert len(chash) == 32
        return self.emit(b"\x02" + struct.pack("<I", s) + b"\xa0" + chash
                         + bytes([len(nb)]) + nb + path_bytes(nibs))


def build(witness_path, plain):
    fields = rlp_list(open(witness_path, "rb").read())
    assert len(fields) == 6, len(fields)
    block_rlp = rlp_payload(fields[0])[1]
    nodes = [n if rlp_payload(n)[0] else rlp_payload(n)[1] for n in rlp_list(fields[1])]
    by_hash = {keccak256(n): n for n in nodes}
    headers = [rlp_payload(h)[1] for h in rlp_list(fields[3])]
    state_root = rlp_payload(rlp_list(headers[-1])[3])[1]
    rest = fields[2] + fields[3] + fields[4] + fields[5]

    def envelope(blob):
        inner = rlp_str(block_rlp) + rlp_len_prefix(len(blob), 0xC0)
        body_len = len(inner) + len(blob) + len(rest)
        lead = len(rlp_len_prefix(body_len, 0xC0)) + len(inner)
        return lead, rlp_len_prefix(body_len, 0xC0) + inner + blob + rest

    base = None if plain else 0
    for _ in range(3):
        b = Builder(by_hash, base)
        root_off = b.root(state_root, False)
        struct.pack_into("<I", b.buf, 4, root_off)
        lead, out = envelope(bytes(b.buf))
        if base is None or lead % 4 == base:
            return out, b
        base = lead % 4
    raise RuntimeError("blob offset did not settle")


def main():
    plain = "--plain" in sys.argv
    os.makedirs(OUT, exist_ok=True)
    for arg in (a for a in sys.argv[1:] if not a.startswith("--")):
        cw, b = build(f"{W}/run/w/rpc_{arg}.witness", plain)
        fr = len(cw).to_bytes(8, "little") + cw
        data = fr + b"\0" * ((8 - len(fr) % 8) % 8)
        path = f"{OUT}/rpc_{arg}.in"
        open(path, "wb").write(data)
        same = ""
        if plain:
            same = " same as run/w" if data == open(f"{W}/run/w/rpc_{arg}.in", "rb").read() else " DIFFERS from run/w"
        print(f"{arg}: blob {len(b.buf)} B, {b.digests} digests, {b.pads} pad bytes{same}")


if __name__ == "__main__":
    main()

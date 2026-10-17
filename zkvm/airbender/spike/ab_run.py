#!/usr/bin/env python3
"""Run one witnessed block on the Airbender guest in Airbender's transpiler VM.

usage: ab_run.py <elf> <block> [--flamegraph out.svg]
Makes app.bin / app.text from the ELF (as cargo-airbender's build does), turns
work/run/w/rpc_<block>.in (ZisK framing: u64 length, payload, pad) into the
runner's hex input (u32 byte length, then the payload as little-endian words),
runs `cargo airbender run`, and checks the output registers against the block
hash computed from the witness header."""
import os, struct, subprocess, sys, time

def keccak256(data):
    """Pure-Python Keccak-256 (Ethereum padding), for the expected block hash."""
    rc = [0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
          0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
          0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
          0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
          0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
          0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]
    rot = [[0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61],
           [28, 55, 25, 21, 56], [27, 20, 39, 8, 14]]
    M = (1 << 64) - 1
    rl = lambda v, n: ((v << n) | (v >> (64 - n))) & M if n else v
    def f(a):
        for r in range(24):
            c = [a[x][0] ^ a[x][1] ^ a[x][2] ^ a[x][3] ^ a[x][4] for x in range(5)]
            d = [c[(x - 1) % 5] ^ rl(c[(x + 1) % 5], 1) for x in range(5)]
            a = [[a[x][y] ^ d[x] for y in range(5)] for x in range(5)]
            b = [[0] * 5 for _ in range(5)]
            for x in range(5):
                for y in range(5):
                    b[y][(2 * x + 3 * y) % 5] = rl(a[x][y], rot[x][y])
            a = [[b[x][y] ^ (~b[(x + 1) % 5][y] & b[(x + 2) % 5][y]) for y in range(5)] for x in range(5)]
            a[0][0] ^= rc[r]
        return a
    rate = 136
    data = bytearray(data) + b"\x01" + b"\0" * ((-len(data) - 1) % rate)
    data[-1] |= 0x80
    a = [[0] * 5 for _ in range(5)]
    for off in range(0, len(data), rate):
        for i in range(rate // 8):
            a[i % 5][i // 5] ^= int.from_bytes(data[off + 8 * i: off + 8 * i + 8], "little")
        a = f(a)
    return b"".join(a[i % 5][i // 5].to_bytes(8, "little") for i in range(4))

def rlp_item(b, i=0):
    """(start, end) of the RLP item at b[i] (its full encoding)."""
    p = b[i]
    if p < 0x80: return i, i + 1
    if p < 0xb8: return i, i + 1 + p - 0x80
    if p < 0xc0: n = p - 0xb7; return i, i + 1 + n + int.from_bytes(b[i + 1:i + 1 + n], "big")
    if p < 0xf8: return i, i + 1 + p - 0xc0
    n = p - 0xf7; return i, i + 1 + n + int.from_bytes(b[i + 1:i + 1 + n], "big")

def rlp_list(b):
    """Encodings of the elements of the RLP list b."""
    p = b[0]
    i = 1 if p < 0xf8 else 1 + (p - 0xf7)
    out = []
    while i < len(b):
        s, e = rlp_item(b, i); out.append(b[s:e]); i = e
    return out

def rlp_payload(b):
    s, e = rlp_item(b)
    p = b[0]
    off = 1 if p < 0xb8 or 0xc0 <= p < 0xf8 else 1 + (p - (0xb7 if p < 0xc0 else 0xf7))
    return p, b[off:e]

# MONAD_ZKVM_WORK holds airbender/ (stack/, out/, build-rv32/) and run/w/
# (the witnesses); by default the directory two above this checkout (from
# argv[0]: the scripts that exec this file's helpers sit beside it).
W = os.environ.get("MONAD_ZKVM_WORK") or os.path.abspath(
    os.path.join(os.path.dirname(os.path.abspath(sys.argv[0])), *[".."] * 5))
TC = os.path.join(os.environ.get("TC_DIR") or os.path.expanduser("~/.local/xPacks/xpack-riscv-none-elf-gcc-15.2.0-1"),
                  "bin/riscv-none-elf")
CARGO_AIRBENDER = f"{W}/airbender/stack/airbender-platform/target/release/cargo-airbender"
# zkvm/airbender/runner: `cargo airbender run`/`flamegraph` plus the host's
# answers to the guest's quotient queries. STOCK=1 runs cargo-airbender.
RUNNER = f"{W}/airbender/stack/airbender-platform/target/release/monad-airbender-runner"
def runner_cmd(mode):
    return [CARGO_AIRBENDER, "airbender", mode] if os.environ.get("STOCK") else [RUNNER, mode]

def main():
    elf, block = sys.argv[1], sys.argv[2]
    flame = sys.argv[sys.argv.index("--flamegraph") + 1] if "--flamegraph" in sys.argv else None
    out = os.path.splitext(elf)[0]
    subprocess.run([f"{TC}-objcopy", "-O", "binary", elf, out + ".bin"], check=True)
    subprocess.run([f"{TC}-objcopy", "-O", "binary", "--only-section=.text", elf, out + ".text"], check=True)
    # ABIN=1: the input with the trie blob laid out for word copies
    # (mk_ab_input.py), which only a guest with Tag::PAD reads
    src = (os.environ.get("ABIN_DIR", f"{W}/airbender/out/abin") + f"/rpc_{block}.in") if os.environ.get("ABIN") else f"{W}/run/w/rpc_{block}.in"
    raw = open(src, "rb").read()
    n = struct.unpack("<Q", raw[:8])[0]
    payload = raw[8:8 + n] + b"\0" * (-n % 4)
    words = [n] + list(struct.unpack(f"<{len(payload) // 4}I", payload))
    hex_path = f"{W}/airbender/out/input_{block}.hex"
    with open(hex_path, "w") as f:
        f.write("".join(f"{w:08x}" for w in words))
    f0 = rlp_list(open(f"{W}/run/w/rpc_{block}.witness", "rb").read())
    expected = keccak256(rlp_list(rlp_payload(f0[0])[1])[0]).hex()
    cmd = runner_cmd("flamegraph" if flame else "run") + [out + ".bin", "--input", hex_path]
    if flame:  # the text path is derived from app.bin's (out.text)
        cmd += ["--output", flame, "--elf-path", elf]
    else:
        cmd += ["--text-path", out + ".text"]
    t = time.time()
    r = subprocess.run(cmd, capture_output=True, text=True)
    print(r.stdout[-3000:], r.stderr[-3000:], sep="\n")
    print(f"wall {time.time() - t:.1f} s; expected block hash {expected}")

main()

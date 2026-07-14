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

# Serialize the go-ethereum precompile golden vectors into a single binary blob
# consumed by the zkVM precompile-test guest (zkvm/guest/precompile_test.cpp).
# The guest runs each vector through the matching precompile `_execute` shim
# (which routes crypto through the SP1/ZisK accelerators) and checks the output,
# so we exercise the accelerator ABI without needing block witnesses.
#
# Blob format (little-endian):
#   magic "PT01" | count u32
#   per case: addr u16 | input_len u32 | input | kind u8 | out_len u32 | out
#     kind 0 = success  -> `out` is the expected output (may be empty)
#     kind 1 = failure   -> `out` is empty; the precompile must reject the input
#
# Usage: gen_precompile_vectors.py <geth-testdata-dir> <out.bin>

import json
import struct
import sys
from pathlib import Path

# geth golden file -> (precompile address, kind). Mirrors the address mapping in
# category/execution/ethereum/precompiles_test.cpp.
FILES = [
    ("bn256Add.json", 0x06, 0),
    ("bn256ScalarMul.json", 0x07, 0),
    ("bn256Pairing.json", 0x08, 0),
    ("blake2F.json", 0x09, 0),
    ("fail-blake2f.json", 0x09, 1),
    ("modexp.json", 0x05, 0),
    ("modexp_eip2565.json", 0x05, 0),
    ("modexp_eip7883.json", 0x05, 0),
    ("blsG1Add.json", 0x0B, 0),
    ("fail-blsG1Add.json", 0x0B, 1),
    ("blsG1Mul.json", 0x0C, 0),
    ("blsG1MultiExp.json", 0x0C, 0),
    ("fail-blsG1Mul.json", 0x0C, 1),
    ("fail-blsG1MultiExp.json", 0x0C, 1),
    ("blsG2Add.json", 0x0D, 0),
    ("fail-blsG2Add.json", 0x0D, 1),
    ("blsG2Mul.json", 0x0E, 0),
    ("blsG2MultiExp.json", 0x0E, 0),
    ("fail-blsG2Mul.json", 0x0E, 1),
    ("fail-blsG2MultiExp.json", 0x0E, 1),
    ("blsPairing.json", 0x0F, 0),
    ("fail-blsPairing.json", 0x0F, 1),
    ("blsMapG1.json", 0x10, 0),
    ("fail-blsMapG1.json", 0x10, 1),
    ("blsMapG2.json", 0x11, 0),
    ("fail-blsMapG2.json", 0x11, 1),
    ("p256Verify.json", 0x0100, 0),
]


def main():
    if len(sys.argv) < 3:
        sys.exit(
            f"usage: {sys.argv[0]} <geth-testdata-dir> <out.bin> "
            "[--exclude 0x09,0x11]")
    src = Path(sys.argv[1])
    out = Path(sys.argv[2])
    exclude = set()
    if "--exclude" in sys.argv:
        spec = sys.argv[sys.argv.index("--exclude") + 1]
        exclude = {int(a, 16) for a in spec.split(",") if a}

    cases = bytearray()
    count = 0
    per_addr = {}
    for name, addr, kind in FILES:
        if addr in exclude:
            continue
        path = src / name
        if not path.is_file():
            sys.exit(f"missing golden file: {path}")
        for entry in json.load(open(path)):
            inp = bytes.fromhex(entry["Input"])
            if kind == 0:
                exp = bytes.fromhex(entry.get("Expected", ""))
            else:
                assert "ExpectedError" in entry, entry
                exp = b""
            cases += struct.pack("<HI", addr, len(inp)) + inp
            cases += struct.pack("<BI", kind, len(exp)) + exp
            count += 1
            per_addr[addr] = per_addr.get(addr, 0) + 1

    blob = b"PT01" + struct.pack("<I", count) + bytes(cases)
    out.write_bytes(blob)
    print(f"wrote {count} cases, {len(blob)} bytes -> {out}")
    for addr in sorted(per_addr):
        print(f"  0x{addr:02x}: {per_addr[addr]} cases")


if __name__ == "__main__":
    main()

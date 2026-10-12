#!/usr/bin/env python3
"""Frame raw Monad witnesses and compare guest public output with a block hash."""
import argparse
from pathlib import Path
import struct
import subprocess
import tempfile


def validate(data):
    if len(data) < 8:
        raise ValueError("input has no ZiskStdin length prefix")
    length = struct.unpack_from("<Q", data)[0]
    if not length or len(data) != 8 + ((length + 7) // 8) * 8:
        raise ValueError("expected exactly one framed witness; use 'frame' for raw .witness files")
    if any(data[8 + length:]):
        raise ValueError("nonzero ZiskStdin padding")


def compare(path, expected):
    digest = bytes.fromhex(expected.removeprefix("0x"))
    if len(digest) != 32:
        raise ValueError("expected block hash must contain 32 bytes")
    actual = path.read_bytes()
    if len(actual) < 32 or actual[:32] != digest:
        raise ValueError(f"block hash mismatch: got {actual[:32].hex()}, expected {digest.hex()}")
    print(f"Block hash matches: 0x{digest.hex()}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    subs = parser.add_subparsers(dest="command", required=True)
    frame = subs.add_parser("frame", help="raw .witness -> framed .bin (once only)")
    frame.add_argument("source", type=Path)
    frame.add_argument("destination", type=Path)
    check = subs.add_parser("check", help="execute a framed input and compare its public block hash")
    check.add_argument("input", type=Path)
    check.add_argument("expected_hash")
    check.add_argument("--elf", default="/opt/monad/monad-zkvm-zisk")
    validation = subs.add_parser("validate", help="check single-witness framing")
    validation.add_argument("input", type=Path)
    outputs = subs.add_parser("publics", help="compare saved proof public output")
    outputs.add_argument("output", type=Path)
    outputs.add_argument("expected_hash")
    args = parser.parse_args()
    if args.command == "frame":
        raw = args.source.read_bytes()
        if not raw:
            raise ValueError("empty witness")
        try:
            validate(raw)
        except ValueError:
            pass
        else:
            raise ValueError("already framed; copy the .bin directly")
        with args.destination.open("xb") as out:
            out.write(struct.pack("<Q", len(raw)) + raw + bytes((-len(raw)) % 8))
    elif args.command == "validate":
        validate(args.input.read_bytes())
    elif args.command == "check":
        validate(args.input.read_bytes())
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "publics.bin"
            subprocess.run(["ziskemu", "-e", args.elf, "-i", str(args.input), "-o", str(output)], check=True)
            compare(output, args.expected_hash)
    else:
        compare(args.output, args.expected_hash)


if __name__ == "__main__":
    main()

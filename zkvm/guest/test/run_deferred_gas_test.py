#!/usr/bin/env python3
"""Run a guest built with -DMONAD_ZKVM_GAS_SELFTEST=ON.

Build the eager reference with -DMONAD_ZKVM_GAS_CHECK_EVERY_OPCODE=ON as well.
Both variants must pass. No witness input is needed. Example:
  python3 zkvm/guest/test/run_deferred_gas_test.py --ziskemu /path/to/ziskemu /path/to/guest.elf
"""
import argparse
from pathlib import Path
import subprocess
import tempfile

CASES = [
    "STOP", "padded STOP", "truncated PUSH", "RETURN", "REVERT", "GAS",
    "backward JUMP", "untaken JUMPI", "INVALID", "stack underflow", "MLOAD",
    "SSTORE", "TSTORE", "SELFDESTRUCT", "LOG0", "SLOAD",
    "BLOCKHASH after OOG", "SELFBALANCE after OOG", "TLOAD after OOG",
    "BLOCKHASH gas boundary", "SELFBALANCE gas boundary", "TLOAD gas boundary",
    "stack overflow", "CALL", "pure chain gas sweep", "exact-gas RETURN",
    "exact-gas REVERT", "affordable host reads", "dynamic effects",
    "selector chain gas sweep", "mask widths and gas boundaries",
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--ziskemu", default="ziskemu")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="deferred-gas-") as directory:
        output = Path(directory) / "output.bin"
        subprocess.run(
            [args.ziskemu, "-e", str(args.elf), "-o", str(output),
             "-n", "100000000"], check=True, timeout=120,
        )
        data = output.read_bytes()
    if len(data) < 32 or data[4:8] != b"GAS2":
        raise SystemExit("Missing gas self-test completion marker")
    mask = int.from_bytes(data[:4], "little")
    if mask:
        failures = [name for i, name in enumerate(CASES) if mask & (1 << i)]
        raise SystemExit(f"FAIL mask={mask:#x}: {', '.join(failures)}")
    state_mask = int.from_bytes(data[8:12], "little")
    state_cases = ["writes completed", "accepted child / rejected parent",
                   "OOG before STOP", "OOG before RETURN", "OOG before REVERT",
                   "OOG before INVALID"]
    if state_mask:
        failures = [name for i, name in enumerate(state_cases) if state_mask & (1 << i)]
        raise SystemExit(f"FAIL State mask={state_mask:#x}: {', '.join(failures)}")
    print("PASS: 6 State rollback checks (5 production calls)")
    print(f"PASS: {len(CASES)} gas boundary groups (1228 interpreter executions)")


if __name__ == "__main__":
    main()

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
    "selector chain gas sweep", "immediate AND masks",
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
    print(f"PASS: {len(CASES)} gas boundary groups (208 interpreter executions)")


if __name__ == "__main__":
    main()

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

"""Run the guest built with MONAD_ZKVM_UINT256_SELFTEST=ON."""

import argparse
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--ziskemu", default="ziskemu")
    parser.add_argument("--host", action="store_true", help="Run the host executable")
    args = parser.parse_args()
    if args.host:
        subprocess.run([str(args.elf)], check=True, timeout=60)
        print("PASS software overrides (host)")
        return

    with TemporaryDirectory() as tmp:
        directory = Path(tmp)
        for selector, name in enumerate(
            ('software overrides', 'arithmetic opcodes and helpers')
        ):
            input_path = directory / f"{selector}.input"
            output_path = directory / f"{selector}.output"
            input_path.write_bytes(bytes([selector]))
            result = subprocess.run(
                [
                    args.ziskemu,
                    "-e",
                    str(args.elf),
                    "--legacy-inputs",
                    str(input_path),
                    "-o",
                    str(output_path),
                ],
                capture_output=True,
                text=True,
                timeout=60,
                check=False,
            )

            if selector <= 1:
                output = output_path.read_bytes() if output_path.exists() else b""
                if result.returncode != 0 or output[:9] != bytes(4) + b"U256" + bytes([selector]):
                    raise SystemExit(
                        f"FAIL {name}: exit {result.returncode}, output {output[:9].hex()}\n"
                        f"{result.stdout}{result.stderr}"
                    )
            elif result.returncode != 1 or "guest exited with code 1" not in result.stderr.lower():
                raise SystemExit(
                    f"FAIL {name}: expected guest assertion exit, got {result.returncode}\n"
                    f"{result.stdout}{result.stderr}"
                )

            print(f"PASS {name}")


if __name__ == "__main__":
    main()

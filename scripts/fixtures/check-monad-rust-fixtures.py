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

"""Check the Rust protocol/client snapshots against the C++ Viem vectors."""

import hashlib
import sys
from pathlib import Path

execution = Path(__file__).resolve().parents[2]
root = execution / "rust"
relative = Path("tests/fixtures/monad_type40_vectors.json")
paths = [root / "crates" / crate / relative for crate in ("monad-transaction", "monad-alloy")]
if len(sys.argv) != 1:
    raise SystemExit("usage: check-monad-rust-fixtures.py")
paths.append(execution / "category/execution/ethereum/core/test/monad_type40_vectors.json")

snapshots = [path.read_bytes() for path in paths]
if any(snapshot != snapshots[0] for snapshot in snapshots[1:]):
    raise SystemExit("transaction vector snapshots differ")
print(f"{len(paths)} identical snapshots: sha256={hashlib.sha256(snapshots[0]).hexdigest()}")

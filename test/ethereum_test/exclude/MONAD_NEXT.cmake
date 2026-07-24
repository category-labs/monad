# Copyright (C) 2025 Category Labs, Inc.
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

# These two fixtures come from the pinned MonadSpecTestFixtures release
# (tests-monad@v1.1.1), which predates SLOTNUM being added to MONAD_NEXT's
# opcode table at 0x4B. Both fail since SLOTNUM/0x4B is a valid opcode.
# Drop these entries once the fixture bundle is re-pinned past that point.
set(MONAD_NEXT_excluded_tests
      "BlockchainTests.for_monad_next/frontier/opcodes/all_opcodes/all_opcodes.json"
      "BlockchainTests.for_monad_next/frontier/scenarios/scenarios/scenarios.json"
)

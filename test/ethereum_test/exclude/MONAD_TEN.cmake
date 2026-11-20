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

set(MONAD_TEN_excluded_tests
    # The fixtures treat the staking precompile (0x1000) as a cold, empty
    # account; fix pending in monad-developers/execution-specs.
    "BlockchainTests.for_monad_ten/berlin/eip2929_gas_cost_increases/call/call_precompile_range_boundaries.json"
)

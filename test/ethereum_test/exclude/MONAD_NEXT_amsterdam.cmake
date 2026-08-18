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

# The MONAD_NEXT Amsterdam spec-test fixtures (EIP-7708, EIP-7843, EIP-8024)
# expect a block header carrying the SLOTNUM field, which the execution layer
# does not yet emit.
# Drop entries here to re-enable individual tests as support lands.
set(MONAD_NEXT_amsterdam_excluded_tests
  "BlockchainTests.for_monad_next/amsterdam/eip7843_slotnum/*"
  "BlockchainTests.for_monad_next/amsterdam/eip7708_eth_transfer_logs/*"
  "BlockchainTests.for_monad_next/amsterdam/eip8024_dupn_swapn_exchange/*"
  # Test contains a EIP-4844 blob which is disabled on Monad
  "BlockchainTests.for_monad_next/amsterdam/eip7981_increase_access_list_cost/transaction_validity/transactions_without_access_list.json"
)

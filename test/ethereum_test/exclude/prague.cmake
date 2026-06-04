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

set(prague_excluded_tests
    # Blobs (EIP-4844)
    "BlockchainTests.cancun/eip4844_blobs/test_invalid_excess_blob_gas_above_target_change.json"
    "BlockchainTests.cancun/eip4844_blobs/test_invalid_excess_blob_gas_change.json"
    "BlockchainTests.cancun/eip4844_blobs/test_invalid_excess_blob_gas_target_blobs_increase_from_zero.json"
    "BlockchainTests.cancun/eip4844_blobs/test_invalid_negative_excess_blob_gas.json"
    "BlockchainTests.cancun/eip4844_blobs/test_invalid_non_multiple_excess_blob_gas.json"
    "BlockchainTests.cancun/eip4844_blobs/test_invalid_static_excess_blob_gas.json"
    "BlockchainTests.cancun/eip4844_blobs/test_invalid_static_excess_blob_gas_from_zero_on_blobs_above_target.json"
    "BlockchainTests.cancun/eip4844_blobs/test_invalid_zero_excess_blob_gas_in_header.json"


    # Long-running tests
    "BlockchainTests.prague/eip2935_historical_block_hashes_from_state/block_hashes/block_hashes_history.json"

    # Stricter validation of base fee
    "BlockchainTests.london/validation/test_invalid_header.json"

    # EIP-7610
    "BlockchainTests.paris/eip7610_create_collision/test_init_collision_create_opcode.json"
    "BlockchainTests.paris/eip7610_create_collision/test_init_collision_create_tx.json"
    "BlockchainTests.static/state_tests/stCreate2/RevertInCreateInInitCreate2Paris.json"
    "BlockchainTests.static/state_tests/stCreate2/create2collisionStorageParis.json"
    "BlockchainTests.static/state_tests/stExtCodeHash/dynamicAccountOverwriteEmpty_Paris.json"
)

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


# The pinned bundle was generated against a spec without EIP-8246, which the
# commit beneath this one implements, so these fixtures encode the pre-8246
# SELFDESTRUCT behaviour: a Burn log where none is emitted any more, and a
# postState missing the balance-only account 8246 now preserves. Drop these
# entries when a bundle generated against a spec that has 8246 is pinned.
#
# The two burn_logs fixtures that assert the *absence* of a burn
# (selfdestruct_to_self_pre_existing_no_log, selfdestruct_to_different_address_
# same_tx) pass and are deliberately not listed. Names are
# fs::relative(path, blockchain_tests), so every one begins for_monad_next/.
set(MONAD_NEXT_amsterdam_excluded_tests
    "BlockchainTests.for_monad_next/amsterdam/eip7708_eth_transfer_logs/burn_logs/finalization_burn_log_single_account_multiple_transfers.json"
    "BlockchainTests.for_monad_next/amsterdam/eip7708_eth_transfer_logs/burn_logs/finalization_burn_logs.json"
    "BlockchainTests.for_monad_next/amsterdam/eip7708_eth_transfer_logs/burn_logs/finalization_burn_logs_multi_account_ordering.json"
    "BlockchainTests.for_monad_next/amsterdam/eip7708_eth_transfer_logs/burn_logs/selfdestruct_finalization_after_priority_fee.json"
    "BlockchainTests.for_monad_next/amsterdam/eip7708_eth_transfer_logs/burn_logs/selfdestruct_same_tx_via_call.json"
    "BlockchainTests.for_monad_next/amsterdam/eip7708_eth_transfer_logs/burn_logs/selfdestruct_to_self_same_tx.json"
    "BlockchainTests.for_monad_next/cancun/eip6780_selfdestruct/selfdestruct/create_selfdestruct_same_tx.json"
    "BlockchainTests.for_monad_next/cancun/eip6780_selfdestruct/selfdestruct/recreate_self_destructed_contract_different_txs.json"
    "BlockchainTests.for_monad_next/cancun/eip6780_selfdestruct/selfdestruct/self_destructing_initcode.json"
    "BlockchainTests.for_monad_next/cancun/eip6780_selfdestruct/selfdestruct_revert/selfdestruct_created_in_same_tx_with_revert.json"
    "BlockchainTests.for_monad_next/frontier/create/create_suicide_during_init/create_suicide_during_transaction_create.json"
    "BlockchainTests.for_monad_next/monad_nine/mip4_checkreservebalance/transfers/contract_unrestricted_within_initcode.json"
    "BlockchainTests.for_monad_next/paris/security/selfdestruct_balance_bug/tx_selfdestruct_balance_bug.json"
    "BlockchainTests.for_monad_next/tangerine_whistle/eip150_operation_gas_costs/eip150_selfdestruct/initcode_selfdestruct_to_self.json"
    "BlockchainTests.for_monad_next/tangerine_whistle/eip150_operation_gas_costs/eip150_selfdestruct/selfdestruct_to_self.json")

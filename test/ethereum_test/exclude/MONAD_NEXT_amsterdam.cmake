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

# Amsterdam spec tests are mutually dependent, so enable them together
# when all EIPs land.
# Every Amsterdam EIP in this fork is now implemented, and the fixture bundle is
# generated against a spec that has them, so nothing is excluded.
# Two groups, both waiting on an upstream fixture release rather than on
# anything in this tree.
#
# Gas: the pinned bundle was generated without EIP-7981, which main implements,
# so its intrinsic-gas budgets predate the access-list cost increase and these
# fixtures fail with "intrinsic gas greater than limit".
set(MONAD_NEXT_amsterdam_excluded_tests
  "BlockchainTests.for_monad_next/berlin/eip2930_access_list/acl/transaction_intrinsic_gas_cost.json"
  "BlockchainTests.for_monad_next/berlin/eip2930_access_list/tx_intrinsic_gas/tx_intrinsic_gas.json"
  "BlockchainTests.for_monad_next/cancun/eip5656_mcopy/mcopy_memory_expansion/mcopy_memory_expansion.json"
  "BlockchainTests.for_monad_next/osaka/eip7825_transaction_gas_limit_cap/tx_gas_limit/tx_gas_limit_cap_access_list_with_diff_addr.json"
  "BlockchainTests.for_monad_next/osaka/eip7825_transaction_gas_limit_cap/tx_gas_limit/tx_gas_limit_cap_access_list_with_diff_keys.json"
  "BlockchainTests.for_monad_next/osaka/eip7825_transaction_gas_limit_cap/tx_gas_limit/tx_gas_limit_cap_authorized_tx.json"
  "BlockchainTests.for_monad_next/prague/eip7623_increase_calldata_cost/transaction_validity/transaction_validity_type_4.json"
  "BlockchainTests.for_monad_next/prague/eip7702_set_code_tx/gas/intrinsic_gas_cost.json"
  #
  # Selfdestruct: the bundle implements EIP-7708 but not EIP-8246 -- upstream
  # carries an EIP8246 fork class and a selfdestruct_no_burn test directory, but
  # the class is a stub and no fixtures are generated from it. So on selfdestruct
  # paths these fixtures expect three things this tree correctly does not do:
  # a Transfer log where nothing moves (beneficiary == self keeps the balance
  # under rule 1, so there is no transfer to log), an account deleted that rule 2
  # preserves, and a balance burned that rule 2 keeps. Each fixture reports the
  # bloom mismatch first, then the post-state size and balance mismatches
  # underneath -- reading only the first line makes this look like a 7708
  # emission bug, which it is not.
  "BlockchainTests.for_monad_next/cancun/eip6780_selfdestruct/selfdestruct/create_selfdestruct_same_tx.json"
  "BlockchainTests.for_monad_next/cancun/eip6780_selfdestruct/selfdestruct/recreate_self_destructed_contract_different_txs.json"
  "BlockchainTests.for_monad_next/cancun/eip6780_selfdestruct/selfdestruct/self_destructing_initcode.json"
  "BlockchainTests.for_monad_next/cancun/eip6780_selfdestruct/selfdestruct_revert/selfdestruct_created_in_same_tx_with_revert.json"
  "BlockchainTests.for_monad_next/frontier/create/create_suicide_during_init/create_suicide_during_transaction_create.json"
  "BlockchainTests.for_monad_next/monad_nine/mip4_checkreservebalance/transfers/contract_unrestricted_within_initcode.json"
  "BlockchainTests.for_monad_next/paris/security/selfdestruct_balance_bug/tx_selfdestruct_balance_bug.json"
  "BlockchainTests.for_monad_next/tangerine_whistle/eip150_operation_gas_costs/eip150_selfdestruct/initcode_selfdestruct_to_self.json"
  "BlockchainTests.for_monad_next/tangerine_whistle/eip150_operation_gas_costs/eip150_selfdestruct/selfdestruct_to_self.json"
)

// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/execution/ethereum/dispatch_transaction.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/vm/evm/explicit_traits.hpp>

MONAD_NAMESPACE_BEGIN

template <Traits traits>
Result<Receipt> dispatch_transaction(
    Chain const &chain, uint64_t const i, Transaction const &transaction,
    Address const &sender,
    std::vector<std::optional<Address>> const &authorities,
    BlockHeader const &header, BlockHashBuffer const &block_hash_buffer,
    BlockState &block_state, BlockMetrics &block_metrics,
    boost::fibers::promise<void> &prev, CallTracerBase &call_tracer,
    RevertTransactionFn const &revert_transaction)
{
    return ExecuteTransaction<traits>{
        chain,
        i,
        transaction,
        sender,
        authorities,
        header,
        block_hash_buffer,
        block_state,
        block_metrics,
        prev,
        call_tracer,
        revert_transaction}();
}

EXPLICIT_EVM_TRAITS(dispatch_transaction)

MONAD_NAMESPACE_END

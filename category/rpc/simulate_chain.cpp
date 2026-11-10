// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/config.hpp>
#include <category/core/monad_exception.hpp>
#include <category/core/runtime/uint256.hpp>
#include <category/execution/ethereum/chain/blob_schedule.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/rpc/simulate_chain.hpp>
#include <category/vm/evm/revision.h>
#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <cstdint>
#include <memory>
#include <utility>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

BlobSchedule pinned_blob_schedule(monad_eth_revision const rev)
{
    SWITCH_EVM_TRAITS(default_blob_schedule);
    MONAD_ASSERT_THROW(false, "unreachable");
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

bool SimulateEvmChain::is_supported_revision(monad_eth_revision const rev)
{
    return rev >= constants::EARLIEST_SUPPORTED_EVM_FORK &&
           rev <= constants::LATEST_SUPPORTED_EVM_FORK;
}

SimulateEvmChain::SimulateEvmChain(
    std::unique_ptr<Chain const> inner, monad_eth_revision const rev)
    : inner_{std::move(inner)}
    , rev_{rev}
    , blob_schedule_{}
{
    MONAD_ASSERT_THROW(inner_ != nullptr, "inner chain must not be null");
    // Monad chains dispatch on `get_monad_revision`, which this wrapper does
    // not provide.
    MONAD_ASSERT_THROW(
        dynamic_cast<MonadChain const *>(inner_.get()) == nullptr,
        "inner chain must not be a MonadChain");
    MONAD_ASSERT_THROW(is_supported_revision(rev_), "unsupported EVM revision");
    blob_schedule_ = pinned_blob_schedule(rev_);
}

uint256_t SimulateEvmChain::get_chain_id() const
{
    return inner_->get_chain_id();
}

monad_eth_revision SimulateEvmChain::get_revision(
    uint64_t /*block_number*/, uint64_t /*timestamp*/) const
{
    return rev_;
}

BlobSchedule SimulateEvmChain::get_blob_schedule(uint64_t /*timestamp*/) const
{
    return blob_schedule_;
}

GenesisState SimulateEvmChain::get_genesis_state() const
{
    return inner_->get_genesis_state();
}

MONAD_NAMESPACE_END

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

#pragma once

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/chain/blob_schedule.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/execution_modalities.hpp>
#include <category/vm/evm/traits.hpp>

#include <optional>
#include <span>

MONAD_NAMESPACE_BEGIN

class State;
struct BlockHeader;
struct Receipt;
struct Transaction;

struct Chain
{
    virtual ~Chain() = default;

    virtual uint256_t get_chain_id() const = 0;

    virtual EvmRevision
    get_revision(uint64_t block_number, uint64_t timestamp) const = 0;

    virtual BlobSchedule get_blob_schedule(uint64_t timestamp) const = 0;

    virtual GenesisState get_genesis_state() const = 0;
};

template <typename T>
struct ChainContext;

template <typename T>
    requires is_evm_trait_v<T>
struct ChainContext<T>
{
    static constexpr ExecutionMode mode{};

    // Returns an empty ChainContext for unit testing purposes.
    // Not intended for production use.
    static ChainContext<T> const &debug_empty()
    {
        static ChainContext<T> const ctx{};
        return ctx;
    }
};

// Whether the context is a private domain block's, and whether a transaction
// in it is from DOMAIN_SYSTEM_RELAYER. Only Monad has private domains: see
// the Monad ChainContext and PROTOCOL.md in category-labs/monad-domains.
template <Traits traits>
bool is_private_domain(ChainContext<traits> const &);

template <Traits traits>
bool is_domain_system_relayer(
    ChainContext<traits> const &, Address const &sender);

MONAD_NAMESPACE_END

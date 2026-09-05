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

#include <category/vm/evm/tx_context.hpp>

#include <evmc/evmc.h>

#include <bit>
#include <cstddef>
#include <type_traits>

// Layout equality with evmc_tx_context; the bit_cast below relies on it.
static_assert(std::is_standard_layout_v<monad_tx_context>);
static_assert(std::is_trivially_copyable_v<monad_tx_context>);
static_assert(sizeof(monad_tx_context) == 264);
static_assert(sizeof(monad_tx_context) == sizeof(evmc_tx_context));
static_assert(alignof(monad_tx_context) == alignof(evmc_tx_context));

#define MONAD_ASSERT_TX_CONTEXT_FIELD_EQ(field)                                \
    static_assert(                                                             \
        offsetof(monad_tx_context, field) == offsetof(evmc_tx_context, field))

MONAD_ASSERT_TX_CONTEXT_FIELD_EQ(tx_gas_price);
MONAD_ASSERT_TX_CONTEXT_FIELD_EQ(tx_origin);
MONAD_ASSERT_TX_CONTEXT_FIELD_EQ(block_coinbase);
MONAD_ASSERT_TX_CONTEXT_FIELD_EQ(block_number);
MONAD_ASSERT_TX_CONTEXT_FIELD_EQ(block_timestamp);
MONAD_ASSERT_TX_CONTEXT_FIELD_EQ(block_gas_limit);
MONAD_ASSERT_TX_CONTEXT_FIELD_EQ(block_prev_randao);
MONAD_ASSERT_TX_CONTEXT_FIELD_EQ(chain_id);
MONAD_ASSERT_TX_CONTEXT_FIELD_EQ(block_base_fee);
MONAD_ASSERT_TX_CONTEXT_FIELD_EQ(blob_base_fee);
MONAD_ASSERT_TX_CONTEXT_FIELD_EQ(blob_hashes);
MONAD_ASSERT_TX_CONTEXT_FIELD_EQ(blob_hashes_count);
MONAD_ASSERT_TX_CONTEXT_FIELD_EQ(initcodes);
MONAD_ASSERT_TX_CONTEXT_FIELD_EQ(initcodes_count);
MONAD_ASSERT_TX_CONTEXT_FIELD_EQ(block_round);

#undef MONAD_ASSERT_TX_CONTEXT_FIELD_EQ

// Same offset does not rule out a narrowed integer padded back to the next
// field; the byte-array and pointer members are already size-pinned.
#define MONAD_ASSERT_TX_CONTEXT_FIELD_TYPE_EQ(field)                           \
    static_assert(std::is_same_v<                                              \
                  decltype(monad_tx_context::field),                           \
                  decltype(evmc_tx_context::field)>)

MONAD_ASSERT_TX_CONTEXT_FIELD_TYPE_EQ(block_number);
MONAD_ASSERT_TX_CONTEXT_FIELD_TYPE_EQ(block_timestamp);
MONAD_ASSERT_TX_CONTEXT_FIELD_TYPE_EQ(block_gas_limit);
MONAD_ASSERT_TX_CONTEXT_FIELD_TYPE_EQ(blob_hashes_count);
MONAD_ASSERT_TX_CONTEXT_FIELD_TYPE_EQ(initcodes_count);
MONAD_ASSERT_TX_CONTEXT_FIELD_TYPE_EQ(block_round);

#undef MONAD_ASSERT_TX_CONTEXT_FIELD_TYPE_EQ

evmc_tx_context to_evmc_tx_context(monad_tx_context const &ctx)
{
    return std::bit_cast<evmc_tx_context>(ctx);
}

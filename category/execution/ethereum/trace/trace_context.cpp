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

#include <category/core/address.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/trace/trace_context.hpp>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <span>
#include <typeindex>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

TxTraceContext::TxTraceContext(
    std::span<monad::trace::TypeErasedRunner const> const runners)
    : runners_{runners}
{
}

void TxTraceContext::dispatch(
    std::type_index const &op_type, void const *op, void *result) const
{
    for (auto &runner : runners_) {
        for (size_t i = 0; i < runner.vtable_size_; ++i) {
            auto const &entry = runner.vtable_[i];
            if (entry.tag == op_type) {
                entry.fn(op, result);
                return;
            }
        }
    }
}

size_t TxTraceContext::size() const
{
    return runners_.size();
}

BlockTraceContext::BlockTraceContext(size_t num_txs)
    : num_txs_(num_txs)
    , runners_{nullptr}
{
}

bool BlockTraceContext::can_slice(size_t n) const
{
    // We can slice the empty context infinitely many times, whereas we can only
    // slice a non-empty context as many times as there are transactions. The
    // right hand side is intentionally an equality rather than inequality,
    // because we want every transaction tracing context to be materialized.
    return !runners_ || num_txs_ == n;
}

size_t BlockTraceContext::runners_per_tx() const
{
    if (!runners_ || num_txs_ == 0) {
        return 0;
    }

    // Every transaction tracing context must have the same number of runners,
    // so we can just check the first one.
    return runners_[0].size();
}

static constexpr TxTraceContext empty_tx_trace_context{};

TxTraceContext BlockTraceContext::slice(size_t i) const
{
    if (!runners_) {
        return empty_tx_trace_context;
    }

    MONAD_ASSERT(i < num_txs_);
    return TxTraceContext{runners_[i]};
}

MONAD_NAMESPACE_END

namespace monad::trace
{
    TypeErasedRunner::TypeErasedRunner(size_t vtable_size)
        : vtable_{std::make_unique_for_overwrite<VTableEntry[]>(vtable_size)}
        , vtable_size_{vtable_size}
    {
    }
}

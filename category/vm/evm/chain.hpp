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

#include <category/vm/core/assert.h>

#include <evmc/evmc.h>

#include <concepts>

namespace monad
{
    template <evmc_revision Rev>
    struct EvmChain
    {
        static constexpr evmc_revision evm_rev() noexcept
        {
            return Rev;
        }

        // Instead of storing a revision, caches should identify revision
        // changes by storing the opaque value returned by this method. No two
        // chain specializations will return the same value, but no further
        // semantics should be associated with the return value.
        static constexpr uint64_t id() noexcept
        {
            return static_cast<uint64_t>(Rev);
        }
    };

    template <typename T>
    concept Traits = requires() {
        requires sizeof(T) == 1;
        { T::evm_rev() } -> std::same_as<evmc_revision>;
        { T::id() } -> std::same_as<uint64_t>;
    };

    // This is a temporary workaround to account for the fact that the VM
    // boundary uses EVM revisions as runtime values. When there's a continuous
    // thread of templated arguments down from execute_block, this should be
    // removed.
    constexpr uint64_t revision_to_chain_id(evmc_revision const rev) noexcept
    {
        return static_cast<uint64_t>(rev);
    }
}

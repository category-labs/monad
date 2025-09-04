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
#include <category/vm/evm/monad/revision.h>

#include <evmc/evmc.h>

#include <concepts>
#include <utility>

namespace monad
{
    template <typename T>
    concept Traits = requires() {
        requires sizeof(T) == 1;
        { T::evm_rev() } -> std::same_as<evmc_revision>;
        { T::monad_rev() } -> std::same_as<monad_revision>;

        // Feature flags
        { T::eip_7951_active() } -> std::same_as<bool>;
        { T::can_create_inside_delegated() } -> std::same_as<bool>;

        // Instead of storing a revision, caches should identify revision
        // changes by storing the opaque value returned by this method. No
        // two chain specializations will return the same value, but no
        // further semantics should be associated with the return value.
        { T::id() } -> std::same_as<uint64_t>;
    };

    template <evmc_revision Rev>
    struct EvmTraits
    {
        static constexpr evmc_revision evm_rev() noexcept
        {
            return Rev;
        }

        static constexpr monad_revision monad_rev() noexcept
        {
            static_assert(false, "Calling monad_rev() on an EVM trait type");
            std::unreachable();
        }

        static constexpr bool eip_7951_active() noexcept
        {
            return Rev >= EVMC_OSAKA;
        }

        static constexpr bool can_create_inside_delegated() noexcept
        {
            return true;
        }

        static constexpr uint64_t id() noexcept
        {
            return static_cast<uint64_t>(Rev);
        }
    };

    template <monad_revision Rev>
    struct MonadTraits
    {
        static constexpr evmc_revision evm_rev() noexcept
        {
            if constexpr (Rev >= MONAD_FOUR) {
                return EVMC_PRAGUE;
            }

            return EVMC_CANCUN;
        }

        static constexpr monad_revision monad_rev() noexcept
        {
            return Rev;
        }

        static constexpr bool eip_7951_active() noexcept
        {
            return Rev >= MONAD_FOUR;
        }

        static constexpr bool can_create_inside_delegated() noexcept
        {
            return false;
        }

        static constexpr uint64_t id() noexcept
        {
            return static_cast<uint64_t>(Rev);
        }

        // Temporary workaround that should be considered equivalent to calling
        // evm_rev(); remove when the refactoring to use feature flags is
        // complete.
        using evm_base = EvmTraits<MonadTraits::evm_rev()>;
    };
}

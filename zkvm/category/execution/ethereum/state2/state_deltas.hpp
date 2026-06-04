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

// zkVM shadow of category/execution/ethereum/state2/state_deltas.hpp.
// The host backs StorageDeltas / StateDeltas / Code with
// oneapi::tbb::concurrent_hash_map; TBB doesn't compile on RISC-V (its
// _export.h hits `#error "Unknown platform/compiler"`), and the zkVM is
// single-threaded anyway. Swap in ankerl::unordered_dense::segmented_map
// and inherit a thin shim that adds the two TBB-style overloads
// BlockState calls — find(accessor, key) and emplace(accessor, key, ...) —
// so block_state.cpp compiles unchanged. accessor aliases the base
// iterator, const_accessor aliases const_iterator; that's enough for the
// one const call site (BlockState::read_storage binds the inner
// StorageDeltas through a `const &`).

#pragma once

#include <category/core/config.hpp>

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/vm/code.hpp>

#include <ankerl/unordered_dense.h>

#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

template <class T>
using Delta = std::pair<T const, T>;

using AccountDelta = Delta<std::optional<Account>>;
using StorageDelta = Delta<bytes32_t>;

namespace detail
{
    template <class K, class V>
    class HashMapWithAccessor
        : public ankerl::unordered_dense::segmented_map<K, V>
    {
        using Base = ankerl::unordered_dense::segmented_map<K, V>;

    public:
        using Base::Base;
        using Base::emplace;
        using Base::find;
        using typename Base::const_iterator;
        using typename Base::iterator;

        using accessor = iterator;
        using const_accessor = const_iterator;

        bool find(iterator &a, K const &key)
        {
            a = Base::find(key);
            return a != Base::end();
        }

        bool find(const_iterator &a, K const &key) const
        {
            a = Base::find(key);
            return a != Base::cend();
        }

        template <class... Args>
        bool emplace(iterator &a, K const &key, Args &&...args)
        {
            auto const [it, inserted] =
                Base::emplace(key, std::forward<Args>(args)...);
            a = it;
            return inserted;
        }

        template <class... Args>
        bool emplace(const_iterator &a, K const &key, Args &&...args)
        {
            auto const [it, inserted] =
                Base::emplace(key, std::forward<Args>(args)...);
            a = it;
            return inserted;
        }
    };
}

using StorageDeltas = detail::HashMapWithAccessor<bytes32_t, StorageDelta>;

struct StateDelta
{
    AccountDelta account;
    StorageDeltas storage{};
};

using StateDeltas = detail::HashMapWithAccessor<Address, StateDelta>;

using Code = detail::HashMapWithAccessor<bytes32_t, vm::SharedIntercode>;

MONAD_NAMESPACE_END

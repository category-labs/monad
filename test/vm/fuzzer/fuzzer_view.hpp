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

#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/address.hpp>

#include <evmc/evmc.h>

#include <concepts>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <memory>
#include <ranges>
#include <span>

namespace monad::vm::fuzzing
{
    /// A single storage slot as seen during state comparison.
    /// Includes access_status so that warm/cold divergences between VMs
    /// are caught within a transaction.
    struct StorageEntry
    {
        bytes32_t key;
        bytes32_t current;
        bytes32_t original;
        evmc_access_status access_status;
    };

    /// A single transient storage slot (EIP-1153).
    struct TransientStorageEntry
    {
        bytes32_t key;
        bytes32_t value;
    };

    /// A single account as seen during state comparison.
    /// The `code` span points into the backend's own memory and is valid for
    /// the lifetime of the view that produced this entry.
    struct AccountEntry
    {
        Address addr;
        uint64_t nonce;
        uint256_t balance;
        bytes32_t code_hash;
        std::span<uint8_t const> code;
    };

    /// Virtual cursor over a sequence of entries. Each backend implements this
    /// to walk its internal data structures in canonical (sorted) order.
    template <typename T>
    class Cursor
    {
    public:
        virtual ~Cursor() = default;
        virtual bool at_end() const = 0;
        virtual T current() const = 0;
        virtual void advance() = 0;
    };

    /// Concrete C++ input iterator that wraps a virtual Cursor<T>.
    /// Move-only — each iterator exclusively owns its cursor. This is
    /// sufficient for std::views::zip over input ranges, which never
    /// copies the underlying iterators.
    template <typename T>
    class CursorIterator
    {
        std::unique_ptr<Cursor<T>> c_;

    public:
        using iterator_concept = std::input_iterator_tag;
        using value_type = T;
        using difference_type = std::ptrdiff_t;

        CursorIterator() = default;

        explicit CursorIterator(std::unique_ptr<Cursor<T>> c)
            : c_(std::move(c))
        {
        }

        T operator*() const
        {
            return c_->current();
        }

        CursorIterator &operator++()
        {
            c_->advance();
            return *this;
        }

        void operator++(int)
        {
            c_->advance();
        }

        bool operator==(std::default_sentinel_t) const
        {
            return !c_ || c_->at_end();
        }
    };

    /// Ordered view over a collection of entries, yielded in canonical order
    /// via a virtual cursor. Used for storage, transient storage, and
    /// potentially other sorted key-value collections.
    template <typename T>
    class SortedView
    {
    protected:
        virtual std::unique_ptr<Cursor<T>> cursor() const = 0;

    public:
        virtual ~SortedView() = default;
        virtual size_t size() const = 0;

        CursorIterator<T> begin() const
        {
            return CursorIterator<T>(cursor());
        }

        std::default_sentinel_t end() const
        {
            return {};
        }
    };

    using SortedStorageView = SortedView<StorageEntry>;
    using SortedTransientStorageView = SortedView<TransientStorageEntry>;

    /// Ordered view over the accounts in a backend's state.
    /// Accounts are yielded in canonical order (lexicographic by address).
    /// Storage for each account is accessible via storage() and
    /// transient_storage().
    class SortedStateView
    {
    protected:
        virtual std::unique_ptr<Cursor<AccountEntry>> cursor() const = 0;

    public:
        virtual ~SortedStateView() = default;
        virtual size_t size() const = 0;
        virtual std::unique_ptr<SortedStorageView>
        storage(Address const &) const = 0;
        virtual std::unique_ptr<SortedTransientStorageView>
        transient_storage(Address const &) const = 0;

        CursorIterator<AccountEntry> begin() const
        {
            return CursorIterator<AccountEntry>(cursor());
        }

        std::default_sentinel_t end() const
        {
            return {};
        }
    };

    static_assert(std::input_iterator<CursorIterator<StorageEntry>>);
    static_assert(std::input_iterator<CursorIterator<TransientStorageEntry>>);
    static_assert(std::input_iterator<CursorIterator<AccountEntry>>);
    static_assert(std::ranges::input_range<SortedStorageView>);
    static_assert(std::ranges::input_range<SortedTransientStorageView>);
    static_assert(std::ranges::input_range<SortedStateView>);
    static_assert(!std::copyable<CursorIterator<StorageEntry>>);
    static_assert(!std::copyable<CursorIterator<TransientStorageEntry>>);
    static_assert(!std::copyable<CursorIterator<AccountEntry>>);
}

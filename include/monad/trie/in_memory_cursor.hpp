#pragma once

#include "evmc/evmc.hpp"

#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/trie/comparator.hpp>
#include <monad/trie/config.hpp>
#include <monad/trie/key_buffer.hpp>

#include <tl/optional.hpp>

#include <algorithm>
#include <cassert>
#include <unordered_map>

MONAD_TRIE_NAMESPACE_BEGIN

// Per-snapshot and prefix
template <comparator TComparator>
struct InMemoryCursor
{
    using element_t = std::pair<byte_string, byte_string>;
    using storage_t = std::vector<element_t>;
    using iterator_t = std::vector<element_t>::const_iterator;

    storage_t const &storage_;
    iterator_t it_;

    mutable KeyBuffer buf_;

    struct Key
    {
        bool has_prefix;
        byte_string raw;

        [[nodiscard]] constexpr bool operator==(Key const &) const = default;

        [[nodiscard]] constexpr Nibbles path() const
        {
            assert(!has_prefix || raw.size() > sizeof(address_t));
            return deserialize_nibbles(
                       has_prefix ? raw.substr(sizeof(address_t)) : raw)
                .first;
        }

        [[nodiscard]] constexpr bool path_empty() const
        {
            assert(!has_prefix || raw.size() > sizeof(address_t));
            return (has_prefix ? raw[sizeof(address_t)] : raw[0]) == 0;
        }
    };

    constexpr explicit InMemoryCursor(std::vector<element_t> const &storage)
        : storage_(storage)
        , it_(storage_.end())
    {
    }

    [[nodiscard]] tl::optional<Key> key() const
    {
        return valid() ? tl::make_optional(
                             Key{.has_prefix = (buf_.prefix_size > 0),
                                 .raw = it_->first})
                       : tl::nullopt;
    }

    [[nodiscard]] tl::optional<byte_string> value() const
    {
        return valid() ? tl::make_optional(it_->second) : tl::nullopt;
    }

    constexpr void prev()
    {
        if (it_ > storage_.begin()) {
            std::advance(it_, -1);
        }
        else {
            it_ = storage_.end();
        }
    }

    constexpr void next()
    {
        if (it_ < storage_.end()) {
            std::advance(it_, 1);
        }
        else {
            it_ = storage_.begin();
            MONAD_ASSERT(valid());
        }
    }

    constexpr void lower_bound(
        Nibbles const &key, tl::optional<Key> const & /*first*/ = tl::nullopt,
        tl::optional<Key> const & /*last */ = tl::nullopt)
    {
        serialize_nibbles(buf_, key);
        it_ = std::ranges::lower_bound(
            storage_, buf_.view(), TComparator{}, &element_t::first);
    }

    [[nodiscard]] constexpr bool valid() const { return is_it_valid(it_); }

    [[nodiscard]] constexpr bool empty() const
    {
        serialize_nibbles(buf_, Nibbles{});
        return !is_it_valid(std::ranges::lower_bound(
            storage_, buf_.view(), TComparator{}, &element_t::first));
    }

    constexpr void set_prefix(address_t const &address)
    {
        buf_.set_prefix(address);
    }

    constexpr void take_snapshot() const noexcept {};
    constexpr void release_snapshots() const noexcept {};

    [[nodiscard]] constexpr bool is_it_valid(iterator_t it) const
    {
        return it < storage_.end() && it->first.starts_with(buf_.prefix());
    }
};

MONAD_TRIE_NAMESPACE_END

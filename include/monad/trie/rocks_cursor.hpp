#pragma once

#include "evmc/evmc.hpp"
#include <bits/iterator_concepts.h>
#include <cstring>
#include <iterator>

#include <monad/core/assert.h>
#include <monad/core/variant.hpp>

#include <monad/trie/assert.h>
#include <monad/trie/key_buffer.hpp>
#include <monad/trie/nibbles.hpp>
#include <monad/trie/util.hpp>

#include <rocksdb/comparator.h>
#include <rocksdb/db.h>
#include <rocksdb/options.h>

#include <tl/optional.hpp>

#include <filesystem>
#include <type_traits>

MONAD_TRIE_NAMESPACE_BEGIN

// Per-snapshot and prefix
class RocksCursor
{
private:
    std::shared_ptr<rocksdb::DB> const db_;

    byte_string lower_;
    byte_string upper_;
    rocksdb::Slice lower_slice_;
    rocksdb::Slice upper_slice_;
    std::unique_ptr<rocksdb::Iterator> it_;
    rocksdb::ColumnFamilyHandle *cf_; // non-owning
    rocksdb::ReadOptions read_opts_;
    mutable KeyBuffer buf_;

public:
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

    RocksCursor(std::shared_ptr<rocksdb::DB>, rocksdb::ColumnFamilyHandle *);

    tl::optional<Key> key() const;
    tl::optional<byte_string> value() const;

    void prev();
    void next();
    void lower_bound(
        Nibbles const &key, tl::optional<Key> const &first = tl::nullopt,
        tl::optional<Key> const &last = tl::nullopt);

    [[nodiscard]] bool valid() const;
    [[nodiscard]] bool empty();
    void take_snapshot();
    void set_prefix(address_t const &);
    void release_snapshots();
};

Nibbles deserialize_nibbles(rocksdb::Slice);

MONAD_TRIE_NAMESPACE_END

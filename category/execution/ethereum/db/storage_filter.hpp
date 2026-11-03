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

#pragma once

#include <category/core/blocked_bloom_filter.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/crypto/hash256.h>
#include <category/mpt/node.hpp>

#include <atomic>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <memory>
#include <optional>

MONAD_NAMESPACE_BEGIN

namespace mpt
{
    class Db;
}

// Identifies the trie state a storage filter is complete for: the finalized
// state of `block_number`, whose state root is `state_root`, on a db whose
// storage is page-encoded or not.
struct StorageFilterTag
{
    uint64_t block_number;
    bytes32_t state_root;
    bool page_encoded;

    bool operator==(StorageFilterTag const &) const = default;
};

// Membership filter over the storage leaves of the state trie. A negative
// answer proves that a leaf does not exist, so a read that misses the cache
// can skip the trie find. On a slot-encoded (Ethereum) db a leaf is one
// storage slot; on a page-encoded (Monad, MIP-8) db it is one page of slots.
// Either way the filter is keyed by the leaf's trie path, keccak(address) and
// keccak(lookup key), which a read computes for the find anyway.
//
// Keys are only ever added: a leaf that is deleted stays a false positive
// until the filter is rebuilt, which costs a trie find, as without the
// filter. The filter is complete (has no false negatives) for every trie
// version from the one it was built from, provided every block committed
// since then was inserted; TrieDb::commit inserts into the filter attached to
// it. Queries must not be answered before the filter is ready.
class StorageFilter final
{
    BlockedBloomFilter bloom_;
    bool const page_encoded_;
    uint64_t const base_block_number_;
    std::atomic<bool> ready_{false};

public:
    struct Config
    {
        size_t size_bytes; // rounded down to whole 64-byte blocks
        unsigned num_probes; // per key, within one block
    };

    // Monad (page-encoded): ~180M pages at block 110M; 512 MiB is ~23 bits
    // per page and leaves room to grow. Ethereum (slot-encoded): ~1.65B slots
    // at block 26M; 2 GiB is ~10 bits per slot.
    static Config default_config(bool page_encoded) noexcept;

    // A filter for the finalized state of `base_block_number` and later
    // versions; empty until it is built or loaded.
    StorageFilter(
        Config const &, bool page_encoded, uint64_t base_block_number);

    bool is_page_encoded() const noexcept
    {
        return page_encoded_;
    }

    // Versions before this one may have leaves the filter never saw.
    uint64_t base_block_number() const noexcept
    {
        return base_block_number_;
    }

    // The filter is ready once it holds every leaf of the state it was built
    // from; publishes the inserts that happened before.
    bool is_ready() const noexcept
    {
        return ready_.load(std::memory_order_acquire);
    }

    void set_ready() noexcept
    {
        ready_.store(true, std::memory_order_release);
    }

    void insert(
        monad_hash256 const &address_hash,
        monad_hash256 const &key_hash) noexcept;

    bool may_contain(
        monad_hash256 const &address_hash,
        monad_hash256 const &key_hash) const noexcept;

    BlockedBloomFilter const &bloom() const noexcept
    {
        return bloom_;
    }

    // Writes the filter to `path` atomically (a temporary file renamed over
    // it); false, with the reason logged, if it could not. Inserts may run
    // concurrently; the file holds every key inserted before the call, so it
    // is complete for `tag` if the filter is complete for `tag` at the call.
    bool save(std::filesystem::path const &, StorageFilterTag const &) const;

    // Loads a filter saved for exactly `expected`, with the given size and
    // probes; nullptr (with the reason logged) if the file is missing, was
    // saved for another state or configuration, or is damaged. The returned
    // filter is ready.
    static std::unique_ptr<StorageFilter> load(
        std::filesystem::path const &, StorageFilterTag const &expected,
        Config const &);
};

// The tag of the finalized state of `block_number` in `db` (whose storage
// encoding is `page_encoded`), given the root of that version, or nullopt if
// that state is not in the db.
std::optional<StorageFilterTag> finalized_storage_filter_tag(
    mpt::Db &, mpt::Node::SharedPtr const &root, uint64_t block_number,
    bool page_encoded);

// The same for an on-disk db, which loads the root of `block_number`.
std::optional<StorageFilterTag> finalized_storage_filter_tag(
    mpt::Db &, uint64_t block_number, bool page_encoded);

// Inserts every storage leaf of the finalized state of `block_number` in
// `db`, given the root of that version, visiting only the subtries of the
// state trie whose first and second nibbles are set in `first_nibbles` and
// `second_nibbles`. Stops early when `stop` is set. Returns the number of
// leaves inserted, or nullopt if the traversal did not complete.
std::optional<uint64_t> insert_storage_leaves(
    StorageFilter &, mpt::Db &, mpt::Node::SharedPtr const &root,
    uint64_t block_number, uint16_t first_nibbles = 0xffff,
    uint16_t second_nibbles = 0xffff, size_t concurrency_limit = 4096,
    std::atomic<bool> const *stop = nullptr);

// Inserts every storage leaf of the finalized state of `block_number` of the
// on-disk db at `dbname_path`, with `num_threads` read-only handles that
// share out the state trie. Same result as insert_storage_leaves.
std::optional<uint64_t> build_storage_filter(
    StorageFilter &, std::filesystem::path const &dbname_path,
    uint64_t block_number, unsigned num_threads,
    std::atomic<bool> const *stop = nullptr);

MONAD_NAMESPACE_END

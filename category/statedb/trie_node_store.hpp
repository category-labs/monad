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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/bytes_hash_compare.hpp>
#include <category/core/config.hpp>
#include <category/core/lru/lru_cache.hpp>
#include <category/statedb/kv_store.hpp>

#include <cstddef>
#include <optional>

MONAD_NAMESPACE_BEGIN

namespace statedb
{
    // Per-value framing for CF_TRIE_NODES: [version][prune_epoch][node
    // bytes...]. The version byte lets the stored node format evolve; the
    // prune-epoch byte is reserved for mark-and-sweep pruning (F13) and is
    // written keep-all (0) for now. Distinct from schema.hpp's DB-wide
    // SCHEMA_VERSION.
    inline constexpr unsigned char TRIE_NODE_FORMAT_VERSION = 1;
    inline constexpr unsigned char TRIE_NODE_PRUNE_EPOCH_KEEP_ALL = 0;
    inline constexpr std::size_t TRIE_NODE_HEADER_SIZE = 2;

    // A node_hash-keyed store for trie nodes, backed by CF_TRIE_NODES and
    // fronted by an in-memory hash-keyed LRU. Nodes are opaque bytes here:
    // their RLP codec lives in the ethereum-side caller (PartialTrieDb's codec,
    // applied in F7), and node_hash is keccak256 of those bytes.
    //
    // The cache reuses DbCache's LruCache (concurrent tbb map + a
    // time-throttled LRU list that re-orders at most ~once/sec/node), rather
    // than the offset-keyed mpt::NodeCache's static_lru_cache, which re-orders
    // on every hit and isn't thread-safe. The RocksDbDb read path is
    // concurrent, so the concurrent + lazy-LRU impl fits better (the
    // offset-keyed NodeCache is untouched). Bound is entry-count for now;
    // byte-bounding can be layered on later. Borrows the KvStore (the RocksDbDb
    // owns one KvStore across all CFs).
    class TrieNodeStore
    {
    public:
        TrieNodeStore(KvStore &, std::size_t lru_capacity);

        // The opaque node bytes for `node_hash`, or nullopt if absent. Serves
        // from the LRU, else reads CF_TRIE_NODES and warms the LRU.
        std::optional<byte_string> get(bytes32_t const &node_hash);

        // Persist a node's opaque bytes under its node_hash (its own WAL
        // write).
        void put(bytes32_t const &node_hash, byte_string_view node_bytes);

        // Stage a node into a cross-CF WriteBatch (for the atomic per-block
        // commit in F9/F10); also warms the LRU.
        void batch_put(
            rocksdb::WriteBatch &, bytes32_t const &node_hash,
            byte_string_view node_bytes);

    private:
        using Cache =
            LruCache<bytes32_t, byte_string, BytesHashCompare<bytes32_t>>;

        KvStore &kv_;
        Cache cache_;
    };
}

MONAD_NAMESPACE_END

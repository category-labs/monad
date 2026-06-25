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
#include <category/core/config.hpp>
#include <category/core/lru/lru_cache.hpp>
#include <category/statedb/kv_store.hpp>

#include <komihash.h>

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

    // A trie-path-keyed store for trie nodes, backed by CF_TRIE_NODES and
    // fronted by an in-memory LRU. Nodes are opaque bytes here: both the RLP
    // codec and the path-key construction live in the ethereum-side caller
    // (RocksDbDb). Keying by path (rather than keccak of the node) means a
    // changed node overwrites its own key instead of inserting a new one --
    // no orphaned versions, and writes/reads stay in trie order.
    //
    // The cache reuses DbCache's LruCache (concurrent tbb map + a
    // time-throttled LRU list that re-orders at most ~once/sec/node), rather
    // than the offset-keyed mpt::NodeCache's static_lru_cache, which re-orders
    // on every hit and isn't thread-safe. The RocksDbDb read path is
    // concurrent, so the concurrent + lazy-LRU impl fits better (the
    // offset-keyed NodeCache is untouched). Bound is entry-count for now;
    // byte-bounding can be layered on later. Borrows the KvStore (the RocksDbDb
    // owns one KvStore across all CFs).
    // Hash/compare for variable-length byte_string LRU keys (BytesHashCompare
    // only handles fixed `.bytes` types like bytes32_t).
    struct ByteStringHashCompare
    {
        std::size_t hash(byte_string const &a) const
        {
            return komihash(a.data(), a.size(), 0);
        }

        bool equal(byte_string const &a, byte_string const &b) const
        {
            return a == b;
        }
    };

    class TrieNodeStore
    {
    public:
        TrieNodeStore(KvStore &, std::size_t lru_capacity);

        // The opaque node bytes for the trie-path `key`, or nullopt if absent.
        // Serves from the LRU, else reads CF_TRIE_NODES and warms the LRU.
        std::optional<byte_string> get(byte_string_view key);

        // Persist a node's opaque bytes under its trie-path `key` (its own WAL
        // write). A changed node keeps the same key, so it overwrites in place.
        void put(byte_string_view key, byte_string_view node_bytes);

        // Stage a node into a cross-CF WriteBatch (for the atomic per-block
        // commit); also warms the LRU.
        void batch_put(
            rocksdb::WriteBatch &, byte_string_view key,
            byte_string_view node_bytes);

    private:
        using Cache = LruCache<byte_string, byte_string, ByteStringHashCompare>;

        KvStore &kv_;
        Cache cache_;
    };
}

MONAD_NAMESPACE_END

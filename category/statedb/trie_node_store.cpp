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

#include <category/core/assert.h>
#include <category/statedb/schema.hpp>
#include <category/statedb/trie_node_store.hpp>

MONAD_NAMESPACE_BEGIN

namespace statedb
{
    namespace
    {
        byte_string frame(byte_string_view const node_bytes)
        {
            byte_string out;
            out.reserve(TRIE_NODE_HEADER_SIZE + node_bytes.size());
            out.push_back(TRIE_NODE_FORMAT_VERSION);
            out.push_back(TRIE_NODE_PRUNE_EPOCH_KEEP_ALL);
            out.append(node_bytes.data(), node_bytes.size());
            return out;
        }
    }

    TrieNodeStore::TrieNodeStore(KvStore &kv, std::size_t const lru_capacity)
        : kv_{kv}
        , cache_{lru_capacity}
    {
    }

    std::optional<byte_string> TrieNodeStore::get(bytes32_t const &node_hash)
    {
        {
            Cache::ConstAccessor acc;
            if (cache_.find(acc, node_hash)) {
                return byte_string{acc->second.value_};
            }
        }
        auto const framed = kv_.get(Cf::trie_nodes, node_hash);
        if (!framed.has_value()) {
            return std::nullopt;
        }
        MONAD_ASSERT(framed->size() >= TRIE_NODE_HEADER_SIZE);
        MONAD_ASSERT((*framed)[0] == TRIE_NODE_FORMAT_VERSION);
        byte_string body{
            framed->data() + TRIE_NODE_HEADER_SIZE,
            framed->size() - TRIE_NODE_HEADER_SIZE};
        cache_.insert(node_hash, body);
        return body;
    }

    void TrieNodeStore::put(
        bytes32_t const &node_hash, byte_string_view const node_bytes)
    {
        kv_.put(Cf::trie_nodes, node_hash, frame(node_bytes));
        cache_.insert(node_hash, byte_string{node_bytes});
    }

    void TrieNodeStore::batch_put(
        rocksdb::WriteBatch &batch, bytes32_t const &node_hash,
        byte_string_view const node_bytes)
    {
        kv_.batch_put(batch, Cf::trie_nodes, node_hash, frame(node_bytes));
        cache_.insert(node_hash, byte_string{node_bytes});
    }
}

MONAD_NAMESPACE_END

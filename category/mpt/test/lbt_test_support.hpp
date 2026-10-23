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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/mpt/lbt/commit.hpp>
#include <category/mpt/lbt/compute.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>

#include <cstddef>
#include <iterator>
#include <map>

namespace monad::test
{
    // The binary trie over 32-byte keys, its root computed bit by bit from
    // the sorted leaves with no grouping into nodes. A correctness oracle
    // for LbtCompute.
    class ReferenceTrie
    {
    public:
        void upsert(bytes32_t const &key, bytes32_t const &value)
        {
            leaves_[key] = value;
        }

        void erase(bytes32_t const &key)
        {
            MONAD_ASSERT(leaves_.erase(key) == 1);
        }

        size_t size() const
        {
            return leaves_.size();
        }

        // 32 zero bytes when empty.
        bytes32_t root() const
        {
            if (leaves_.empty()) {
                return bytes32_t{};
            }
            return subtree(leaves_.begin(), leaves_.end(), 0).hash();
        }

    private:
        using iterator = std::map<bytes32_t, bytes32_t>::const_iterator;

        static bool key_bit(bytes32_t const &key, unsigned const i)
        {
            return ((key.bytes[i / 8] >> (7 - i % 8)) & 1) != 0;
        }

        // [lo, hi) share their first `bit` key bits.
        static mpt::lbt::Commitment
        subtree(iterator const lo, iterator const hi, unsigned const bit)
        {
            if (std::next(lo) == hi) {
                return mpt::lbt::commit_leaf(
                    mpt::NibblesView{lo->first}, lo->second);
            }
            auto mid = lo;
            while (mid != hi && !key_bit(mid->first, bit)) {
                ++mid;
            }
            if (mid == hi || mid == lo) {
                return mpt::lbt::merge_one_sided(
                    subtree(lo, hi, bit + 1), mid == lo);
            }
            return mpt::lbt::merge(
                subtree(lo, mid, bit + 1), subtree(mid, hi, bit + 1));
        }

        // Sorted by bytes, which is key-bit order.
        std::map<bytes32_t, bytes32_t> leaves_;
    };

    // A 32-byte value is committed as is; anything else is hashed first.
    inline bytes32_t leaf_value(byte_string_view const value)
    {
        if (value.size() != sizeof(bytes32_t)) {
            return mpt::lbt::value_hash(value);
        }
        return to_bytes(value);
    }

    struct RawValueHasher
    {
        static bytes32_t hash(mpt::Node const &node)
        {
            return leaf_value(node.value());
        }
    };

    // The root of a trie built by the raw upsert() with no Db wrapper; a
    // lone leaf is its own root.
    inline bytes32_t trie_root(mpt::Node const *const root)
    {
        if (root == nullptr) {
            return bytes32_t{};
        }
        return mpt::lbt::commit_node<RawValueHasher>(*root, {}).hash();
    }

    // The root of an mpt::Db, whose empty-path root node keeps the
    // commitment over its children in its own data.
    inline bytes32_t db_root_commitment(mpt::Node const *const root)
    {
        if (root == nullptr || root->mask == 0) {
            return bytes32_t{};
        }
        MONAD_ASSERT(root->data().size() == sizeof(bytes32_t));
        return to_bytes(root->data());
    }
}

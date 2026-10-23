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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <cstdint>
#include <span>

MONAD_MPT_NAMESPACE_BEGIN

// The binary trie over key bits, in the style of EIP-7864: a lone leaf rises
// to its shortest unique prefix and a lone internal node is hashed against a
// zero sibling. Leaves commit their full key, so no commitment depends on how
// the engine groups key bits into nodes.
namespace lbt
{
    inline constexpr unsigned KEY_NIBBLES = 64;

    // A node's hash and whether the node is a leaf. A parent needs the type
    // because a lone leaf rises while a lone internal node is hashed; the
    // engine records it beside the child's hash (Node::child_value_mask), so
    // it never enters the hash.
    class Commitment
    {
    public:
        // 32 zero bytes, internal; only array storage needs it.
        constexpr Commitment() noexcept = default;

        static constexpr Commitment leaf(bytes32_t const &h) noexcept
        {
            return Commitment{h, true};
        }

        static constexpr Commitment internal(bytes32_t const &h) noexcept
        {
            return Commitment{h, false};
        }

        static Commitment from_child_data(byte_string_view data, bool is_leaf);

        constexpr bool is_leaf() const noexcept
        {
            return leaf_;
        }

        constexpr bytes32_t const &hash() const noexcept
        {
            return hash_;
        }

        friend constexpr bool
        operator==(Commitment const &, Commitment const &) = default;

    private:
        constexpr Commitment(bytes32_t const &h, bool const leaf) noexcept
            : hash_{h}
            , leaf_{leaf}
        {
        }

        bytes32_t hash_{};
        bool leaf_{false};
    };

    struct Entry
    {
        uint16_t index;
        Commitment child;
    };

    Commitment merge(Commitment const &left, Commitment const &right);

    // An internal node whose only child, internal itself, is merged with a
    // zero sibling.
    Commitment merge_one_sided(Commitment const &child, bool child_is_right);

    Commitment commit_leaf(NibblesView key, bytes32_t const &value);

    // The slice of the binary trie spanned by one branch's index bits.
    // entries: non-empty, strictly ascending by index, index < 2^IndexBits.
    template <unsigned IndexBits>
        requires(IndexBits >= 1 && IndexBits <= 8)
    Commitment branch_commit(std::span<Entry const> entries);

    // An internal node reached through a compressed path: one one-sided
    // merge per path bit.
    Commitment commit_path(NibblesView path, Commitment const &node);

    bytes32_t value_hash(byte_string_view value);

    // The raw hashes, pinned by tests.
    namespace detail
    {
        bytes32_t merge_hash(bytes32_t const &left, bytes32_t const &right);

        // The key's nibble count is bound through the compression counter.
        bytes32_t leaf_commit(NibblesView key, bytes32_t const &value);
    }
}

MONAD_MPT_NAMESPACE_END

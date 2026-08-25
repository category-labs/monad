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
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/mpt/nibbles_view.hpp>

#ifdef MONAD_ZKVM_KECCAK_SITES
    #include <category/core/keccak_sites.hpp>
#endif

#include <algorithm>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <ranges>
#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace detail
{
    struct Item
    {
        unsigned char key[1 + sizeof(size_t)];
        uint8_t key_len;
        byte_string_view val;

        Item(size_t const index, byte_string_view const value)
            : val{value}
        {
            auto const remaining = rlp::encode_unsigned(key, index);
            key_len = static_cast<uint8_t>(sizeof(key) - remaining.size());
        }

        mpt::NibblesView nib() const
        {
            return mpt::NibblesView{byte_string_view{key, key_len}};
        }
    };

    // Write the inline node RLP (<32 bytes) or its raw keccak (32 bytes) into
    // ref_dest's tail and return the number of bytes written. A 32-byte
    // result is a hash: the caller prepends the RLP string header itself.
    // Only leaf encoding needs a dynamically sized buffer.
    size_t node_ref(
        std::vector<Item> const &items, size_t lo, size_t hi, unsigned depth,
        std::span<unsigned char, KECCAK256_SIZE> ref_dest);
}

// Root of an Ethereum ordered trie: item i stored under key rlp(i). used for
// computing the root hash for transactions, receipts and withdrawals inside a
// block.
template <std::ranges::random_access_range R>
    requires std::convertible_to<
        std::ranges::range_reference_t<R const>, byte_string_view>
bytes32_t ordered_trie_root(R const &items)
{
    size_t const n = std::ranges::size(items);
    if (n == 0) {
        return NULL_ROOT;
    }
    using detail::Item;
    std::vector<Item> it;
    it.reserve(n);
    // RLP keys sort as 1..127, 0, 128 onwards: zero encodes as 0x80,
    // followed by length-prefixed big-endian integers in numeric order.
    for (size_t i = 1; i < std::min(n, size_t{128}); ++i) {
        it.emplace_back(i, items[i]);
    }
    it.emplace_back(0, items[0]);
    for (size_t i = 128; i < n; ++i) {
        it.emplace_back(i, items[i]);
    }
    bytes32_t root;
    size_t const ref_len = detail::node_ref(it, 0, it.size(), 0, root.bytes);
    if (MONAD_LIKELY(ref_len == sizeof(root.bytes))) {
        return root;
    }
    // The root is always hashed, even when its RLP is short enough to inline.
#ifdef MONAD_ZKVM_KECCAK_SITES
    MONAD_KECCAK_SITE(BODY_ROOTS, ref_len);
#endif
    return to_bytes(
        keccak256({root.bytes + sizeof(root.bytes) - ref_len, ref_len}));
}

MONAD_NAMESPACE_END

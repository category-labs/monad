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

#include <category/execution/ethereum/db/ordered_trie.hpp>

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/core/rlp/encode.hpp>
#include <category/crypto/keccak.h>
#include <category/execution/ethereum/db/offset_trie.hpp>
#include <category/mpt/merkle/compact_encode.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <algorithm>
#include <cstddef>
#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace detail
{
    // Items [lo, hi) are sorted by nibble sequence. RLP integer keys are
    // prefix-free, so branch value slots are always empty.
    size_t node_ref(
        std::vector<Item> const &it, size_t const lo, size_t const hi,
        unsigned const depth,
        std::span<unsigned char, KECCAK256_SIZE> const ref_dest)
    {
        auto const compute_ref = [&](byte_string_view const node) {
            size_t const size = std::min(node.size(), KECCAK256_SIZE);
            if (node.size() < KECCAK256_SIZE) {
                std::copy(node.begin(), node.end(), ref_dest.last(size).data());
            }
            else {
#ifdef MONAD_ZKVM_KECCAK_SITES
                MONAD_KECCAK_SITE(BODY_ROOTS, node.size());
#endif
                monad_keccak256(node.data(), node.size(), ref_dest.data());
            }
            return size;
        };

        if (hi - lo == 1) {
            auto const path = it[lo].nib().substr(depth);
            size_t const path_len = path.nibble_size() / 2 + 1;
            size_t const payload_len =
                path_len + (path_len > 1) + rlp::string_length(it[lo].val);
            size_t const node_len = rlp::list_length(payload_len);

            byte_string node;
            node.resize_and_overwrite(
                node_len, [&](unsigned char *const data, size_t) {
                    auto out = rlp::encode_list_prefix(
                        std::span{data, node_len}, payload_len);
                    // path_len <= sizeof(Item::key) + 1, always a short RLP
                    // string.
                    static_assert(sizeof(detail::Item::key) + 1 <= 55);
                    if (path_len > 1) {
                        out[0] = static_cast<unsigned char>(0x80 + path_len);
                        out = out.subspan(1);
                    }
                    mpt::compact_encode_raw(out.data(), path, true);
                    out = rlp::encode_string(out.subspan(path_len), it[lo].val);
                    MONAD_ASSERT(out.empty());
                    return node_len;
                });
            return compute_ref(node);
        }

        // Sixteen hash references, an empty value, and the list header.
        constexpr size_t max_node_rlp = rlp::list_length(16 * 33 + 1);
        unsigned char buffer[max_node_rlp];
        mpt::node_rlp_span<max_node_rlp> payload{buffer};
        // A hashed child comes back as 32 raw bytes and needs the RLP string
        // header; an inline child is already its own RLP.
        auto const prepend_child =
            [&](size_t const lo, size_t const hi, unsigned const depth) {
                size_t const len = node_ref(
                    it,
                    lo,
                    hi,
                    depth,
                    std::span<unsigned char, KECCAK256_SIZE>{
                        payload.last(KECCAK256_SIZE)});
                payload = payload.shrink(len);
                if (len == 32) {
                    payload.back() = 0x80 + 32;
                    payload = payload.shrink(1);
                }
            };
        unsigned prefix = depth;
        // Since the list is sorted by nibbles, if the first and last
        // element have a common prefix, then so do all the items between
        while (it[lo].nib().get(prefix) == it[hi - 1].nib().get(prefix)) {
            ++prefix;
        }
        if (prefix > depth) {
            prepend_child(lo, hi, prefix);
            auto const path = it[lo].nib().substr(depth, prefix - depth);
            size_t const len = path.nibble_size() / 2 + 1;
            mpt::compact_encode_raw(payload.last(len).data(), path, false);
            payload = payload.shrink(len);
            if (len > 1) {
                payload.back() = static_cast<unsigned char>(0x80 + len);
                payload = payload.shrink(1);
            }
        }
        else {
            payload.back() = 0x80; // empty branch value
            payload = payload.shrink(1);
            // Emit rightmost children first because the buffer grows backwards.
            size_t k = hi;
            for (unsigned nb = 16; nb != 0; --nb) {
                size_t const end = k;
                while (k > lo && it[k - 1].nib().get(depth) == nb - 1) {
                    --k;
                }
                if (k == end) {
                    payload.back() = 0x80;
                    payload = payload.shrink(1);
                }
                else {
                    prepend_child(k, end, depth + 1);
                }
            }
        }

        size_t const payload_len = payload.rlp_size();
        size_t const hdr_len = rlp::list_length(payload_len) - payload_len;
        rlp::encode_list_prefix_compact(payload.last(hdr_len), payload_len);
        payload = payload.shrink(hdr_len);
        return compute_ref({payload.rlp_data(), payload.rlp_size()});
    }
}

MONAD_NAMESPACE_END

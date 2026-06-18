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

#include <category/core/assert.h>
#include <category/core/rlp/encode.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/execution_witness.hpp>

#include <boost/outcome/try.hpp>

#include <algorithm>
#include <cstring>
#include <vector>

MONAD_NAMESPACE_BEGIN

Result<ExecutionWitness> parse_execution_witness(byte_string_view witness_bytes)
{
    byte_string_view view{witness_bytes.data(), witness_bytes.size()};

    // Strip the outer RLP list envelope.
    BOOST_OUTCOME_TRY(auto outer, rlp::parse_list_metadata(view));

    // No bytes may follow the outer list.
    if (MONAD_UNLIKELY(!view.empty())) {
        return rlp::DecodeError::InputTooLong;
    }

    ExecutionWitness w{};

    BOOST_OUTCOME_TRY(w.block_rlp, rlp::parse_string_metadata(outer));
    BOOST_OUTCOME_TRY(w.encoded_nodes, rlp::parse_list_metadata(outer));
    BOOST_OUTCOME_TRY(w.encoded_codes, rlp::parse_list_metadata(outer));
    BOOST_OUTCOME_TRY(w.encoded_headers, rlp::parse_list_metadata(outer));
    BOOST_OUTCOME_TRY(
        w.encoded_parent_senders_and_authorities,
        rlp::parse_list_metadata(outer));
    BOOST_OUTCOME_TRY(
        w.encoded_grandparent_senders_and_authorities,
        rlp::parse_list_metadata(outer));

    if (MONAD_UNLIKELY(!outer.empty())) {
        return rlp::DecodeError::InputTooLong;
    }

    return w;
}

byte_string encode_execution_witness(
    byte_string_view const block_rlp, std::span<byte_string const> const nodes,
    std::span<byte_string const> const codes,
    std::span<byte_string const> const headers,
    ankerl::unordered_dense::segmented_set<Address> const
        *const parent_senders_and_authorities,
    ankerl::unordered_dense::segmented_set<Address> const
        *const grandparent_senders_and_authorities)
{
    // 20-byte address → 1-byte length prefix (0x94) + 20 payload bytes.
    static_assert(sizeof(Address) == 20);
    constexpr size_t addr_string_size = 1 + sizeof(Address);

    // Pre-calc: payload size of every nested list, then total output size.
    size_t nodes_payload = 0;
    for (auto const &n : nodes) {
        nodes_payload += n.size();
    }
    size_t codes_payload = 0;
    for (auto const &c : codes) {
        codes_payload += rlp::string_length(c);
    }
    size_t headers_payload = 0;
    for (auto const &h : headers) {
        headers_payload += rlp::string_length(h);
    }
    size_t const parent_payload =
        parent_senders_and_authorities
            ? parent_senders_and_authorities->size() * addr_string_size
            : 0;
    size_t const grandparent_payload =
        grandparent_senders_and_authorities
            ? grandparent_senders_and_authorities->size() * addr_string_size
            : 0;

    size_t const outer_payload =
        rlp::string_length(block_rlp) + rlp::list_length(nodes_payload) +
        rlp::list_length(codes_payload) + rlp::list_length(headers_payload) +
        rlp::list_length(parent_payload) +
        rlp::list_length(grandparent_payload);

    byte_string result;
    result.resize_and_overwrite(
        rlp::list_length(outer_payload),
        [](auto *, size_t const count) { return count; });
    std::span<unsigned char> d{result};

    // Outer 6-field list
    d = rlp::encode_list_prefix(d, outer_payload);

    // [0] block_rlp wrapped as RLP string
    d = rlp::encode_string(d, block_rlp);

    // [1] nodes — each entry is itself a complete RLP list, concatenated raw
    d = rlp::encode_list_prefix(d, nodes_payload);
    for (auto const &n : nodes) {
        std::memcpy(d.data(), n.data(), n.size());
        d = d.subspan(n.size());
    }

    // [2] codes — each raw bytecode wrapped as RLP string
    d = rlp::encode_list_prefix(d, codes_payload);
    for (auto const &c : codes) {
        d = rlp::encode_string(d, c);
    }

    // [3] headers — each pre-encoded header wrapped as RLP string
    d = rlp::encode_list_prefix(d, headers_payload);
    for (auto const &h : headers) {
        d = rlp::encode_string(d, h);
    }

    // segmented_set has no defined iteration order, so emit addresses in
    // sorted order to keep the encoding deterministic across runs.
    auto const encode_addresses =
        [](std::span<unsigned char> d,
           ankerl::unordered_dense::segmented_set<Address> const *const set) {
            if (!set) {
                return d;
            }
            std::vector<Address> sorted(set->begin(), set->end());
            std::sort(sorted.begin(), sorted.end());
            for (auto const &a : sorted) {
                d = rlp::encode_string(d, to_byte_string_view(a.bytes));
            }
            return d;
        };

    // [4] parent senders and authorities — list of address strings
    d = rlp::encode_list_prefix(d, parent_payload);
    d = encode_addresses(d, parent_senders_and_authorities);

    // [5] grandparent senders and authorities
    d = rlp::encode_list_prefix(d, grandparent_payload);
    d = encode_addresses(d, grandparent_senders_and_authorities);

    MONAD_ASSERT(d.empty());
    return result;
}

MONAD_NAMESPACE_END

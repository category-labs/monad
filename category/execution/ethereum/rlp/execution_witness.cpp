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

#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/ethereum/rlp/execution_witness.hpp>

#include <boost/outcome/try.hpp>

#include <cstring>

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

    BOOST_OUTCOME_TRY(
        auto const pre_root, rlp::decode_byte_string_fixed<32>(outer));
    std::memcpy(w.pre_state_root.bytes, pre_root.data(), 32);

    BOOST_OUTCOME_TRY(
        auto const post_root, rlp::decode_byte_string_fixed<32>(outer));
    std::memcpy(w.post_state_root.bytes, post_root.data(), 32);

    BOOST_OUTCOME_TRY(w.encoded_nodes, rlp::parse_list_metadata(outer));

    BOOST_OUTCOME_TRY(w.encoded_codes, rlp::parse_list_metadata(outer));

    // preimages — advance past it, do not store.
    BOOST_OUTCOME_TRY(auto const preimages, rlp::parse_list_metadata(outer));
    (void)preimages;

    BOOST_OUTCOME_TRY(w.encoded_headers, rlp::parse_list_metadata(outer));

    if (MONAD_UNLIKELY(!outer.empty())) {
        return rlp::DecodeError::InputTooLong;
    }

    return w;
}

byte_string encode_execution_witness(
    byte_string_view const block_rlp, bytes32_t const &pre_state_root,
    bytes32_t const &post_state_root, std::span<byte_string const> const nodes,
    std::span<byte_string const> const codes,
    std::span<byte_string const> const headers)
{
    byte_string nodes_body;
    for (auto const &n : nodes) {
        nodes_body += rlp::encode_string2(n);
    }

    byte_string codes_body;
    for (auto const &c : codes) {
        codes_body += rlp::encode_string2(c);
    }

    // Each header is already RLP-encoded as a list; reth wraps each one as
    // an opaque string in this outer list (first byte 0xb8/0xb9).
    byte_string headers_body;
    for (auto const &h : headers) {
        headers_body += rlp::encode_string2(h);
    }

    return rlp::encode_list2(
        rlp::encode_string2(block_rlp),
        rlp::encode_string2(byte_string_view{pre_state_root.bytes, 32}),
        rlp::encode_string2(byte_string_view{post_state_root.bytes, 32}),
        rlp::encode_list2(nodes_body),
        rlp::encode_list2(codes_body),
        rlp::encode_list2(),
        rlp::encode_list2(headers_body));
}

MONAD_NAMESPACE_END

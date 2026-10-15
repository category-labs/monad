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
#include <optional>
#include <vector>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

/// The outer envelope. Each entry point checks for trailing bytes itself,
/// after reading the six fields its own shape defines.
Result<byte_string_view> strip_envelope(byte_string_view const witness_bytes)
{
    byte_string_view view{witness_bytes.data(), witness_bytes.size()};
    BOOST_OUTCOME_TRY(auto outer, rlp::parse_list_metadata(view));
    // No bytes may follow the outer list.
    if (MONAD_UNLIKELY(!view.empty())) {
        return rlp::DecodeError::InputTooLong;
    }
    return outer;
}

/// The node's six fields, advancing `outer`.
Result<ExecutionWitness> parse_base_fields(byte_string_view &outer)
{
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

    return w;
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

Result<ExecutionWitness> parse_execution_witness(byte_string_view witness_bytes)
{
    BOOST_OUTCOME_TRY(auto outer, strip_envelope(witness_bytes));
    BOOST_OUTCOME_TRY(auto w, parse_base_fields(outer));

    if (MONAD_UNLIKELY(!outer.empty())) {
        return rlp::DecodeError::InputTooLong;
    }

    return w;
}

Result<ExecutionWitnessL2>
parse_execution_witness_l2(byte_string_view witness_bytes)
{
    BOOST_OUTCOME_TRY(auto outer, strip_envelope(witness_bytes));

    ExecutionWitnessL2 w{};
    BOOST_OUTCOME_TRY(w.domain_body, rlp::parse_string_metadata(outer));
    BOOST_OUTCOME_TRY(w.encoded_nodes, rlp::parse_list_metadata(outer));
    BOOST_OUTCOME_TRY(w.encoded_codes, rlp::parse_list_metadata(outer));
    BOOST_OUTCOME_TRY(
        w.encoded_ancestor_hashes, rlp::parse_list_metadata(outer));
    // Field [4] is where the two shapes part: a string here, a list of
    // addresses in the node's witness. Reading one as the other stops at this
    // line rather than deeper in, where a misparse would be subtler.
    BOOST_OUTCOME_TRY(w.sk, rlp::parse_string_metadata(outer));
    BOOST_OUTCOME_TRY(w.salt_secret, rlp::parse_string_metadata(outer));

    // A secp256k1 scalar and nothing else. Its range is the cipher's business;
    // its width is the envelope's.
    if (MONAD_UNLIKELY(w.sk.size() != 32)) {
        return rlp::DecodeError::ArrayLengthUnexpected;
    }

    // The blinder's preimage. Nothing here constrains its value -- the guest's
    // commitment check does that -- only its width.
    if (MONAD_UNLIKELY(w.salt_secret.size() != 32)) {
        return rlp::DecodeError::ArrayLengthUnexpected;
    }

    if (MONAD_UNLIKELY(!outer.empty())) {
        return rlp::DecodeError::InputTooLong;
    }

    return w;
}

MONAD_NAMESPACE_END

MONAD_ANONYMOUS_NAMESPACE_BEGIN

/// The offset-format blob, emitted raw inside a list envelope.
std::span<unsigned char>
encode_raw_list(std::span<unsigned char> d, byte_string_view const blob)
{
    d = rlp::encode_list_prefix(d, blob.size());
    if (!blob.empty()) {
        std::memcpy(d.data(), blob.data(), blob.size());
        d = d.subspan(blob.size());
    }
    return d;
}

/// A list of pre-encoded strings, each wrapped.
std::span<unsigned char> encode_string_list(
    std::span<unsigned char> d, std::span<byte_string const> const items,
    size_t const payload)
{
    d = rlp::encode_list_prefix(d, payload);
    for (auto const &i : items) {
        d = rlp::encode_string(d, i);
    }
    return d;
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

byte_string encode_execution_witness(
    byte_string_view const block_rlp, byte_string_view const nodes,
    std::span<byte_string const> const codes,
    std::span<byte_string const> const headers,
    ankerl::unordered_dense::segmented_set<Address> const
        *const parent_senders_and_authorities,
    ankerl::unordered_dense::segmented_set<Address> const
        *const grandparent_senders_and_authorities)
{
    // 20-byte address -> 1-byte length prefix (0x94) + 20 payload bytes.
    static_assert(sizeof(Address) == 20);
    constexpr size_t addr_string_size = 1 + sizeof(Address);

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
        rlp::string_length(block_rlp) + rlp::list_length(nodes.size()) +
        rlp::list_length(codes_payload) + rlp::list_length(headers_payload) +
        rlp::list_length(parent_payload) +
        rlp::list_length(grandparent_payload);

    byte_string result;
    result.resize_and_overwrite(
        rlp::list_length(outer_payload),
        [](auto *, size_t const count) { return count; });
    std::span<unsigned char> d{result};

    d = rlp::encode_list_prefix(d, outer_payload);
    d = rlp::encode_string(d, block_rlp);
    d = encode_raw_list(d, nodes);
    d = encode_string_list(d, codes, codes_payload);
    d = encode_string_list(d, headers, headers_payload);

    // segmented_set has no defined iteration order, so emit addresses sorted
    // to keep the encoding deterministic across runs.
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

    d = rlp::encode_list_prefix(d, parent_payload);
    d = encode_addresses(d, parent_senders_and_authorities);
    d = rlp::encode_list_prefix(d, grandparent_payload);
    d = encode_addresses(d, grandparent_senders_and_authorities);

    MONAD_ASSERT(d.empty());
    return result;
}

byte_string encode_execution_witness_l2(
    byte_string_view const domain_body, byte_string_view const nodes,
    std::span<byte_string const> const codes,
    std::span<byte_string const> const ancestor_hashes,
    byte_string_view const sk, byte_string_view const salt_secret)
{
    MONAD_ASSERT(sk.size() == 32);
    MONAD_ASSERT(salt_secret.size() == 32);

    size_t codes_payload = 0;
    for (auto const &c : codes) {
        codes_payload += rlp::string_length(c);
    }
    size_t hashes_payload = 0;
    for (auto const &h : ancestor_hashes) {
        MONAD_ASSERT(h.size() == sizeof(bytes32_t));
        hashes_payload += rlp::string_length(h);
    }

    size_t const outer_payload =
        rlp::string_length(domain_body) + rlp::list_length(nodes.size()) +
        rlp::list_length(codes_payload) + rlp::list_length(hashes_payload) +
        rlp::string_length(sk) + rlp::string_length(salt_secret);

    byte_string result;
    result.resize_and_overwrite(
        rlp::list_length(outer_payload),
        [](auto *, size_t const count) { return count; });
    std::span<unsigned char> d{result};

    d = rlp::encode_list_prefix(d, outer_payload);
    d = rlp::encode_string(d, domain_body);
    d = encode_raw_list(d, nodes);
    d = encode_string_list(d, codes, codes_payload);
    d = encode_string_list(d, ancestor_hashes, hashes_payload);
    d = rlp::encode_string(d, sk);
    d = rlp::encode_string(d, salt_secret);

    MONAD_ASSERT(d.empty());
    return result;
}

MONAD_NAMESPACE_END

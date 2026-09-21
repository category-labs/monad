// Copyright (C) 2026 Category Labs, Inc.
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

// See namespace_anchor.hpp for why the rule lives here and why it is not the
// ordered trie.

#include <category/execution/ethereum/namespace_anchor.hpp>

#include <category/core/assert.h>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/core/contract/abi_decode.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/validate_block.hpp>

#include <boost/outcome/try.hpp>

#include <cstddef>
#include <cstdint>
#include <cstring>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

/// keccak256(min(a,b) || max(a,b)). bytes32_t's operator<=> is a lexicographic
/// compare over its 32 bytes, which for a big-endian value is exactly
/// Solidity's `<` on bytes32 -- so this is MerkleTreeLib._hashPair.
bytes32_t hash_pair(bytes32_t const &a, bytes32_t const &b)
{
    bool const swapped = b < a;
    unsigned char buf[2 * sizeof(bytes32_t)];
    std::memcpy(buf, (swapped ? b : a).bytes, sizeof(bytes32_t));
    std::memcpy(
        buf + sizeof(bytes32_t), (swapped ? a : b).bytes, sizeof(bytes32_t));
    return to_bytes(keccak256(buf));
}

/// The one value Solidity can emit for this event's `data` offset, as the ABI
/// word it arrives as. Checked rather than assumed: anything else means the
/// parameter list changed, and messageHash would no longer be where this reads
/// it from.
///
/// A comparison against the thirty-two bytes rather than a decode to uint256.
/// The question is whether the head word IS this word, which needs no
/// byteswap and no temporary; the two are equivalent, this one says it.
constexpr bytes32_t EXPECTED_DATA_OFFSET =
    store_be_as<bytes32_t>(uint256_t{NAMESPACE_LOG_DATA_OFFSET});

bool head_offset_is_expected(byte_string_view const data)
{
    // The caller's size check short-circuits before this, so the word is there.
    MONAD_DEBUG_ASSERT(data.size() >= sizeof(EXPECTED_DATA_OFFSET.bytes));
    return std::memcmp(
               data.data(),
               EXPECTED_DATA_OFFSET.bytes,
               sizeof(EXPECTED_DATA_OFFSET.bytes)) == 0;
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

Result<std::vector<bytes32_t>> collect_namespace_messages(
    std::span<Receipt const> const receipts, Address const &spoke)
{
    std::vector<bytes32_t> leaves;
    for (auto const &receipt : receipts) {
        for (auto const &log : receipt.logs) {
            if (log.address != spoke || log.topics.empty() ||
                log.topics[0] != NAMESPACE_MESSAGE_RECORDED_TOPIC) {
                continue;
            }
            // Past this point the log claims to be ours, so a defect is the
            // contract's and not the prover's -- fail the block.
            if (MONAD_UNLIKELY(
                    log.topics.size() != 3 ||
                    log.data.size() < NAMESPACE_LOG_MIN_SIZE ||
                    !head_offset_is_expected(log.data))) {
                return BlockError::InvalidNamespaceLog;
            }
            // The declared tail length has to account for the whole data
            // section, padded to a word: a log whose size does not follow from
            // its own length field was not produced by this ABI.
            byte_string_view tail{log.data};
            tail.remove_prefix(NAMESPACE_LOG_HEAD_WORDS * 32);
            BOOST_OUTCOME_TRY(
                auto const declared, abi_decode_fixed<u256_be>(tail));
            // One .native(): it is a 256-bit byteswap, and the narrowing test
            // below only wants to know whether the word is a length at all.
            auto const declared_len = declared.native();
            auto const len = static_cast<std::size_t>(declared_len);
            if (MONAD_UNLIKELY(
                    declared_len != len ||
                    log.data.size() !=
                        NAMESPACE_LOG_MIN_SIZE + ((len + 31) / 32) * 32)) {
                return BlockError::InvalidNamespaceLog;
            }

            // messageHash is the third head word. Read directly: there is no
            // abi_decode_fixed<bytes32_t> -- its constraint admits big-endian
            // wrappers and Address, and bytes32_t is neither.
            bytes32_t leaf;
            std::memcpy(
                leaf.bytes,
                log.data.data() + NAMESPACE_LOG_HASH_OFFSET,
                sizeof(leaf.bytes));
            leaves.push_back(leaf);
        }
    }
    return leaves;
}

bytes32_t sorted_pair_merkle_root(std::vector<bytes32_t> &leaves)
{
    if (leaves.empty()) {
        return bytes32_t{};
    }
    // In place, and the write index never overtakes the reads: pair i reads 2i
    // and 2i+1 and writes i, and i <= 2i. The promoted node lands at
    // (n+1)/2 - 1, which the pair loop stops short of, and comes from n-1,
    // which for odd n the pair loop never touches.
    std::size_t n = leaves.size();
    while (n > 1) {
        std::size_t const next = (n + 1) / 2;
        for (std::size_t i = 0; i < n / 2; ++i) {
            leaves[i] = hash_pair(leaves[2 * i], leaves[2 * i + 1]);
        }
        if (n % 2 == 1) {
            leaves[next - 1] = leaves[n - 1];
        }
        n = next;
    }
    return leaves[0];
}

bytes32_t namespace_pending_element_key(
    std::uint64_t const slot, std::uint64_t const index)
{
    // store_be_as and NOT to_bytes: to_bytes(uint256_t) is a bare bit_cast, so
    // on a little-endian target it yields the value's LITTLE-endian bytes. A
    // storage key is a big-endian word, which is what storage_array.hpp uses
    // store_be_as for. The difference is silent and it would clear the wrong
    // slots.
    bytes32_t const length_key = store_be_as<bytes32_t>(uint256_t{slot});
    auto const base = load_be<uint256_t>(to_bytes(keccak256(length_key.bytes)));
    return store_be_as<bytes32_t>(base + index);
}

void clear_pending_namespace_messages(
    State &state, Address const &spoke, std::uint64_t const slot,
    std::uint64_t const expected_length)
{
    // State::get_storage requires the account to have been read first -- it
    // asserts on one that is not in original_ -- and the epilogue runs on
    // every block, including the overwhelming majority that never touch the
    // spoke. So this is not a convenience check: without it the guest aborts
    // on any block whose transactions leave the spoke alone.
    if (!state.account_exists(spoke)) {
        // No account, so no log could have come from it, so nothing was
        // harvested. A spoke that is absent where the protocol says one is
        // deployed is a misconfiguration, and the assertion is what says so.
        MONAD_ASSERT(expected_length == 0);
        return;
    }

    bytes32_t const length_key = store_be_as<bytes32_t>(uint256_t{slot});
    auto const stored =
        load_be<uint256_t>(state.get_storage(spoke, length_key));
    // See the header: this is the check that catches the leaf set and the
    // pending array drifting apart, which nothing downstream can.
    MONAD_ASSERT(stored == expected_length);
    if (expected_length == 0) {
        // Nothing pushed, nothing to clear -- and the contract's own
        // length == 0 early return does not write either.
        return;
    }

    // Solidity puts a dynamic array's elements at keccak256(slot) + i.
    for (std::uint64_t i = 0; i < expected_length; ++i) {
        state.set_storage(
            spoke, namespace_pending_element_key(slot, i), bytes32_t{});
    }
    state.set_storage(spoke, length_key, bytes32_t{});
}

MONAD_NAMESPACE_END

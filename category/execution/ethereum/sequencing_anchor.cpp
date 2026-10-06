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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#ifdef MONAD_L2_HASH_POSEIDON2
    #include <category/core/poseidon2.hpp>
#endif
#include <category/execution/ethereum/sequencing_anchor.hpp>

#include <cstddef>
#include <cstdint>
#include <span>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

/// The chain's hash (MONAD_ZKVM_L2_HASH), for the leaves and for the anchor
/// alike: the Poseidon2 sponge in a chain built on Poseidon2 -- ZisK's
/// precompile in the guest, the same permutation in software on the host --
/// and keccak256 otherwise.
bytes32_t chain_hash(byte_string_view const bytes)
{
#ifdef MONAD_L2_HASH_POSEIDON2
    bytes32_t out;
    monad_poseidon2_256(bytes.data(), bytes.size(), out.bytes);
    return out;
#else
    return to_bytes(keccak256(bytes));
#endif
}

/// Big-endian, like every other multi-byte quantity this protocol puts on the
/// wire, and written out rather than taken from a helper so that the byte order
/// of a value the L1 must reproduce is visible in the file that defines it.
void append_be64(monad::byte_string &out, uint64_t const v)
{
    for (size_t i = 0; i < sizeof(uint64_t); ++i) {
        out.push_back(
            static_cast<unsigned char>(v >> (8 * (sizeof(uint64_t) - 1 - i))));
    }
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

bytes32_t sequencing_anchor(
    uint64_t const domain_chain_id, uint64_t const block_number,
    std::span<byte_string_view const> const ciphertexts)
{
    // The label's terminating NUL is not absorbed: it carries nothing, and
    // leaving it out is what a Solidity `abi.encodePacked("...")` of the same
    // string does.
    constexpr size_t LABEL_LEN = sizeof(SEQUENCING_ANCHOR_LABEL) - 1;
    constexpr size_t PREAMBLE_LEN = LABEL_LEN + 2 * sizeof(uint64_t);

    // One allocation. The buffer is the sponge's whole input, so sizing it up
    // front is also what keeps this a single pass over the leaves.
    byte_string buf;
    buf.reserve(PREAMBLE_LEN + ciphertexts.size() * sizeof(bytes32_t));
    buf.append(
        reinterpret_cast<unsigned char const *>(SEQUENCING_ANCHOR_LABEL),
        LABEL_LEN);
    append_be64(buf, domain_chain_id);
    append_be64(buf, block_number);

    for (auto const &ciphertext : ciphertexts) {
        bytes32_t const leaf = chain_hash(ciphertext);
        buf.append(leaf.bytes, sizeof(leaf.bytes));
    }

    return chain_hash(byte_string_view{buf});
}

MONAD_NAMESPACE_END

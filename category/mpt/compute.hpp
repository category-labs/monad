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

#pragma once

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/rlp/encode.hpp>

#include <category/core/mem/allocators.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/merkle/compact_encode.hpp>
#include <category/mpt/merkle/node_reference.hpp>
#include <category/mpt/node.hpp>

#include <algorithm>
#include <cstdint>
#include <span>

MONAD_MPT_NAMESPACE_BEGIN

namespace detail
{
    struct InternalMerkleState
    {
        unsigned char buffer[KECCAK256_SIZE];
        unsigned len{0};

        void keccak_inplace_to_root_hash()
        {
            MONAD_DEBUG_ASSERT(len <= KECCAK256_SIZE);
            if (len < KECCAK256_SIZE) {
                keccak256(buffer, len, buffer);
                len = KECCAK256_SIZE;
            }
        }
    };
}

std::span<unsigned char> encode_empty_string(std::span<unsigned char> result);

std::span<unsigned char>
encode_16_children(std::span<ChildData>, std::span<unsigned char> result);

std::span<unsigned char>
encode_16_children(Node *, std::span<unsigned char> result);

unsigned encode_two_pieces(
    unsigned char *const dest, NibblesView const path,
    byte_string_view const second, bool const has_value = false);

struct Compute
{
    virtual ~Compute() = default;
    //! compute length of hash from a span of child data, which include the node
    //! pointer, file offset and calculated hash
    virtual unsigned compute_len(
        std::span<ChildData> children, uint16_t mask, NibblesView path,
        std::optional<byte_string_view> value) = 0;
    //! compute hash_data inside node if hash_len > 0, which is the hash of all
    //! node's branches, return hash data length
    virtual unsigned compute_branch(unsigned char *buffer, Node *node) = 0;
    //! compute data of a trie rooted at node, put data to first argument and
    //! return data length
    virtual unsigned compute(unsigned char *buffer, Node *node) = 0;
};

template <typename T>
concept compute_leaf_data = requires {
    { T::compute(std::declval<Node const &>()) } -> std::same_as<byte_string>;
};

template <compute_leaf_data TComputeLeafData>
struct MerkleComputeBase : Compute
{
    static constexpr auto max_branch_rlp_size = rlp::list_length(
        rlp::list_length(KECCAK256_SIZE) * 16 + rlp::list_length(0));
    static constexpr auto max_leaf_data_size = rlp::list_length( // account rlp
        rlp::list_length(32) // balance
        + rlp::list_length(KECCAK256_SIZE) // code hash
        + rlp::list_length(KECCAK256_SIZE) // storage hash
        + rlp::list_length(8) // nonce
    );
    static_assert(max_branch_rlp_size == 532);
    static_assert(max_leaf_data_size == 110);

    // Compute data from children and value to the internal state, which
    // will later be copied to in the intermediate data section inside node
    virtual unsigned compute_len(
        std::span<ChildData> const children, uint16_t const mask,
        NibblesView /*path*/,
        std::optional<byte_string_view> const value) override
    {
        MONAD_DEBUG_ASSERT(mask);
        if (!value.has_value()) {
            // no intermediate data for non-leaf node
            return 0;
        }
        // special case, the node to be created has only one branch
        if (std::has_single_bit(mask)) {
            auto const it = std::ranges::find_if(
                children, [](ChildData const &item) constexpr {
                    return item.is_valid();
                });
            MONAD_DEBUG_ASSERT(it != children.end());
            MONAD_DEBUG_ASSERT(it->branch < 16);
            MONAD_DEBUG_ASSERT(it->ptr);
            compute_hash_with_extra_nibble_to_state_(*it);
            // root data of a subtrie is always a hash
            state.keccak_inplace_to_root_hash();
            return KECCAK256_SIZE;
        }

        unsigned char branch_str_rlp[max_branch_rlp_size];
        auto result = encode_16_children(children, {branch_str_rlp});
        // encode empty value string
        result = encode_empty_string(result);
        auto const concat_len =
            static_cast<size_t>(result.data() - branch_str_rlp);
        MONAD_DEBUG_ASSERT(concat_len <= max_branch_rlp_size);

        // encode list
        auto const rlp_len = rlp::list_length(concat_len);
        MONAD_DEBUG_ASSERT(rlp_len <= max_branch_rlp_size);
        unsigned char branch_rlp[max_branch_rlp_size];
        rlp::encode_list(
            branch_rlp, byte_string_view{branch_str_rlp, concat_len});
        // Compute hash to internal state and return hash length
        state.len = to_node_reference({branch_rlp, rlp_len}, state.buffer);
        // root data of merkle trie is always a hash
        state.keccak_inplace_to_root_hash();
        return KECCAK256_SIZE;
    }

    virtual unsigned
    compute_branch(unsigned char *const buffer, Node *const node) override
    {
        MONAD_DEBUG_ASSERT(node->number_of_children());
        if (state.len) {
            // a simple memcpy if already computed to internal state
            std::memcpy(buffer, state.buffer, state.len);
            unsigned const len = state.len;
            // reset state
            state.len = 0;
            return len;
        }
        unsigned char branch_str_rlp[max_branch_rlp_size];
        auto result = encode_16_children(node, {branch_str_rlp});
        // encode empty value string
        result = encode_empty_string(result);

        auto const concat_len =
            static_cast<size_t>(result.data() - branch_str_rlp);
        MONAD_ASSERT(concat_len <= max_branch_rlp_size);
        auto const branch_rlp_len = rlp::list_length(concat_len);
        MONAD_DEBUG_ASSERT(branch_rlp_len <= max_branch_rlp_size);

        unsigned char branch_rlp[max_branch_rlp_size];
        rlp::encode_list(
            branch_rlp, byte_string_view{branch_str_rlp, concat_len});
        return to_node_reference({branch_rlp, branch_rlp_len}, buffer);
    }

    virtual unsigned
    compute(unsigned char *const buffer, Node *const node) override
    {
        if (node->has_value()) {
            return encode_two_pieces(
                buffer,
                node->path_nibble_view(),
                TComputeLeafData::compute(*node),
                true);
        }
        MONAD_DEBUG_ASSERT(node->number_of_children() > 1);
        if (node->has_path()) {
            unsigned char reference[KECCAK256_SIZE];
            unsigned len = compute_branch(reference, node);
            return encode_two_pieces(
                buffer, node->path_nibble_view(), {reference, len}, false);
        }
        return compute_branch(buffer, node);
    }

protected:
    detail::InternalMerkleState state{};

    unsigned compute_hash_with_extra_nibble_to_state_(ChildData &single_child)
    {
        Node *const node = single_child.ptr.get();
        MONAD_DEBUG_ASSERT(node);

        return state.len = encode_two_pieces(
                state.buffer,
                concat(single_child.branch, node->path_nibble_view()),
                (node->has_value()
                     ? TComputeLeafData::compute(*node)
                     : (node->has_path()
                            ? ([&] -> byte_string {
                                  unsigned char branch_hash[KECCAK256_SIZE];
                                  return {
                                      branch_hash,
                                      compute_branch(branch_hash, node)};
                              }())
                            : byte_string_view{single_child.data, single_child.len})),
                node->has_value());
    }
};

/* Compute implementation for variable length merkle trie, for example receipt
trie. Current use cases only involve insert operation but no update or erase
in the middle of a variable length trie.

TODO for vicky: consolidate VarLenMerkleCompute and MerkleCompute into one.
*/

template <typename T>
concept leaf_processor = requires {
    {
        T::process(std::declval<byte_string_view>())
    } -> std::same_as<byte_string_view>;
};

struct NoopProcessor
{
    static byte_string_view process(byte_string_view const in)
    {
        return in;
    }
};

template <leaf_processor LeafDataProcessor = NoopProcessor>
struct VarLenMerkleCompute : Compute
{
    static constexpr auto calc_rlp_max_size =
        [](unsigned const leaf_data_size) -> unsigned {
        return static_cast<unsigned>(rlp::list_length(
            rlp::list_length(KECCAK256_SIZE) * 16 +
            rlp::list_length(leaf_data_size)));
    };

    // Compute the intermediate branch data to the internal state.
    // For variable length merkle trie, we store branch node data inline in
    // nodes that have at least one child and non-empty path.
    virtual unsigned compute_len(
        std::span<ChildData> const children, uint16_t const mask,
        NibblesView const path,
        std::optional<byte_string_view> const value) override
    {
        MONAD_ASSERT(mask);
        if (path.empty()) {
            // node without any children or node with empty path has no
            // intermediate data
            return 0;
        }
        return do_compute_len(children, value);
    }

    virtual unsigned compute_branch(unsigned char *buffer, Node *node) override
    {
        // copy from internal state
        MONAD_DEBUG_ASSERT(node->number_of_children());
        if (state.len) {
            // a simple memcpy if already computed to internal state in
            // compute_len()
            std::memcpy(buffer, state.buffer, state.len);
            unsigned const len = state.len;
            state.len = 0;
            return len;
        }
        // compute branch node hash
        byte_string branch_str_rlp(calc_rlp_max_size(node->value_len), 0);
        auto result = encode_16_children(node, branch_str_rlp);
        // encode vt
        result = (node->has_value() && node->value_len)
                     ? rlp::encode_string(
                           result, LeafDataProcessor::process(node->value()))
                     : encode_empty_string(result);
        auto const concat_len =
            static_cast<size_t>(result.data() - branch_str_rlp.data());
        byte_string branch_rlp(rlp::list_length(concat_len), 0);
        rlp::encode_list(branch_rlp, {branch_str_rlp.data(), concat_len});
        return to_node_reference(
            {branch_rlp.data(), branch_rlp.size()}, buffer);
    }

    virtual unsigned compute(unsigned char *buffer, Node *node) override
    {
        // Ethereum leaf: leaf node hash without child
        if (node->number_of_children() == 0) {
            MONAD_ASSERT(node->has_value());
            return encode_two_pieces(
                buffer,
                node->path_nibble_view(),
                LeafDataProcessor::process(node->value()),
                true);
        }
        // Ethereum extension: there is non-empty path
        // rlp(encoded path, inline branch hash)
        if (node->has_path()) { // extension node, rlp encode with path too
            MONAD_ASSERT(node->bitpacked.data_len);
            return encode_two_pieces(
                buffer,
                node->path_nibble_view(),
                node->data(),
                node->has_value());
        }
        // Ethereum branch
        return compute_branch(buffer, node);
    }

protected:
    detail::InternalMerkleState state;

    unsigned do_compute_len(
        std::span<ChildData> const children,
        std::optional<byte_string_view> const value)
    {
        // compute branch node data to internal state
        unsigned const branch_str_max_len = calc_rlp_max_size(
            (unsigned)value.transform(&byte_string_view::size).value_or(0));

        byte_string branch_str_rlp(branch_str_max_len, 0);
        auto result = encode_16_children(children, branch_str_rlp);
        // encode vt
        result = (value.has_value() && value.value().size())
                     ? rlp::encode_string(
                           result, LeafDataProcessor::process(value.value()))
                     : encode_empty_string(result);
        auto const concat_len =
            static_cast<size_t>(result.data() - branch_str_rlp.data());
        // encode list
        byte_string rlp(rlp::list_length(concat_len), 0);
        rlp::encode_list(rlp, {branch_str_rlp.data(), concat_len});
        // Compute hash to internal state and return hash length
        state.len = to_node_reference({rlp.data(), rlp.size()}, state.buffer);
        return state.len;
    }
};

template <leaf_processor LeafDataProcessor = NoopProcessor>
struct RootVarLenMerkleCompute : public VarLenMerkleCompute<LeafDataProcessor>
{
    using Base = VarLenMerkleCompute<LeafDataProcessor>;
    using Base::state;

    virtual unsigned compute(unsigned char *const, Node *const) override
    {
        return 0;
    }

    virtual unsigned compute_len(
        std::span<ChildData> const children, uint16_t mask, NibblesView,
        std::optional<byte_string_view> const value) override
    {
        MONAD_ASSERT(mask);
        if (std::has_single_bit(mask)) {
            auto const it = std::ranges::find_if(
                children, [](ChildData const &item) constexpr {
                    return item.is_valid();
                });
            MONAD_DEBUG_ASSERT(it != children.end());
            MONAD_DEBUG_ASSERT(it->branch < 16);
            MONAD_DEBUG_ASSERT(it->ptr);
            compute_hash_with_extra_nibble_to_state_(*it);
        }
        else {
            Base::do_compute_len(children, value);
        }
        // root data of a merkle trie is always a hash
        state.keccak_inplace_to_root_hash();
        return KECCAK256_SIZE;
    }

    virtual unsigned compute_branch(unsigned char *buffer, Node *node) override
    {
        return Base::compute_branch(buffer, node);
    }

private:
    unsigned compute_hash_with_extra_nibble_to_state_(ChildData &single_child)
    {
        Node *const node = single_child.ptr.get();
        MONAD_DEBUG_ASSERT(node);

        return state.len = encode_two_pieces(
                   state.buffer,
                   concat(single_child.branch, node->path_nibble_view()),
                   /* second: branch hash or leaf value */
                   node->mask ? (node->bitpacked.data_len ? node->data()
                                                          : [&] -> byte_string {
                       MONAD_ASSERT(!node->has_path());
                       unsigned char branch_hash[KECCAK256_SIZE];
                       return {branch_hash, compute_branch(branch_hash, node)};
                   }())
                              : LeafDataProcessor::process(node->value()),
                   node->has_value());
    }
};

MONAD_MPT_NAMESPACE_END

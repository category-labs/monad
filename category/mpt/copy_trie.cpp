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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/mem/allocators.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/util.hpp>

#include <array>
#include <bit>
#include <cstdint>
#include <limits>
#include <optional>
#include <stack>
#include <utility>
#include <vector>

MONAD_MPT_NAMESPACE_BEGIN

Node::UniquePtr create_node_add_new_branch(
    UpdateAuxImpl &aux, Node *const node, unsigned char const new_branch,
    Node::UniquePtr new_child, uint64_t const new_version,
    std::optional<byte_string_view> opt_value)
{
    uint16_t const mask =
        static_cast<uint16_t>(node->mask | (1u << new_branch));
    std::vector<ChildData> children(static_cast<unsigned>(std::popcount(mask)));
    for (unsigned i = 0, j = 0, old_j = 0, bit = 1; i < 16; ++i, bit <<= 1) {
        if (i == new_branch) {
            auto &child = children[j];
            child.branch = (unsigned char)i;
            child.ptr = std::move(new_child);
            child.subtrie_min_version = calc_min_version(*child.ptr);
            if (aux.is_on_disk()) {
                child.offset =
                    async_write_node_set_spare(aux, *child.ptr, true);
                std::tie(child.min_offset_fast, child.min_offset_slow) =
                    calc_min_offsets(
                        *child.ptr, aux.physical_to_virtual(child.offset));
            }
            ++j;
        }
        else if (mask & bit) {
            auto &child = children[j];
            child.branch = (unsigned char)i;
            child.ptr = node->move_next(old_j);
            child.subtrie_min_version = node->subtrie_min_version(old_j);
            if (aux.is_on_disk()) {
                child.min_offset_fast = node->min_offset_fast(old_j);
                child.min_offset_slow = node->min_offset_slow(old_j);
                child.offset = node->fnext(old_j);
                MONAD_ASSERT(child.offset != INVALID_OFFSET);
            }
            ++old_j;
            ++j;
        }
    }
    return make_node(
        mask,
        children,
        node->path_nibble_view(),
        opt_value,
        0,
        static_cast<int64_t>(new_version));
}

Node::UniquePtr create_node_with_two_children(
    UpdateAuxImpl &aux, NibblesView const path, unsigned char const branch0,
    Node::UniquePtr child0, unsigned char const branch1, Node::UniquePtr child1,
    uint64_t const new_version, std::optional<byte_string_view> opt_value)
{
    // mismatch: split node's path: turn node to a branch node with two
    // children
    uint16_t const mask =
        static_cast<uint16_t>((1u << branch0) | (1u << branch1));
    bool const zero_comes_first = branch0 < branch1;
    ChildData children[2];
    {
        auto &child = children[!zero_comes_first];
        child.ptr = std::move(child0);
        child.subtrie_min_version = calc_min_version(*child.ptr);
        child.branch = branch0;
        if (aux.is_on_disk()) {
            child.offset = async_write_node_set_spare(aux, *child.ptr, true);
            std::tie(child.min_offset_fast, child.min_offset_slow) =
                calc_min_offsets(*child.ptr);
        }
    }
    {
        auto &child = children[zero_comes_first];
        child.ptr = std::move(child1);
        child.subtrie_min_version = calc_min_version(*child.ptr);
        child.branch = branch1;
        if (aux.is_on_disk()) {
            child.offset = async_write_node_set_spare(aux, *child.ptr, true);
            std::tie(child.min_offset_fast, child.min_offset_slow) =
                calc_min_offsets(*child.ptr);
        }
    }
    return make_node(
        mask,
        std::span(children),
        path,
        opt_value,
        0,
        static_cast<int64_t>(new_version));
}

Node::SharedPtr copy_trie_impl(
    UpdateAuxImpl &aux, NodeCursor src_root, NibblesView const src_prefix,
    uint64_t const src_version, Node::SharedPtr root, NibblesView const dest,
    uint64_t const dest_version)
{
    auto [src_cursor, res, tp] =
        find_blocking(aux, src_root, src_prefix, src_version);
    MONAD_ASSERT(res == find_result::success);
    Node &src_node = *src_cursor.node;
    if (!root) {
        auto new_node = make_node(
            src_node,
            dest.substr(1),
            src_node.opt_value(),
            static_cast<int64_t>(dest_version));
        ChildData child{.ptr = std::move(new_node), .branch = dest.get(0)};
        child.subtrie_min_version = calc_min_version(*child.ptr);
        if (aux.is_on_disk()) {
            child.offset = async_write_node_set_spare(aux, *child.ptr, true);
            std::tie(child.min_offset_fast, child.min_offset_slow) =
                calc_min_offsets(
                    *child.ptr, aux.physical_to_virtual(child.offset));
        }
        return make_node(
            static_cast<uint16_t>(1u << child.branch),
            {&child, 1},
            {},
            src_root.node->value(),
            0,
            static_cast<int64_t>(dest_version));
    }
    // serialize to buffer for each new node created
    Node *parent = nullptr;
    unsigned char branch = INVALID_BRANCH;
    Node::SharedPtr node = root;
    Node::UniquePtr new_node{};
    unsigned prefix_index = 0;
    unsigned node_prefix_index = 0;

    using ParentIndexPair = std::pair<Node *, unsigned char>;
    std::vector<ParentIndexPair> vec_pairs;
    vec_pairs.reserve(16);
    std::stack<ParentIndexPair, std::vector<ParentIndexPair>>
        parents_and_indexes{std::move(vec_pairs)};

    // Insert `dest` to trie, create the `dest` node to have the same
    // children as node at `src`. Disconnect src_node's in memory children to
    // avoid double references
    while (prefix_index < dest.nibble_size()) {
        auto const nibble = dest.get(prefix_index);
        if (node_prefix_index < node->path_nibbles_len()) {
            // not yet end of path in node
            auto const node_nibble =
                node->path_nibble_view().get(node_prefix_index);
            if (nibble == node_nibble) {
                ++prefix_index;
                ++node_prefix_index;
                continue;
            }
            MONAD_DEBUG_ASSERT(
                prefix_index < std::numeric_limits<unsigned char>::max());
            auto const node_path = node->path_nibble_view();
            // copy children of src_node to under `dest` prefix, move the in
            // memory children to `dest` node
            auto dest_latter_half = make_node(
                src_node,
                dest.substr(static_cast<unsigned char>(prefix_index) + 1u),
                src_node.opt_value(),
                src_node.version);
            auto node_latter_half = make_node(
                *node,
                node_path.substr(
                    static_cast<unsigned char>(node_prefix_index) + 1),
                node->opt_value(),
                node->version);
            new_node = create_node_with_two_children(
                aux,
                node_path.substr(0, node_prefix_index),
                nibble,
                std::move(dest_latter_half),
                node_nibble,
                std::move(node_latter_half),
                dest_version,
                node.get() == root.get()
                    ? std::make_optional(src_root.node->value())
                    : std::nullopt);
            break;
        }
        // end of node path
        if (node->mask & (1u << nibble)) {
            auto const index = node->to_child_index(nibble);
            if (node->next(index) == nullptr) {
                Node::UniquePtr next_node_ondisk =
                    read_node_blocking(aux, node->fnext(index), dest_version);
                MONAD_ASSERT(next_node_ondisk != nullptr);
                node->set_next(index, std::move(next_node_ondisk));
            }
            // there is a matched branch, go to next child
            parent = node.get();
            branch = nibble;
            parents_and_indexes.emplace(std::make_pair(parent, index));
            node = node->next(index);
            node_prefix_index = 0;
            ++prefix_index;
            continue;
        }
        MONAD_DEBUG_ASSERT(
            prefix_index < std::numeric_limits<unsigned char>::max());
        auto dest_node = make_node(
            src_node,
            dest.substr(static_cast<unsigned char>(prefix_index) + 1u),
            src_node.opt_value(),
            src_node.version);
        new_node = create_node_add_new_branch(
            aux,
            node.get(),
            nibble,
            std::move(dest_node),
            dest_version,
            node.get() == root.get()
                ? std::make_optional(src_root.node->value())
                : std::nullopt);
        break;
    }

    if (prefix_index == dest.nibble_size()) { // replace existing `dest` trie
        MONAD_ASSERT(node_prefix_index == node->path_nibbles_len());
        new_node = make_node(
            src_node,
            node->path_nibble_view(),
            src_node.opt_value(),
            static_cast<int64_t>(dest_version));
    }
    if (node.get() == root.get()) {
        MONAD_ASSERT(parents_and_indexes.empty());
        root = std::move(new_node);
    }
    else {
        MONAD_ASSERT(parent != nullptr);
        auto const child_index = parent->to_child_index(branch);
        // reset child at `branch` to the new_node
        parent->set_next(child_index, std::move(new_node));
        parents_and_indexes.emplace(std::make_pair(parent, child_index));
        // serialize nodes of insert path up until root (excludes root)
        while (!parents_and_indexes.empty()) {
            auto const &[p, i] = parents_and_indexes.top();
            auto &node = *p->next(i);
            p->set_fnext(i, async_write_node_set_spare(aux, node, true));
            auto const [min_offset_fast, min_offset_slow] =
                calc_min_offsets(node);
            p->set_min_offset_fast(i, min_offset_fast);
            p->set_min_offset_slow(i, min_offset_slow);
            p->set_subtrie_min_version(i, calc_min_version(node));
            parents_and_indexes.pop();
        }
    }

    return root;
}

Node::SharedPtr copy_trie_to_dest(
    UpdateAuxImpl &aux, NodeCursor src_root, NibblesView const src_prefix,
    uint64_t const src_version, Node::SharedPtr root,
    NibblesView const dest_prefix, uint64_t const dest_version,
    bool const must_write_to_disk)
{
    auto impl = [&]() -> Node::SharedPtr {
        root = copy_trie_impl(
            aux,
            src_root,
            src_prefix,
            src_version,
            std::move(root),
            dest_prefix,
            dest_version);
        if (must_write_to_disk && aux.version_is_valid_ondisk(dest_version) &&
            aux.is_on_disk()) { // DO NOT write new version to disk, only
                                // upsert() should write new version
            write_new_root_node(aux, *root, dest_version);
            MONAD_ASSERT(aux.db_history_max_version() >= dest_version);
        }
        if (aux.is_on_disk()) {
            MONAD_ASSERT(root->value_len == sizeof(uint32_t) * 2);
        }
        return root;
    };
    if (aux.is_current_thread_upserting()) {
        return impl();
    }
    else {
        auto g(aux.unique_lock());
        auto g2(aux.set_current_upsert_tid());
        return impl();
    }
}

MONAD_MPT_NAMESPACE_END

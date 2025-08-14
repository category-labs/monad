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

#include <category/core/byte_string.hpp>
#include <category/core/mem/allocators.hpp>

#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/util.hpp>

#include <optional>
#include <vector>

MONAD_MPT_NAMESPACE_BEGIN

enum class tnode_type : uint8_t
{
    update,
    compact,
    invalid
};

struct UpdateTNode;
struct CompactTNode;

template <class T>
concept any_tnode =
    std::same_as<T, UpdateTNode> || std::same_as<T, CompactTNode>;

template <any_tnode Derived>
struct UpwardTreeNodeBase
{
    Derived *const parent{nullptr};
    tnode_type const type{tnode_type::invalid};
    uint8_t npending{0};

    bool is_sentinel() const noexcept
    {
        return !parent;
    }
};

struct UpdateTNode : public UpwardTreeNodeBase<UpdateTNode>
{
    using Base = UpwardTreeNodeBase<UpdateTNode>;
    uint8_t branch{INVALID_BRANCH};
    uint16_t mask{0};
    uint16_t orig_mask{0};
    uint8_t path_start_index{0};
    bool end_of_path{false};
    // UpdateTNode owns old node's lifetime only when old is leaf node, as
    // opt_leaf_data has to be valid in memory when it works the way back to
    // recompute leaf data
    Node::UniquePtr old{};
    std::vector<ChildData> children{};
    Nibbles path{}; // fullpath
    std::optional<byte_string_view> opt_leaf_data{std::nullopt};
    int64_t version{0};

    UpdateTNode(
        uint16_t const orig_mask, UpdateTNode *const parent = nullptr,
        uint8_t const branch = INVALID_BRANCH, NibblesView const path = {},
        unsigned const relpath_start_index = 0, bool const end_of_path = false,
        int64_t const version = 0,
        std::optional<byte_string_view> const opt_leaf_data = std::nullopt,
        Node::UniquePtr old = {})
        : Base(
              parent, tnode_type::update,
              static_cast<uint8_t>(std::popcount(orig_mask)))
        , branch(branch)
        , mask(orig_mask)
        , orig_mask(orig_mask)
        , path_start_index(static_cast<uint8_t>(relpath_start_index))
        , end_of_path{end_of_path}
        , old(std::move(old))
        , children(npending)
        , path(path)
        , opt_leaf_data(opt_leaf_data)
        , version(version)
    {
        MONAD_ASSERT(
            relpath_start_index <
            std::numeric_limits<decltype(path_start_index)>::max());
    }

    [[nodiscard]] unsigned number_of_children() const
    {
        return static_cast<unsigned>(std::popcount(mask));
    }

    constexpr uint8_t child_index() const noexcept
    {
        MONAD_ASSERT(parent != nullptr);
        return static_cast<uint8_t>(bitmask_index(parent->orig_mask, branch));
    }

    constexpr unsigned relpath_size() const
    {
        return path.nibble_size() - path_start_index;
    }

    using allocator_type = allocators::malloc_free_allocator<UpdateTNode>;

    static allocator_type &pool()
    {
        static allocator_type v;
        return v;
    }

    using unique_ptr_type = std::unique_ptr<
        UpdateTNode, allocators::unique_ptr_allocator_deleter<
                         allocator_type, &UpdateTNode::pool>>;

    static unique_ptr_type make(UpdateTNode v)
    {
        return allocators::allocate_unique<allocator_type, &UpdateTNode::pool>(
            std::move(v));
    }
};

using tnode_unique_ptr = UpdateTNode::unique_ptr_type;

inline tnode_unique_ptr make_tnode(
    uint16_t const orig_mask, UpdateTNode *const parent = nullptr,
    uint8_t const branch = INVALID_BRANCH, NibblesView const path = {},
    unsigned const relpath_start_index = 0, bool const end_of_path = false,
    int64_t const version = 0,
    std::optional<byte_string_view> const opt_leaf_data = std::nullopt,
    Node::UniquePtr old = {})
{
    return UpdateTNode::make(UpdateTNode{
        orig_mask,
        parent,
        branch,
        path,
        relpath_start_index,
        end_of_path,
        version,
        opt_leaf_data,
        std::move(old)});
}

static_assert(sizeof(UpdateTNode) == 104);
static_assert(alignof(UpdateTNode) == 8);

struct CompactTNode : public UpwardTreeNodeBase<CompactTNode>
{
    using Base = UpwardTreeNodeBase<CompactTNode>;
    uint8_t const index{INVALID_BRANCH}; // of parent
    bool rewrite_to_fast{false};
    /* Cache the owned node after the CompactTNode is destroyed. The rule here
    is to always cache the compacted node who is child of an UpdateTNode,
    because there is a corner case where the node in UpdateTNode only has single
    child left after applying all updates. If not cached, then that single
    child may have been compacted and deallocated from memory but not yet landed
    on disk (either in write buffer or inflight for write), thus `cache_node`
    value is either the node is currently cached in memory or its node is child
    of an update tnode. */
    bool const cache_node{false};
    Node::UniquePtr node{nullptr};

    template <any_tnode Parent>
    CompactTNode(
        Parent *const parent, unsigned const index, Node::UniquePtr ptr)
        : Base(
              (CompactTNode *)parent, tnode_type::compact,
              ptr ? static_cast<uint8_t>(ptr->number_of_children()) : 0)
        , index(static_cast<uint8_t>(index))
        , cache_node(parent->type == tnode_type::update || ptr != nullptr)
        , node(std::move(ptr))
    {
    }

    void update_after_async_read(Node::UniquePtr ptr)
    {
        npending = static_cast<uint8_t>(ptr->number_of_children());
        node = std::move(ptr);
    }

    using allocator_type = allocators::malloc_free_allocator<CompactTNode>;

    static allocator_type &pool()
    {
        static allocator_type v;
        return v;
    }

    using unique_ptr_type = std::unique_ptr<
        CompactTNode, allocators::unique_ptr_allocator_deleter<
                          allocator_type, &CompactTNode::pool>>;

    static unique_ptr_type make(CompactTNode v)
    {
        return allocators::allocate_unique<allocator_type, &CompactTNode::pool>(
            std::move(v));
    }

    template <any_tnode Parent>
    static unique_ptr_type
    make(Parent *const parent, unsigned const index, Node::UniquePtr node)
    {
        MONAD_DEBUG_ASSERT(parent);
        return allocators::allocate_unique<allocator_type, &CompactTNode::pool>(
            parent, index, std::move(node));
    }
};

static_assert(sizeof(CompactTNode) == 24);
static_assert(alignof(CompactTNode) == 8);

MONAD_MPT_NAMESPACE_END

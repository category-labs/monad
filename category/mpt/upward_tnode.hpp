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
#include <category/mpt/scratch_pool.hpp>
#include <category/mpt/util.hpp>

#include <algorithm>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <new>
#include <optional>
#include <span>
#include <utility>

MONAD_MPT_NAMESPACE_BEGIN

enum class tnode_type : uint8_t
{
    update,
    compact,
    expire,
    invalid
};

struct UpdateTNode;
struct CompactTNode;
struct ExpireTNode;

template <class T>
concept any_tnode =
    std::same_as<T, ExpireTNode> || std::same_as<T, UpdateTNode> ||
    std::same_as<T, CompactTNode>;

struct TNodeBase
{
protected:
    TNodeBase *const parent_{nullptr};

public:
    tnode_type const type{tnode_type::invalid};
    uint8_t npending{0};

    bool is_sentinel() const noexcept
    {
        return !parent_;
    }

    TNodeBase *parent() const noexcept
    {
        return parent_;
    }

protected:
    TNodeBase() = default;

    TNodeBase(
        TNodeBase *const parent, tnode_type const type, uint8_t const npending)
        : parent_(parent)
        , type(type)
        , npending(npending)
    {
    }

    TNodeBase(TNodeBase &&other) noexcept
        : parent_(other.parent_)
        , type(other.type)
        , npending(std::exchange(other.npending, uint8_t{0}))
    {
    }

    ~TNodeBase()
    {
        MONAD_ASSERT(npending == 0);
    }

public:
    void child_done() noexcept
    {
        MONAD_ASSERT(npending > 0);
        --npending;
    }
};

struct UpdateExpireBase : public TNodeBase
{
    uint8_t const branch{INVALID_BRANCH};
    uint16_t mask{0};

protected:
    UpdateExpireBase(
        TNodeBase *const parent, tnode_type const type, uint8_t const npending,
        uint8_t const branch, uint16_t const mask)
        : TNodeBase(parent, type, npending)
        , branch(branch)
        , mask(mask)
    {
    }
};

// `children` and `path` point into storage that trails the struct, so a tnode
// is one ScratchPool block. Create with make().
struct UpdateTNode : public UpdateExpireBase
{
    using Base = UpdateExpireBase;
    uint16_t const orig_mask;
    // UpdateTNode keeps old node alive only when old is leaf node, as
    // opt_leaf_data has to be valid in memory when it works the way back to
    // recompute leaf data
    Node::SharedPtr old;
    std::span<ChildData> const children;
    NibblesView const path;
    std::optional<byte_string_view> opt_leaf_data;
    int64_t version;

    struct Deleter
    {
        void operator()(UpdateTNode *) const noexcept;
    };

    using unique_ptr_type = std::unique_ptr<UpdateTNode, Deleter>;

    static unique_ptr_type make(
        uint16_t orig_mask, UpdateTNode *parent = nullptr,
        uint8_t branch = INVALID_BRANCH, NibblesView path = {},
        int64_t version = 0,
        std::optional<byte_string_view> opt_leaf_data = std::nullopt,
        Node::SharedPtr old = {});

    UpdateTNode(UpdateTNode const &) = delete;
    UpdateTNode &operator=(UpdateTNode const &) = delete;

    ~UpdateTNode()
    {
        std::destroy(children.begin(), children.end());
    }

    UpdateTNode *parent() const noexcept
    {
        MONAD_ASSERT(
            !TNodeBase::parent() ||
            TNodeBase::parent()->type == tnode_type::update);
        return static_cast<UpdateTNode *>(TNodeBase::parent());
    }

    [[nodiscard]] unsigned number_of_children() const
    {
        return static_cast<unsigned>(std::popcount(mask));
    }

    constexpr uint8_t child_index() const noexcept
    {
        MONAD_ASSERT(parent() != nullptr);
        return static_cast<uint8_t>(bitmask_index(parent()->orig_mask, branch));
    }

private:
    UpdateTNode(
        uint16_t const orig_mask, UpdateTNode *const parent,
        uint8_t const branch, std::span<ChildData> const children,
        NibblesView const path, int64_t const version,
        std::optional<byte_string_view> const opt_leaf_data,
        Node::SharedPtr old)
        : Base(
              parent, tnode_type::update, static_cast<uint8_t>(children.size()),
              branch, orig_mask)
        , orig_mask(orig_mask)
        , old(std::move(old))
        , children(children)
        , path(path)
        , opt_leaf_data(opt_leaf_data)
        , version(version)
    {
    }

    static constexpr size_t
    alloc_size(size_t const number_of_children, size_t const path_bytes)
    {
        return sizeof(UpdateTNode) + number_of_children * sizeof(ChildData) +
               path_bytes;
    }
};

static_assert(sizeof(UpdateTNode) == 96);
static_assert(alignof(UpdateTNode) == 8);
static_assert(sizeof(UpdateTNode) % alignof(ChildData) == 0);

inline UpdateTNode::unique_ptr_type UpdateTNode::make(
    uint16_t const orig_mask, UpdateTNode *const parent, uint8_t const branch,
    NibblesView const path, int64_t const version,
    std::optional<byte_string_view> const opt_leaf_data, Node::SharedPtr old)
{
    auto const number_of_children =
        static_cast<size_t>(std::popcount(orig_mask));
    auto const path_bytes = path.data_span();
    auto *const mem = static_cast<std::byte *>(ScratchPool::local().allocate(
        alloc_size(number_of_children, path_bytes.size())));
    auto *const children =
        reinterpret_cast<ChildData *>(mem + sizeof(UpdateTNode));
    std::uninitialized_value_construct_n(children, number_of_children);
    auto *const path_data =
        reinterpret_cast<unsigned char *>(children + number_of_children);
    std::ranges::copy(path_bytes, path_data);
    unsigned const begin_nibble = path.begin_nibble();
    return unique_ptr_type{::new (mem) UpdateTNode{
        orig_mask,
        parent,
        branch,
        {children, number_of_children},
        NibblesView{begin_nibble, begin_nibble + path.nibble_size(), path_data},
        version,
        opt_leaf_data,
        std::move(old)}};
}

inline void
UpdateTNode::Deleter::operator()(UpdateTNode *const tnode) const noexcept
{
    auto const bytes =
        alloc_size(tnode->children.size(), tnode->path.data_size());
    tnode->~UpdateTNode();
    ScratchPool::local().deallocate(tnode, bytes);
}

using tnode_unique_ptr = UpdateTNode::unique_ptr_type;

struct CompactTNode : public TNodeBase
{
    using Base = TNodeBase;
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
    Node::SharedPtr node{nullptr};

    template <any_tnode Parent>
    CompactTNode(
        Parent *const parent, unsigned const index, Node::SharedPtr ptr)
        : Base(
              parent, tnode_type::compact,
              static_cast<uint8_t>(ptr ? ptr->number_of_children() : 0))
        , index(static_cast<uint8_t>(index))
        , cache_node(parent->type == tnode_type::update || ptr != nullptr)
        , node(std::move(ptr))
    {
        MONAD_ASSERT(parent != nullptr);
    }

    void update_after_async_read(Node::SharedPtr ptr)
    {
        npending = static_cast<uint8_t>(ptr->number_of_children());
        node = std::move(ptr);
    }

    using allocator_type = ScratchAllocator<CompactTNode>;

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
    make(Parent *const parent, unsigned const index, Node::SharedPtr node)
    {
        MONAD_ASSERT(parent);
        return allocators::allocate_unique<allocator_type, &CompactTNode::pool>(
            parent, index, std::move(node));
    }
};

static_assert(sizeof(CompactTNode) == 32);
static_assert(alignof(CompactTNode) == 8);

struct ExpireTNode : public UpdateExpireBase
{
    using Base = UpdateExpireBase;

    UpdateExpireBase *parent() const noexcept
    {
        MONAD_ASSERT(
            !TNodeBase::parent() ||
            TNodeBase::parent()->type == tnode_type::update ||
            TNodeBase::parent()->type == tnode_type::expire);
        return static_cast<UpdateExpireBase *>(TNodeBase::parent());
    }

    uint8_t const index{INVALID_BRANCH};
    /* Cache the recreated node after this struct is destroyed.
    Similar reason to what is noted above in CompactTNode, the expiring
    branch can end up being the only child after applying updates, thus
    always need to be cached if it is a child of UpdateTNode. */
    bool const cache_node{false};
    // A mask of which child to cache, each bit is a child of original node
    uint16_t cache_mask{0};
    Node::SharedPtr node{nullptr};

    ExpireTNode(
        UpdateExpireBase *const parent, unsigned const branch,
        unsigned const index, bool const cache_node, Node::SharedPtr ptr)
        : Base(
              parent, tnode_type::expire,
              static_cast<uint8_t>(ptr->number_of_children()),
              static_cast<uint8_t>(branch), ptr->mask)
        , index(static_cast<uint8_t>(index))
        , cache_node(cache_node)
        , node(std::move(ptr))
    {
        MONAD_ASSERT(parent != nullptr);
        MONAD_ASSERT(node != nullptr);
    }

    using allocator_type = ScratchAllocator<ExpireTNode>;

    static allocator_type &pool()
    {
        static allocator_type v;
        return v;
    }

    using unique_ptr_type = std::unique_ptr<
        ExpireTNode, allocators::unique_ptr_allocator_deleter<
                         allocator_type, &ExpireTNode::pool>>;

    static unique_ptr_type make(
        UpdateExpireBase *const parent, unsigned const branch,
        unsigned const index, bool const cache_node, Node::SharedPtr node)
    {
        MONAD_ASSERT(parent);
        return allocators::allocate_unique<allocator_type, &ExpireTNode::pool>(
            parent, branch, index, cache_node, std::move(node));
    }
};

static_assert(sizeof(ExpireTNode) == 40);
static_assert(alignof(ExpireTNode) == 8);

MONAD_MPT_NAMESPACE_END

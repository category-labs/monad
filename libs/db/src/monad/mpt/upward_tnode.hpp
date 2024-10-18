#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/mem/allocators.hpp>

#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/util.hpp>

#include <optional>

MONAD_MPT_NAMESPACE_BEGIN

enum class tnode_type : uint8_t
{
    update,
    compact,
    expire
};

struct UpwardTreeNode
{
    UpwardTreeNode *parent{nullptr};
    tnode_type type{tnode_type::update};
    uint8_t npending{0};
    uint8_t branch{INVALID_BRANCH};
    uint16_t mask{0};
    uint16_t orig_mask{0};
    // tnode owns old node's lifetime only when old is leaf node, as
    // opt_leaf_data has to be valid in memory when it works the way back to
    // recompute leaf data
    Node::UniquePtr old{};
    allocators::owning_span<ChildData> children{};
    Nibbles path{};
    std::optional<byte_string_view> opt_leaf_data{std::nullopt};
    int64_t version{0};

    [[nodiscard]] unsigned number_of_children() const
    {
        return static_cast<unsigned>(std::popcount(mask));
    }

    constexpr uint8_t child_index() const noexcept
    {
        MONAD_ASSERT(parent != nullptr);
        return static_cast<uint8_t>(bitmask_index(parent->orig_mask, branch));
    }

    bool is_sentinel() const noexcept
    {
        return !parent;
    }

    using allocator_type = allocators::malloc_free_allocator<UpwardTreeNode>;

    static allocator_type &pool()
    {
        static allocator_type v;
        return v;
    }

    using unique_ptr_type = std::unique_ptr<
        UpwardTreeNode, allocators::unique_ptr_allocator_deleter<
                            allocator_type, &UpwardTreeNode::pool>>;

    static unique_ptr_type make(UpwardTreeNode v)
    {
        return allocators::
            allocate_unique<allocator_type, &UpwardTreeNode::pool>(
                std::move(v));
    }
};

using tnode_unique_ptr = UpwardTreeNode::unique_ptr_type;

inline tnode_unique_ptr make_tnode(
    uint16_t const orig_mask, UpwardTreeNode *const parent = nullptr,
    uint8_t const branch = INVALID_BRANCH, NibblesView const path = {},
    int64_t const version = 0,
    std::optional<byte_string_view> const opt_leaf_data = std::nullopt,
    Node::UniquePtr old = {})
{
    uint8_t const n = static_cast<uint8_t>(std::popcount(orig_mask));
    return UpwardTreeNode::make(UpwardTreeNode{
        .parent = parent,
        .type = tnode_type::update,
        .npending = n,
        .branch = branch,
        .mask = orig_mask,
        .orig_mask = orig_mask,
        .old = std::move(old),
        .children = allocators::owning_span<ChildData>{n},
        .path = path,
        .opt_leaf_data = opt_leaf_data,
        .version = version});
}

static_assert(sizeof(UpwardTreeNode) == 88);
static_assert(alignof(UpwardTreeNode) == 8);

struct CompactTNode
{
    // parent can be of any of the three TNode types
    CompactTNode *parent{nullptr};
    tnode_type type{tnode_type::compact};
    uint8_t npending{0};
    uint8_t index{INVALID_BRANCH}; // of parent
    bool rewrite_to_fast{false};
    bool cached{true}; // cache the owned node
    Node::UniquePtr node{nullptr};

    CompactTNode(
        CompactTNode *const parent, unsigned const index, Node::UniquePtr ptr)
        : parent(parent)
        , type(tnode_type::compact)
        , npending(ptr ? static_cast<uint8_t>(ptr->number_of_children()) : 0)
        , index(static_cast<uint8_t>(index))
        , node(std::move(ptr))
    {
    }

    void update_after_async_read(Node::UniquePtr ptr)
    {
        npending = static_cast<uint8_t>(ptr->number_of_children());
        node = std::move(ptr);
        /* Should always cache the compacted node who is child of an update
           tnode, because there is a corner case where update tnode only has
           single child left after applying all updates, but if not cached, then
           that single child may have been compacted and deallocated from memory
           but not yet landed on disk (either in write buffer or inflight for
           write), thus `cached` value is either the node is currently cached in
           memory or its node is child of an update tnode. */
        cached = parent->type == tnode_type::update;
    }

    bool is_sentinel() const noexcept
    {
        return !parent;
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

    static unique_ptr_type
    make(CompactTNode *const parent, unsigned const index, Node::UniquePtr node)
    {
        MONAD_DEBUG_ASSERT(parent);
        return allocators::allocate_unique<allocator_type, &CompactTNode::pool>(
            parent, index, std::move(node));
    }
};

static_assert(sizeof(CompactTNode) == 24);
static_assert(alignof(CompactTNode) == 8);

struct ExpireTNode
{
    // parent can be `UpdateTNode` or `ExpireTNode`, will never be
    // `CompactTNode`
    ExpireTNode *parent{nullptr};
    tnode_type type{tnode_type::expire};
    uint8_t npending{0};
    uint8_t branch{INVALID_BRANCH};
    uint16_t mask{0};
    // above must be the same as UpwardTreeNode
    uint8_t index{INVALID_BRANCH};
    bool cached{true};
    // mask indicate which child to cache, by orig child index
    uint16_t cache_mask{0};
    Node::UniquePtr node{nullptr};

    ExpireTNode(
        ExpireTNode *const parent, unsigned const branch, unsigned const index,
        Node::UniquePtr ptr)
        : parent(parent)
        , npending(ptr ? static_cast<uint8_t>(ptr->number_of_children()) : 0)
        , branch(static_cast<uint8_t>(branch))
        , mask(ptr ? ptr->mask : 0)
        , index(static_cast<uint8_t>(index))
        , node(std::move(ptr))
    {
    }

    void update_after_async_read(Node::UniquePtr ptr)
    {
        npending = static_cast<uint8_t>(ptr->number_of_children());
        mask = ptr->mask;
        node = std::move(ptr);
        // See note in CompactTNode above
        cached = parent->type == tnode_type::update;
    }

    bool is_sentinel() const noexcept
    {
        return !parent;
    }

    using allocator_type = allocators::malloc_free_allocator<ExpireTNode>;

    static allocator_type &pool()
    {
        static allocator_type v;
        return v;
    }

    using unique_ptr_type = std::unique_ptr<
        ExpireTNode, allocators::unique_ptr_allocator_deleter<
                         allocator_type, &ExpireTNode::pool>>;

    static unique_ptr_type make(ExpireTNode v)
    {
        return allocators::allocate_unique<allocator_type, &ExpireTNode::pool>(
            std::move(v));
    }

    static unique_ptr_type make(
        ExpireTNode *const parent, unsigned const branch, unsigned index,
        Node::UniquePtr node)
    {
        MONAD_DEBUG_ASSERT(parent);
        return allocators::allocate_unique<allocator_type, &ExpireTNode::pool>(
            parent, branch, index, std::move(node));
    }
};

static_assert(sizeof(ExpireTNode) == 32);
static_assert(alignof(ExpireTNode) == 8);

MONAD_MPT_NAMESPACE_END

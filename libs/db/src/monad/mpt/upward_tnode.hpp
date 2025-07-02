#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/mem/allocators.hpp>

#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/util.hpp>

#include <optional>
#include <vector>

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

template <class T>
concept update_or_expire_tnode =
    std::same_as<T, ExpireTNode> || std::same_as<T, UpdateTNode>;

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

template <update_or_expire_tnode Derived>
struct UpdateExpireCommonStorage : public UpwardTreeNodeBase<Derived>
{
    using Base = UpwardTreeNodeBase<Derived>;
    uint8_t const branch{INVALID_BRANCH};
    uint16_t mask{0};

    UpdateExpireCommonStorage(
        Derived *const parent, tnode_type const type, uint8_t const npending,
        uint8_t branch, uint16_t const mask)
        : Base(parent, type, npending)
        , branch(branch)
        , mask(mask)
    {
    }
};

struct UpdateTNode : public UpdateExpireCommonStorage<UpdateTNode>
{
    using Base = UpdateExpireCommonStorage<UpdateTNode>;
    uint16_t orig_mask{0};
    // UpdateTNode owns old node's lifetime only when old is leaf node, as
    // opt_leaf_data has to be valid in memory when it works the way back to
    // recompute leaf data
    Node::UniquePtr old{};
    std::vector<ChildData> children{};
    Nibbles path{};
    std::optional<byte_string_view> opt_leaf_data{std::nullopt};
    int64_t version{0};

    UpdateTNode(
        uint16_t const orig_mask, UpdateTNode *const parent = nullptr,
        uint8_t const branch = INVALID_BRANCH, NibblesView const path = {},
        int64_t const version = 0,
        std::optional<byte_string_view> const opt_leaf_data = std::nullopt,
        Node::UniquePtr old = {})
        : Base(
              parent, tnode_type::update,
              static_cast<uint8_t>(std::popcount(orig_mask)), branch, orig_mask)
        , orig_mask(orig_mask)
        , old(std::move(old))
        , children(npending)
        , path(path)
        , opt_leaf_data(opt_leaf_data)
        , version(version)
    {
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
    int64_t const version = 0,
    std::optional<byte_string_view> const opt_leaf_data = std::nullopt,
    Node::UniquePtr old = {})
{
    return UpdateTNode::make(
        UpdateTNode{
            orig_mask,
            parent,
            branch,
            path,
            version,
            opt_leaf_data,
            std::move(old)});
}

static_assert(sizeof(UpdateTNode) == 96);
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
        MONAD_ASSERT(parent != nullptr);
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

struct ExpireTNode : public UpdateExpireCommonStorage<ExpireTNode>
{
    using Base = UpdateExpireCommonStorage<ExpireTNode>;

    uint8_t const index{INVALID_BRANCH};
    /* Cache the recreated node after this struct is destroyed.
    Similar reason to what is noted above in CompactTNode, the expiring
    branch can end up being the only child after applying updates, thus
    always need to be cached if it is a child of UpdateTNode. */
    bool const cache_node{false};
    // A mask of which child to cache, each bit is a child of original node
    uint16_t cache_mask{0};
    Node::UniquePtr node{nullptr};

    template <update_or_expire_tnode Parent>
    ExpireTNode(
        Parent *const parent, unsigned const branch, unsigned const index,
        Node::UniquePtr ptr)
        : Base(
              (ExpireTNode *)parent, tnode_type::expire,
              ptr ? static_cast<uint8_t>(ptr->number_of_children()) : 0,
              static_cast<uint8_t>(branch), ptr ? ptr->mask : 0)
        , index(static_cast<uint8_t>(index))
        , cache_node(parent->type == tnode_type::update || ptr != nullptr)
        , node(std::move(ptr))
    {
        MONAD_ASSERT(parent != nullptr);
    }

    void update_after_async_read(Node::UniquePtr ptr)
    {
        npending = static_cast<uint8_t>(ptr->number_of_children());
        mask = ptr->mask;
        node = std::move(ptr);
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

    template <update_or_expire_tnode Parent>
    static unique_ptr_type make(
        Parent *const parent, unsigned const branch, unsigned index,
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

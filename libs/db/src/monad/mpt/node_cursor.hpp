#pragma once
#include <monad/mpt/config.hpp>
#include <monad/mpt/node.hpp>

#include <cstdint>

MONAD_MPT_NAMESPACE_BEGIN

struct NodeCursor
{
    Node *node{nullptr};
    unsigned prefix_index{0};

    constexpr NodeCursor()
        : node{nullptr}
        , prefix_index{0}
    {
    }

    constexpr NodeCursor(Node &node_, unsigned prefix_index_)
        : node{&node_}
        , prefix_index{prefix_index_}
    {
    }

    constexpr NodeCursor(Node &node_)
        : NodeCursor{node_, node_.bitpacked.path_nibble_index_start}
    {
    }

    constexpr bool is_valid() const noexcept
    {
        return node != nullptr;
    }
};

static_assert(sizeof(NodeCursor) == 16);
static_assert(alignof(NodeCursor) == 8);
static_assert(std::is_trivially_copyable_v<NodeCursor> == true);

MONAD_MPT_NAMESPACE_END

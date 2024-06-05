#pragma once

#include <monad/mpt/config.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/util.hpp>

#include <cstdint>
#include <functional>

MONAD_MPT_NAMESPACE_BEGIN

struct TraverseMachine
{
    virtual void down(unsigned char branch, Node const &) = 0;
    virtual void up(unsigned char branch, Node const &) = 0;
};

namespace detail
{
    // current implementation does not contaminate triedb node caching
    template <typename VerifyVersionFunc>
    inline bool preorder_traverse_impl(
        UpdateAuxImpl &aux, unsigned char const branch, Node const &node,
        TraverseMachine &traverse, VerifyVersionFunc &&verify_func)
    {
        traverse.down(branch, node);
        for (unsigned char i = 0; i < 16; ++i) {
            if (node.mask & (1u << i)) {
                auto const idx = node.to_child_index(i);
                auto const *const next = node.next(idx);
                if (next) {
                    preorder_traverse_impl(
                        aux, i, *next, traverse, verify_func);
                    continue;
                }
                MONAD_ASSERT(aux.is_on_disk());
                // verify version before read
                if (!verify_func()) {
                    return false;
                }
                Node::UniquePtr next_disk{};
                try {
                    next_disk.reset(read_node_blocking(
                        aux.io->storage_pool(), node.fnext(idx)));
                }
                catch (std::exception const &e) { // exception implies UB
                    return false;
                }
                // verify version after read is done
                if (!verify_func()) {
                    return false;
                }
                preorder_traverse_impl(
                    aux, i, *next_disk, traverse, verify_func);
            }
        }
        traverse.up(branch, node);
        return true;
    }
}

// return value indicates if we have done the full traversal or not
template <typename VerifyVersionFunc>
inline bool preorder_traverse(
    UpdateAuxImpl &aux, Node const &node, TraverseMachine &traverse,
    VerifyVersionFunc &&verify_func)
{
    return detail::preorder_traverse_impl(
        aux, INVALID_BRANCH, node, traverse, verify_func);
}

MONAD_MPT_NAMESPACE_END

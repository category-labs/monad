#include <monad/mpt/traverse.hpp>

#include <monad/mpt/config.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/util.hpp>

MONAD_MPT_NAMESPACE_BEGIN

namespace
{
    void preorder_traverse_impl(
        UpdateAuxImpl &aux, unsigned char const branch, Node const &node,
        TraverseMachine &traverse)
    {
        traverse.down(branch, node);
        for (unsigned char i = 0; i < 16; ++i) {
            if (node.mask & (1u << i)) {
                auto const idx = node.to_child_index(i);
                auto const *const next = node.next(idx);
                if (next == nullptr) {
                    auto const next_disk = Node::UniquePtr{read_node_blocking(
                        aux.io->storage_pool(), node.fnext(idx))};
                    preorder_traverse_impl(aux, i, *next_disk, traverse);
                }
                else {
                    preorder_traverse_impl(aux, i, *next, traverse);
                }
            }
        }
        traverse.up(branch, node);
    }
}

void preorder_traverse(
    UpdateAuxImpl &aux, Node const &node, TraverseMachine &traverse)
{
    preorder_traverse_impl(aux, INVALID_BRANCH, node, traverse);
}

MONAD_MPT_NAMESPACE_END

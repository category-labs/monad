#include <monad/core/assert.h>
#include <monad/core/nibble.h>
#include <monad/mpt/config.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>

#include <bit>
#include <cassert>

MONAD_MPT_NAMESPACE_BEGIN

find_result_type
find_blocking(UpdateAuxImpl const &aux, NodeCursor root, NibblesView const key)
{
    auto g(aux.shared_lock());
    if (!root.is_valid()) {
        return {NodeCursor{}, DbError::root_node_is_null_failure};
    }
    Node *node = root.node;
    unsigned node_prefix_index = root.prefix_index;
    unsigned prefix_index = 0;
    while (prefix_index < key.nibble_size()) {
        unsigned char const nibble = key.get(prefix_index);
        if (node->path_nibble_index_end == node_prefix_index) {
            if (!(node->mask & (1u << nibble))) {
                return {
                    NodeCursor{*node, node_prefix_index},
                    DbError::branch_not_exist_failure};
            }
            // go to node's matched child
            if (!node->next(node->to_child_index(nibble))) {
                MONAD_ASSERT(aux.is_on_disk());
                auto g2(g.upgrade());
                if (g2.upgrade_was_atomic() ||
                    !node->next(node->to_child_index(nibble))) {
                    // read node if not yet in mem
                    node->set_next(
                        node->to_child_index(nibble),
                        read_node_blocking(
                            aux.io->storage_pool(),
                            node->fnext(node->to_child_index(nibble))));
                }
            }
            MONAD_ASSERT(node->next(node->to_child_index(nibble)));
            node = node->next(node->to_child_index(nibble));
            node_prefix_index = node->bitpacked.path_nibble_index_start;
            ++prefix_index;
            continue;
        }
        if (nibble != get_nibble(node->path_data(), node_prefix_index)) {
            // return the last matched node and first mismatch prefix index
            return {
                NodeCursor{*node, node_prefix_index},
                DbError::key_mismatch_failure};
        }
        // nibble is matched
        ++prefix_index;
        ++node_prefix_index;
    }
    if (node_prefix_index != node->path_nibble_index_end) {
        // prefix key exists but no leaf ends at `key`
        return {
            NodeCursor{*node, node_prefix_index},
            DbError::key_ends_earlier_than_node_failure};
    }
    return {NodeCursor{*node, node_prefix_index}, DbError::success};
}

MONAD_MPT_NAMESPACE_END

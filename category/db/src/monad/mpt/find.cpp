#include <category/core/assert.h>
#include <category/core/nibble.h>
#include <monad/mpt/config.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>

#include <bit>
#include <cassert>
#include <cstdint>

MONAD_MPT_NAMESPACE_BEGIN

find_cursor_result_type find_blocking(
    UpdateAuxImpl const &aux, NodeCursor const root, NibblesView const key,
    uint64_t const version)
{
    auto g(aux.shared_lock());
    if (!root.is_valid()) {
        return {NodeCursor{}, find_result::root_node_is_null_failure};
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
                    find_result::branch_not_exist_failure};
            }
            // go to node's matched child
            if (auto const idx = node->to_child_index(nibble);
                !node->next(idx)) {
                MONAD_ASSERT(aux.is_on_disk());
                auto g2(g.upgrade());
                if (g2.upgrade_was_atomic() || !node->next(idx)) {
                    Node::UniquePtr next_node_ondisk =
                        read_node_blocking(aux, node->fnext(idx), version);
                    if (!next_node_ondisk) {
                        return {
                            NodeCursor{}, find_result::version_no_longer_exist};
                    }
                    node->set_next(idx, std::move(next_node_ondisk));
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
                find_result::key_mismatch_failure};
        }
        // nibble is matched
        ++prefix_index;
        ++node_prefix_index;
    }
    if (node_prefix_index != node->path_nibble_index_end) {
        // prefix key exists but no leaf ends at `key`
        return {
            NodeCursor{*node, node_prefix_index},
            find_result::key_ends_earlier_than_node_failure};
    }
    return {NodeCursor{*node, node_prefix_index}, find_result::success};
}

MONAD_MPT_NAMESPACE_END

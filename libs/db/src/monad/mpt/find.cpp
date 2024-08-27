#include <monad/core/assert.h>
#include <monad/core/keccak.hpp>
#include <monad/core/nibble.h>
#include <monad/mpt/compute.hpp>
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

get_proof_result_type get_trie_proof_blocking(
    UpdateAuxImpl const &aux, NodeCursor root, NibblesView const key,
    byte_string (*compute_leaf)(NodeCursor const, NibblesView const))
{
    auto g(aux.shared_lock());
    std::vector<byte_string> proof;

    if (!root.is_valid()) {
        return {{NodeCursor{}, proof}, find_result::root_node_is_null_failure};
    }
    Node *node = root.node;
    unsigned node_prefix_index = root.prefix_index;
    unsigned prefix_index = 0;
    bool save_root_nibble = false;
    unsigned char root_nibble = 0;

    while (prefix_index < key.nibble_size()) {
        unsigned char const nibble = key.get(prefix_index);

        if (node->path_nibble_index_end == node_prefix_index) {
            // skip root node if it only has one child
            if (node->number_of_children() == 1 && prefix_index == 0) {
                save_root_nibble = true;
                root_nibble = nibble;
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
            if (!(node->mask & (1u << nibble))) {
                return {
                    {NodeCursor{*node, node_prefix_index}, proof},
                    find_result::branch_not_exist_failure};
            }
            // if save_root_nibble, then it's extension + branch case

            // branch node
            if ((!node->has_path() || !prefix_index) && !save_root_nibble) {
                byte_string acc = (prefix_index)
                                      ? rlp_encode_branch(node)
                                      : rlp_encode_branch(node, true);
                proof.push_back(acc);
            }
            // extension + branch node
            else {
                // encode branch node
                byte_string branch = rlp_encode_branch(node);
                auto const hash = keccak256({branch.data(), branch.size()});
                // encode extesion node
                byte_string ext;
                if (save_root_nibble) {
                    ext = rlp_encode_two_pieces(
                        concat(root_nibble, node->path_nibble_view()),
                        {hash.bytes, KECCAK256_SIZE},
                        false);
                    save_root_nibble = false;
                }
                else {
                    ext = rlp_encode_two_pieces(
                        node->path_nibble_view(),
                        {hash.bytes, KECCAK256_SIZE},
                        false);
                }
                proof.push_back(ext);
                proof.push_back(branch);
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
                {NodeCursor{*node, node_prefix_index}, proof},
                find_result::key_mismatch_failure};
        }
        // nibble is matched
        ++prefix_index;
        ++node_prefix_index;
    }
    if (node_prefix_index != node->path_nibble_index_end) {
        // prefix key exists but no leaf ends at `key`
        return {
            {NodeCursor{*node, node_prefix_index}, proof},
            find_result::key_ends_earlier_than_node_failure};
    }
    // add leaf node
    MONAD_ASSERT(node->has_value());

    if (save_root_nibble) {
        proof.push_back(compute_leaf(
            NodeCursor{*node, node_prefix_index},
            concat(root_nibble, node->path_nibble_view())));
    }
    else {
        proof.push_back(compute_leaf(
            NodeCursor{*node, node_prefix_index}, node->path_nibble_view()));
    }

    return {
        {NodeCursor{*node, node_prefix_index}, proof}, find_result::success};
}

MONAD_MPT_NAMESPACE_END

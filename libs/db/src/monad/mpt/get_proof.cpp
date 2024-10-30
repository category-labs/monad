#include <monad/core/assert.h>
#include <monad/core/nibble.h>
#include <monad/mpt/config.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/util.hpp>

#include <bit>
#include <optional>

MONAD_MPT_NAMESPACE_BEGIN

namespace
{
    std::optional<unsigned char> next_branch(
        Node const &node, NibblesView const key, NibblesView const prefix)
    {
        if (key.nibble_size() < prefix.nibble_size()) {
            unsigned char branch = prefix.get(key.nibble_size());
            if (node.mask & (1u << branch)) {
                return branch;
            }
        }
        return {};
    }
}

get_proof_result_type get_proof_blocking(
    UpdateAuxImpl const &aux, NodeCursor root, compute_leaf_fn on_leaf,
    ProofOptions const &opts)
{
    std::vector<byte_string> proof;
    Nibbles key{};

    auto g(aux.shared_lock());

    auto load_next_node = [&](Node *node, unsigned char branch) {
        if (!node->next(node->to_child_index(branch))) {
            MONAD_ASSERT(aux.is_on_disk());
            auto g2(g.upgrade());
            if (g2.upgrade_was_atomic() ||
                !node->next(node->to_child_index(branch))) {
                // read node into mem
                node->set_next(
                    node->to_child_index(branch),
                    read_node_blocking(
                        aux.io->storage_pool(),
                        node->fnext(node->to_child_index(branch))));
            }
        }
        return node->next(node->to_child_index(branch));
    };

    if (!root.is_valid()) {
        return {key, proof};
    }

    Node *node = root.node;
    Nibbles coalesced_path;
    NibblesView compute_path;

    // User has indicated the root node is a subtrie.
    if (opts.root_is_subtrie) {
        auto const branch = next_branch(*node, key, opts.prefix);
        if (!branch) {
            return {key, proof};
        }
        Node *next = load_next_node(node, *branch);
        key = concat(NibblesView{key}, *branch);
        if (std::has_single_bit(node->mask)) {
            // case 1: subtrie has a single child. coalesce the mask nibble
            //         into the next relpath.
            coalesced_path = concat(*branch, next->path_nibble_view());
            compute_path = coalesced_path;
        }
        else {
            // case 2: subtrie has multiple children. root is just the branch
            //         encode without including the value.
            proof.emplace_back(encode_branch(node, true));
            compute_path = next->path_nibble_view();
        }
        node = next;
    }
    else {
        compute_path = node->path_nibble_view();
    }

    while (true) {
        Nibbles next_key = concat(NibblesView{key}, node->path_nibble_view());
        bool const is_extension = !node->path_nibble_view().empty();
        bool const is_branch = node->number_of_children() > 0;
        bool const is_leaf =
            !is_branch || (next_key.nibble_size() == opts.leaf_nibbles_len);

        if (is_leaf) {
            if (NibblesView{next_key}.starts_with(opts.prefix)) {
                key = std::move(next_key);
                auto const rlp =
                    encode_two_pieces(compute_path, on_leaf(*node), true);
                proof.emplace_back(std::move(rlp));
            }
            break;
        }
        else {
            MONAD_DEBUG_ASSERT(is_branch);
            if (is_extension) {
                auto [shared, lrem, rrem] =
                    consume_common_prefix(opts.prefix, next_key);
                if (lrem.empty() && rrem.empty() &&
                    shared.nibble_size() != opts.prefix.nibble_size()) {
                    break;
                }
                key = std::move(next_key);
            }

            auto const branch = next_branch(*node, key, opts.prefix);
            auto const next_data = encode_branch(node);
            if (is_extension) {
                unsigned char ref[KECCAK256_SIZE];
                unsigned const len = mpt::to_node_reference(next_data, ref);
                proof.emplace_back(encode_two_pieces(
                    compute_path, byte_string_view{ref, len}, false));
            }
            if (!branch) {
                break;
            }
            proof.emplace_back(std::move(next_data));
            key = concat(NibblesView{key}, *branch);
            node = load_next_node(node, *branch);
            compute_path = node->path_nibble_view();
        }
    }
    return {key, proof};
}

MONAD_MPT_NAMESPACE_END

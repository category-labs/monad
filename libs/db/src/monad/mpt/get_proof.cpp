#include <boost/outcome/success_failure.hpp>
#include <boost/outcome/try.hpp>
#include <monad/core/assert.h>
#include <monad/core/nibble.h>
#include <monad/mpt/config.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/util.hpp>
#include <monad/mpt2/node.hpp>
#include <monad/mpt2/rlp/item.hpp>

#include <bit>
#include <optional>

using BOOST_OUTCOME_V2_NAMESPACE::success;
using namespace MONAD_MPT2_NAMESPACE;

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

byte_string encode(Node const *const node, byte_string (*on_leaf)(Node const &))
{
    if (node->has_value() && node->value_len != 0) {
        return encode_two_pieces(
            node->path_nibble_view(), on_leaf(*node), true);
    }
    if (node->has_path()) {
        unsigned char reference[KECCAK256_SIZE];
        auto branch = encode_branch(node);
        unsigned len = to_node_reference(branch, reference);
        return encode_two_pieces(
            node->path_nibble_view(), {reference, len}, false);
    }
    return encode_branch(node);
}

byte_string encode_with_extra_nibble(
    unsigned char branch, Node const *const node,
    byte_string (*on_leaf)(Node const &))
{
    return encode_two_pieces(
        concat(branch, node->path_nibble_view()),
        node->has_value() ? on_leaf(*node) : encode_branch(node),
        node->has_value());
}

Result<void> verify_prefix_blocking(
    UpdateAuxImpl const &aux, NodeCursor root, NibblesView prefix,
    byte_string (*on_leaf)(Node const &), byte_string_view encoded_proof)
{
    BOOST_OUTCOME_TRY(
        auto const decoded_proof, rlp::decode_item(encoded_proof));
    BOOST_OUTCOME_TRY(
        auto const proof, UnwrapItemOrError<rlp::RawList>(decoded_proof));

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

    auto node = root.node;
    auto prefix_index = 0u;
    byte_string expected_child_hash;
    while (true) {
        auto branch = prefix.get(prefix_index);
        if (node->number_of_children() > 0) {
            if ((node->mask & (1 << branch)) == 0) {
                break;
            }
            if (node->number_of_children() == 1) {
                // Root node with single child
                auto next_node = load_next_node(node, branch);
                ++prefix_index;
                MONAD_ASSERT(next_node);
                auto path = next_node->path_nibble_view();
                if (path.nibble_size() >= prefix.nibble_size() - prefix_index &&
                    path.starts_with(prefix.substr(prefix_index))) {
                    auto val =
                        encode_with_extra_nibble(branch, next_node, on_leaf);
                    unsigned char buf[KECCAK256_SIZE];
                    auto len = to_node_reference(val, buf);
                    expected_child_hash = byte_string{buf, len};
                }
                break;
            }
            node = load_next_node(node, branch);
            MONAD_ASSERT(node);
            ++prefix_index;
            if (prefix_index == prefix.nibble_size() - 1u) {
                auto branch = prefix.get(prefix_index);
                if (!node->path_nibble_view().empty()) {
                    if (node->path_nibble_view().get(0) == branch) {
                        auto val = encode(node, on_leaf);
                        unsigned char buf[KECCAK256_SIZE];
                        auto len = to_node_reference(val, buf);
                        expected_child_hash = byte_string{buf, len};
                    }
                }
                else if ((node->mask & (1 << branch)) != 0) {
                    expected_child_hash =
                        node->child_data_view(node->to_child_index(branch));
                }
                break;
            }
        }
        else {
            return success();
        }
    }

    auto proof_it = proof.begin();
    prefix_index = 0;
    byte_string proof_hash;
    while (true) {
        auto branch = prefix.get(prefix_index);
        BOOST_OUTCOME_TRY(
            auto const &proof_node, UnwrapItemOrError<rlp::RawList>(*proof_it));
        if (is_branch_node(proof_node)) {
            auto const &child = proof_node[branch];
            BOOST_OUTCOME_TRY(
                auto const child_hash,
                UnwrapItemOrError<rlp::RawString>(child));
            if (child_hash.size() == 0) {
                break;
            }
        }
        else {
            BOOST_OUTCOME_TRY(
                auto const encoded_path,
                UnwrapItemOrError<rlp::RawString>(proof_node[0]));
            auto path = decode_path(encoded_path);
            if (path.nibble_size() >= prefix.nibble_size() - prefix_index &&
                path.starts_with(prefix.substr(prefix_index))) {
                proof_hash = rlp::to_node_reference(*proof_it);
            }
            break;
        }
        ++prefix_index;
        ++proof_it;
        if (prefix_index == prefix.nibble_size() - 1u) {
            BOOST_OUTCOME_TRY(
                auto const &proof_node,
                UnwrapItemOrError<rlp::RawList>(*proof_it));
            auto branch = prefix.get(prefix_index);
            if (is_branch_node(proof_node)) {
                auto const &child = proof_node[branch];
                BOOST_OUTCOME_TRY(
                    auto const child_hash,
                    UnwrapItemOrError<rlp::RawString>(child));
                if (child_hash.size() == 0) {
                    break;
                }
                if (child_hash.size() != KECCAK256_SIZE) {
                    return ProofError::UnexpectedType;
                }
                proof_hash = child_hash;
            }
            else {
                BOOST_OUTCOME_TRY(
                    auto encoded_path,
                    UnwrapItemOrError<rlp::RawString>(proof_node[0]));
                auto path = decode_path(encoded_path);
                if (path.get(0) == branch) {
                    proof_hash = rlp::to_node_reference(*proof_it);
                }
            }
            break;
        }
    }
    if (proof_hash != expected_child_hash) {
        return ProofError::WrongMerkleProof;
    }

    return success();
}

std::vector<byte_string> get_proof_blocking(
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
        return {};
    }

    Node *node = root.node;

    bool at_root = true;

    while (true) {
        bool is_extension = node->has_path();
        Nibbles next_key = concat(NibblesView{key}, node->path_nibble_view());
        if (at_root && opts.root_is_subtrie) {
            if (node->number_of_children() == 0) {
                unsigned char s[] = {RLP_EMPTY_STRING};
                proof.emplace_back(byte_string{s, 1});
                break;
            }
            else if (node->number_of_children() == 1) {
                // subtrie has a single child. coalesce the mask nibble into the
                // next relpath.
                auto branch =
                    static_cast<unsigned char>(std::countr_zero(node->mask));
                auto next_node = load_next_node(node, branch);
                proof.emplace_back(
                    encode_with_extra_nibble(branch, next_node, on_leaf));
                next_key =
                    concat(next_key, branch, next_node->path_nibble_view());
                node = next_node;
                is_extension = true;
            }
            else {
                proof.emplace_back(encode_branch(node, true));
            }
        }
        else {
            proof.emplace_back(encode(node, on_leaf));
        }

        if (node->number_of_children() == 0) {
            break;
        }
        else {
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

            if (!branch) {
                break;
            }
            auto child_index = node->to_child_index(*branch);
            if (node->child_data_len(child_index) < KECCAK256_SIZE) {
                // child data is the branch data
                break;
            }
            byte_string child_data{node->child_data_view(child_index)};
            key = concat(NibblesView{key}, *branch);
            node = load_next_node(node, *branch);
        }
        at_root = false;
    }

    return proof;
}

MONAD_MPT_NAMESPACE_END

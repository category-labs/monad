#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/nibble.h>
#include <monad/mpt/config.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/util.hpp>

#include <array>
#include <cassert>
#include <cstdint>
#include <limits>
#include <optional>
#include <utility>

MONAD_MPT_NAMESPACE_BEGIN

Node::UniquePtr copy_node(
    UpdateAuxImpl &aux, Node::UniquePtr root, NibblesView const src,
    NibblesView const dest)
{
    auto [src_leaf_it, res] = find_blocking(aux, *root, src);
    auto *src_leaf = src_leaf_it.node;
    MONAD_ASSERT(res == find_result::success);
    auto impl = [&]() -> Node::UniquePtr {
        Node *parent = nullptr;
        Node *node = root.get();
        Node *new_node = nullptr;
        unsigned prefix_index = 0;
        unsigned node_prefix_index = root->bitpacked.path_nibble_index_start;
        unsigned char branch_i = INVALID_BRANCH;

        // Disconnect src_leaf's children
        // Insert `dest` to trie, the node created will need to have the same
        // children as node at `src`
        while (prefix_index < dest.nibble_size()) {
            unsigned char const nibble = dest.get(prefix_index);
            if (node->path_nibble_index_end == node_prefix_index) {
                if (node->mask & (1u << nibble) &&
                    node->next(node->to_child_index(nibble)) != nullptr) {
                    // go to node's matched child
                    parent = node;
                    branch_i = nibble;
                    node = node->next(node->to_child_index(nibble));
                    node_prefix_index = node->bitpacked.path_nibble_index_start;
                    ++prefix_index;
                    continue;
                }
                // add a branch = nibble to new_node
                new_node = [&]() -> Node * {
                    MONAD_DEBUG_ASSERT(
                        prefix_index <
                        std::numeric_limits<unsigned char>::max());
                    Node *leaf =
                        make_node(
                            *src_leaf,
                            dest.substr(
                                static_cast<unsigned char>(prefix_index) + 1u),
                            src_leaf->value(),
                            src_leaf->version)
                            .release();
                    // create a node, with no leaf data
                    uint16_t const mask =
                        static_cast<uint16_t>(node->mask | (1u << nibble));
                    std::array<ChildData, 16> children;
                    for (uint8_t i = 0; i < 16; ++i) {
                        if (i == nibble) {
                            children[i].branch = i;
                            children[i].ptr = leaf;
                        }
                        else if (mask & (1u << i)) {
                            children[i].branch = i;
                            auto const old_index = node->to_child_index(i);
                            if (aux.is_on_disk()) {
                                children[i].min_offset_fast =
                                    node->min_offset_fast(old_index);
                                children[i].min_offset_slow =
                                    node->min_offset_slow(old_index);
                                children[i].offset = node->fnext(old_index);
                                node->next_ptr(old_index).reset();
                            }
                            else {
                                children[i].ptr =
                                    node->next_ptr(old_index).release();
                            }
                        }
                    }
                    return make_node(
                               mask,
                               children,
                               node->path_nibble_view(),
                               std::nullopt,
                               0,
                               leaf->version)
                        .release();
                }();
                break;
            }
            auto const node_nibble =
                get_nibble(node->path_data(), node_prefix_index);
            if (nibble == node_nibble) {
                ++prefix_index;
                ++node_prefix_index;
                continue;
            }
            // mismatch: split node's path: turn node to a branch node with two
            // children
            new_node = [&]() -> Node * {
                MONAD_DEBUG_ASSERT(
                    prefix_index < std::numeric_limits<unsigned char>::max());
                Node *dest_leaf =
                    make_node(
                        *src_leaf,
                        dest.substr(
                            static_cast<unsigned char>(prefix_index) + 1u),
                        src_leaf->value(),
                        src_leaf->version)
                        .release();
                Node *node_latter_half =
                    make_node(
                        *node,
                        NibblesView{
                            node_prefix_index + 1,
                            node->path_nibble_index_end,
                            node->path_data()},
                        node->has_value()
                            ? std::optional<byte_string_view>{node->value()}
                            : std::nullopt,
                        node->version)
                        .release();
                MONAD_DEBUG_ASSERT(node_latter_half);
                uint16_t const mask =
                    static_cast<uint16_t>((1u << nibble) | (1u << node_nibble));
                bool const leaf_first = nibble < node_nibble;
                ChildData children[2];
                children[!leaf_first] =
                    ChildData{.ptr = dest_leaf, .branch = node_nibble};
                children[leaf_first] =
                    ChildData{.ptr = node_latter_half, .branch = nibble};
                if (aux.is_on_disk()) {
                    // Request a write for the modified node, async_write_node()
                    // serialize nodes to buffer but it's not guaranteed to land
                    // on disk immediately because the buffer will only be
                    // flushed to disk when full or close to full. To avoid
                    // reading from offset that is still pending on write, we
                    // always cache `node_latter_half` in memory here. TODO once
                    // we enable the write back cache, we can unpin the node
                    // from memory no problem.
                    children[leaf_first].offset = async_write_node_set_spare(
                        aux, *node_latter_half, true);
                }
                return make_node(
                           mask,
                           std::span(children),
                           NibblesView{
                               node->bitpacked.path_nibble_index_start,
                               node_prefix_index,
                               node->path_data()},
                           std::nullopt,
                           0,
                           dest_leaf->version)
                    .release();
            }();
            break;
        }
        if (prefix_index ==
            dest.nibble_size()) { // found an existing dest leaf in memory
            // node is the dest_leaf, need to recreate new_node to have the same
            // children as src_leaf, then deallocate the existing one
            MONAD_DEBUG_ASSERT(new_node == nullptr);
            MONAD_DEBUG_ASSERT(node != root.get());
            new_node = make_node(
                           *src_leaf,
                           node->path_nibble_view(),
                           src_leaf->value(),
                           src_leaf->version)
                           .release();
            // clear parent's children other than new_node
            if (aux.is_on_disk()) {
                for (unsigned j = 0; j < parent->number_of_children(); ++j) {
                    if (j != parent->to_child_index(branch_i)) {
                        parent->next_ptr(j).reset();
                    };
                }
            }
        }
        // deallocate previous child at branch i
        if (parent) {
            auto const child_index = parent->to_child_index(branch_i);
            parent->next_ptr(child_index).reset(); // deallocate child (= node)
            parent->set_next(child_index, new_node);
        }
        else {
            MONAD_DEBUG_ASSERT(node == root.get());
            root = Node::UniquePtr{new_node}; // deallocate root (= node)
        }
        return std::move(root);
    };
    if (aux.is_current_thread_upserting()) {
        return impl();
    }
    else {
        auto g(aux.unique_lock());
        return impl();
    }
}

MONAD_MPT_NAMESPACE_END

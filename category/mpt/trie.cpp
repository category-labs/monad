// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/mpt/trie.hpp>

#include <category/async/concepts.hpp>
#include <category/async/config.hpp>
#include <category/async/erased_connected_operation.hpp>
#include <category/async/io_senders.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/nibble.h>
#include <category/mpt/config.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/request.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/update.hpp>
#include <category/mpt/upward_tnode.hpp>
#include <category/mpt/util.hpp>

#include <quill/Quill.h>

#include <algorithm>
#include <bit>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <limits>
#include <memory>
#include <optional>
#include <span>
#include <tuple>
#include <utility>
#include <vector>

#include "deserialize_node_from_receiver_result.hpp"

MONAD_MPT_NAMESPACE_BEGIN

using namespace MONAD_ASYNC_NAMESPACE;

/* Names: `prefix_index` is nibble index in prefix of an update,
 `old_prefix_index` is nibble index of path in previous node - old.
 `*_prefix_index_start` is the starting nibble index in current function frame
*/
void dispatch_updates_impl_(
    UpdateAuxImpl &, StateMachine &, UpdateTNode &parent, ChildData &,
    Node::SharedPtr old, Requests &, unsigned prefix_index, NibblesView path,
    std::optional<byte_string_view> opt_leaf_data, int64_t version);

void mismatch_handler_(
    UpdateAuxImpl &, StateMachine &, UpdateTNode &parent, ChildData &,
    Node::SharedPtr old, Requests &, NibblesView path,
    unsigned old_prefix_index, unsigned prefix_index);

void create_new_trie_(
    UpdateAuxImpl &aux, StateMachine &sm, int64_t &parent_version,
    ChildData &entry, UpdateList &&updates, unsigned prefix_index = 0);

void create_new_trie_from_requests_(
    UpdateAuxImpl &, StateMachine &, int64_t &parent_version, ChildData &,
    Requests &, NibblesView path, unsigned prefix_index,
    std::optional<byte_string_view> opt_leaf_data, int64_t version);

void upsert_(
    UpdateAuxImpl &, StateMachine &, UpdateTNode &parent, ChildData &,
    Node::SharedPtr old, chunk_offset_t offset, UpdateList &&,
    unsigned prefix_index = 0, unsigned old_prefix_index = 0);

void create_node_compute_data_possibly_async(
    UpdateAuxImpl &, StateMachine &, UpdateTNode &parent, ChildData &,
    tnode_unique_ptr, bool might_on_disk = true);

void compact_(
    UpdateAuxImpl &, StateMachine &, CompactTNode::unique_ptr_type,
    chunk_offset_t node_offset, bool copy_node_for_fast_or_slow);

void expire_(
    UpdateAuxImpl &, StateMachine &, ExpireTNode::unique_ptr_type,
    chunk_offset_t node_offset);

void try_fillin_parent_with_rewritten_node(
    UpdateAuxImpl &, CompactTNode::unique_ptr_type);

void try_fillin_parent_after_expiration(
    UpdateAuxImpl &, StateMachine &, ExpireTNode::unique_ptr_type);

void fillin_parent_after_expiration(
    UpdateAuxImpl &, Node::SharedPtr, ExpireTNode *const, uint8_t const index,
    uint8_t const branch, bool const cache_node);

struct async_write_node_result
{
    chunk_offset_t offset_written_to;
    unsigned bytes_appended;
};

// invoke at the end of each block upsert
void flush_buffered_writes(UpdateAuxImpl &);
chunk_offset_t
write_new_root_node(UpdateAuxImpl &, Node::SharedPtr const &, uint64_t);

Node::SharedPtr upsert(
    UpdateAuxImpl &aux, uint64_t const version, StateMachine &sm,
    Node::SharedPtr old, UpdateList &&updates, bool const write_root)
{
    aux.reset_stats();
    auto sentinel = make_tnode(1 /*mask*/);
    ChildData &entry = sentinel->children[0];
    sentinel->children[0] = ChildData{.branch = 0};
    if (old) {
        if (updates.empty()) {
            auto const old_path = old->path_nibble_view();
            auto const old_path_nibbles_len = old_path.nibble_size();
            for (unsigned n = 0; n < old_path_nibbles_len; ++n) {
                sm.down(old_path.get(n));
            }
            // simply dispatch empty update and potentially do compaction
            Requests requests;
            Node const &old_node = *old;
            dispatch_updates_impl_(
                aux,
                sm,
                *sentinel,
                entry,
                std::move(old),
                requests,
                old_path_nibbles_len,
                old_path,
                old_node.opt_value(),
                old_node.version);
            sm.up(old_path_nibbles_len);
        }
        else {
            upsert_(
                aux,
                sm,
                *sentinel,
                entry,
                std::move(old),
                INVALID_OFFSET,
                std::move(updates));
        }
        if (sentinel->npending) {
            aux.io->flush();
            MONAD_ASSERT(sentinel->npending == 0);
        }
    }
    else {
        create_new_trie_(aux, sm, sentinel->version, entry, std::move(updates));
    }
    auto root = entry.ptr;
    if (aux.is_on_disk() && root) {
        if (write_root) {
            write_new_root_node(aux, root, version);
        }
        else {
            flush_buffered_writes(aux);
        }
    }
    return root;
}

struct load_all_impl_
{
    UpdateAuxImpl &aux;

    size_t nodes_loaded{0};

    struct receiver_t
    {
        static constexpr bool lifetime_managed_internally = true;

        load_all_impl_ *impl;
        NodeCursor root;
        unsigned const branch_index;
        std::unique_ptr<StateMachine> sm;

        chunk_offset_t rd_offset{0, 0};
        unsigned bytes_to_read;
        uint16_t buffer_off;

        receiver_t(
            load_all_impl_ *impl, NodeCursor root, unsigned char const branch,
            std::unique_ptr<StateMachine> sm)
            : impl(impl)
            , root(root)
            , branch_index(branch)
            , sm(std::move(sm))
        {
            chunk_offset_t const offset = root.node->fnext(branch_index);
            auto const num_pages_to_load_node =
                node_disk_pages_spare_15{offset}.to_pages();
            bytes_to_read =
                static_cast<unsigned>(num_pages_to_load_node << DISK_PAGE_BITS);
            rd_offset = offset;
            auto const new_offset =
                round_down_align<DISK_PAGE_BITS>(offset.offset);
            MONAD_DEBUG_ASSERT(new_offset <= chunk_offset_t::max_offset);
            rd_offset.offset = new_offset & chunk_offset_t::max_offset;
            buffer_off = uint16_t(offset.offset - rd_offset.offset);
        }

        template <class ResultType>
        void set_value(erased_connected_operation *io_state, ResultType buffer_)
        {
            MONAD_ASSERT(buffer_);
            // load node from read buffer
            {
                MONAD_ASSERT(root.node->next(branch_index) == nullptr);
                root.node->set_next(
                    branch_index,
                    detail::deserialize_node_from_receiver_result(
                        std::move(buffer_), buffer_off, io_state));
                impl->nodes_loaded++;
            }
            impl->process(NodeCursor{root.node->next(branch_index)}, *sm);
        }
    };

    explicit constexpr load_all_impl_(UpdateAuxImpl &aux)
        : aux(aux)
    {
    }

    void process(NodeCursor const &node_cursor, StateMachine &sm)
    {
        auto node = node_cursor.node;
        for (auto const [idx, i] : NodeChildrenRange(node->mask)) {
            NibblesView const nv =
                node->path_nibble_view().substr(node_cursor.prefix_index);
            for (uint8_t n = 0; n < nv.nibble_size(); n++) {
                sm.down(nv.get(n));
            }
            sm.down(i);
            if (sm.cache()) {
                auto next = node->next(idx);
                if (next == nullptr) {
                    receiver_t receiver(
                        this, NodeCursor{node}, uint8_t(idx), sm.clone());
                    async_read(aux, std::move(receiver));
                }
                else {
                    process(NodeCursor{std::move(next)}, sm);
                }
            }
            sm.up(1 + nv.nibble_size());
        }
    }
};

size_t load_all(UpdateAuxImpl &aux, StateMachine &sm, NodeCursor const &root)
{
    load_all_impl_ impl(aux);
    impl.process(root, sm);
    aux.io->wait_until_done();
    return impl.nodes_loaded;
}

/////////////////////////////////////////////////////
// Async read and update
/////////////////////////////////////////////////////

// Upward update until a unfinished parent node. For each tnode, create the
// trie Node when all its children are created
void upward_update(UpdateAuxImpl &aux, StateMachine &sm, UpdateTNode *tnode)
{
    while (!tnode->npending && tnode->parent) {
        MONAD_DEBUG_ASSERT(tnode->children.size()); // not a leaf
        auto *parent = tnode->parent;
        auto &entry = parent->children[tnode->child_index()];
        // put created node and compute to entry in parent
        size_t const level_up =
            tnode->path.nibble_size() + !parent->is_sentinel();
        create_node_compute_data_possibly_async(
            aux, sm, *parent, entry, tnode_unique_ptr{tnode});
        sm.up(level_up);
        tnode = parent;
    }
}

template <typename Cont>
struct node_receiver_t
{
public:
    static constexpr bool lifetime_managed_internally = true;

    Cont cont;

    // part of the receiver trait
    chunk_offset_t rd_offset;
    uint16_t buffer_offset{};
    unsigned bytes_to_read{};

    node_receiver_t(Cont cont_, chunk_offset_t const offset_)
        : cont(std::move(cont_))
        , rd_offset{round_down_align<DISK_PAGE_BITS>(offset_)}
        , buffer_offset{
              static_cast<uint16_t>(offset_.offset - rd_offset.offset)}
    {
        auto const pages = node_disk_pages_spare_15{rd_offset}.to_pages();
        bytes_to_read = static_cast<unsigned>(pages << DISK_PAGE_BITS);
        rd_offset.set_spare(0);
    }

    template <typename Result>
    void set_value(erased_connected_operation *io_state_, Result buffer_)
    {
        MONAD_ASSERT(buffer_);
        auto as_node = detail::deserialize_node_from_receiver_result(
            std::move(buffer_), buffer_offset, io_state_);
        cont(std::move(as_node));
    }
};

/////////////////////////////////////////////////////
// Create Node
/////////////////////////////////////////////////////

std::pair<bool, Node::SharedPtr> create_node_with_expired_branches(
    UpdateAuxImpl &aux, StateMachine &sm, ExpireTNode::unique_ptr_type tnode)
{
    MONAD_ASSERT(tnode->node);
    // no recomputation of data
    // all children should still be in memory, this function is responsible for
    // deallocating them per state machine cache() output.
    // if single child, coelease branch nibble with single child's path
    if (tnode->mask == 0) {
        return {true, nullptr};
    }
    auto const mask = tnode->mask;
    auto &orig = tnode->node;
    auto const number_of_children = static_cast<size_t>(std::popcount(mask));
    if (number_of_children == 1 && !orig->has_value()) {
        auto const child_branch = static_cast<uint8_t>(std::countr_zero(mask));
        auto const child_index = orig->to_child_index(child_branch);
        auto single_child = orig->move_next(child_index);
        if (!single_child) {
            node_receiver_t recv{
                [aux = &aux,
                 sm = sm.clone(),
                 tnode = std::move(tnode),
                 child_branch](Node::SharedPtr read_node) mutable {
                    auto new_node = make_node(
                        *read_node,
                        concat(
                            tnode->node->path_nibble_view(),
                            child_branch,
                            read_node->path_nibble_view()),
                        read_node->opt_value(),
                        read_node->version);
                    fillin_parent_after_expiration(
                        *aux,
                        std::move(new_node),
                        tnode->parent,
                        tnode->index,
                        tnode->branch,
                        tnode->cache_node);
                    // upward update
                    auto *parent = tnode->parent;
                    while (!parent->npending) {
                        if (parent->type == tnode_type::update) {
                            upward_update(*aux, *sm, (UpdateTNode *)parent);
                            return;
                        }
                        auto *next_parent = parent->parent;
                        MONAD_ASSERT(next_parent);
                        try_fillin_parent_after_expiration(
                            *aux, *sm, ExpireTNode::unique_ptr_type{parent});
                        // go one level up
                        parent = next_parent;
                    }
                },
                orig->fnext(child_index)};
            async_read(aux, std::move(recv));
            return {false, nullptr};
        }
        return {
            true,
            make_node(
                *single_child,
                concat(
                    orig->path_nibble_view(),
                    child_branch,
                    single_child->path_nibble_view()),
                single_child->opt_value(),
                single_child->version)};
    }
    uint16_t total_child_data_size = 0;
    // no need to update version (max of children or itself)
    std::vector<unsigned> orig_indexes;
    std::vector<uint16_t> child_data_offsets;
    orig_indexes.reserve(number_of_children);
    child_data_offsets.reserve(number_of_children);
    for (auto const [orig_index, branch] : NodeChildrenRange(orig->mask)) {
        if (mask & (1u << branch)) {
            orig_indexes.push_back(orig_index);
            total_child_data_size += (uint16_t)orig->child_data_len(orig_index);
            child_data_offsets.push_back(total_child_data_size);
        }
    }
    auto node = Node::make(
        calculate_node_size(
            number_of_children,
            total_child_data_size,
            orig->value_len,
            orig->path_bytes(),
            orig->bitpacked.data_len),
        mask,
        orig->opt_value(),
        (size_t)orig->bitpacked.data_len,
        orig->path_nibble_view(),
        orig->version);

    std::copy_n(
        (byte_string_view::pointer)child_data_offsets.data(),
        child_data_offsets.size() * sizeof(uint16_t),
        node->child_off_data());

    // Must initialize child pointers after copying child_data_offset
    for (unsigned i = 0; i < node->number_of_children(); ++i) {
        new (node->child_ptr(i)) Node::SharedPtr();
    }
    for (unsigned j = 0; j < number_of_children; ++j) {
        auto const &orig_j = orig_indexes[j];
        node->set_fnext(j, orig->fnext(orig_j));
        node->set_min_offset_fast(j, orig->min_offset_fast(orig_j));
        node->set_min_offset_slow(j, orig->min_offset_slow(orig_j));
        MONAD_ASSERT(
            orig->subtrie_min_version(orig_j) >=
            aux.curr_upsert_auto_expire_version);
        node->set_subtrie_min_version(j, orig->subtrie_min_version(orig_j));
        if (tnode->cache_mask & (1u << orig_j)) {
            node->set_next(j, orig->move_next(orig_j));
        }
        node->set_child_data(j, orig->child_data_view(orig_j));
    }
    return {true, std::move(node)};
}

Node::SharedPtr create_node_from_children_if_any(
    UpdateAuxImpl &aux, StateMachine &sm, uint16_t const orig_mask,
    uint16_t const mask, std::span<ChildData> const children,
    NibblesView const path, std::optional<byte_string_view> const leaf_data,
    int64_t const version)
{
    aux.collect_number_nodes_created_stats();
    // handle non child and single child cases
    auto const number_of_children = static_cast<unsigned>(std::popcount(mask));
    if (number_of_children == 0) {
        return leaf_data.has_value()
                   ? make_node(0, {}, path, leaf_data.value(), {}, version)
                   : Node::SharedPtr{};
    }
    else if (number_of_children == 1 && !leaf_data.has_value()) {
        auto const j = bitmask_index(
            orig_mask, static_cast<unsigned>(std::countr_zero(mask)));
        MONAD_DEBUG_ASSERT(children[j].ptr);
        auto node = std::move(children[j].ptr);
        /* Note: there's a potential superfluous extension hash recomputation
        when node coaleases upon erases, because we compute node hash when path
        is not yet the final form. There's not yet a good way to avoid this
        unless we delay all the compute() after all child branches finish
        creating nodes and return in the recursion */
        return make_node(
            *node,
            concat(path, children[j].branch, node->path_nibble_view()),
            node->has_value() ? std::make_optional(node->value())
                              : std::nullopt,
            version); // node is deallocated
    }
    MONAD_DEBUG_ASSERT(
        number_of_children > 1 ||
        (number_of_children == 1 && leaf_data.has_value()));
    // write children to disk, free any if exceeds the cache level limit
    if (aux.is_on_disk()) {
        for (auto &child : children) {
            if (child.is_valid() && child.offset == INVALID_OFFSET) {
                // write updated node or node to be compacted to disk
                // won't duplicate write of unchanged old child
                MONAD_DEBUG_ASSERT(child.branch < 16);
                MONAD_DEBUG_ASSERT(child.ptr);
                child.offset = async_write_node_set_spare(aux, child.ptr, true);
                auto const child_virtual_offset =
                    aux.physical_to_virtual(child.offset);
                MONAD_DEBUG_ASSERT(
                    child_virtual_offset != INVALID_VIRTUAL_OFFSET);
                std::tie(child.min_offset_fast, child.min_offset_slow) =
                    calc_min_offsets(*child.ptr, child_virtual_offset);
                if (sm.compact()) {
                    MONAD_DEBUG_ASSERT(
                        child.min_offset_fast >= aux.compact_offset_fast);
                    MONAD_DEBUG_ASSERT(
                        child.min_offset_slow >= aux.compact_offset_slow);
                }
            }
            // apply cache based on state machine state, always cache node that
            // is a single child
            if (child.ptr && number_of_children > 1 && !child.cache_node) {
                child.ptr.reset();
            }
        }
    }
    return create_node_with_children(
        sm.get_compute(), mask, children, path, leaf_data, version);
}

void create_node_compute_data_possibly_async(
    UpdateAuxImpl &aux, StateMachine &sm, UpdateTNode &parent, ChildData &entry,
    tnode_unique_ptr tnode, bool const might_on_disk)
{
    if (might_on_disk && tnode->number_of_children() == 1) {
        auto &child = tnode->children[bitmask_index(
            tnode->orig_mask,
            static_cast<unsigned>(std::countr_zero(tnode->mask)))];
        if (!child.ptr) {
            MONAD_DEBUG_ASSERT(aux.is_on_disk());
            MONAD_ASSERT(child.offset != INVALID_OFFSET);
            { // some sanity checks
                auto const virtual_child_offset =
                    aux.physical_to_virtual(child.offset);
                MONAD_DEBUG_ASSERT(
                    virtual_child_offset != INVALID_VIRTUAL_OFFSET);
                // child offset is older than current write position
                MONAD_DEBUG_ASSERT(
                    virtual_child_offset <
                    aux.physical_to_virtual(
                        aux.writer(virtual_child_offset.in_fast_list())
                            .write_position.to_chunk_offset()));
            }
            node_receiver_t recv{
                [aux = &aux, sm = sm.clone(), tnode = std::move(tnode)](
                    Node::SharedPtr read_node) mutable {
                    auto *parent = tnode->parent;
                    MONAD_DEBUG_ASSERT(parent);
                    auto &entry = parent->children[tnode->child_index()];
                    MONAD_DEBUG_ASSERT(entry.branch < 16);
                    auto &child = tnode->children[bitmask_index(
                        tnode->orig_mask,
                        static_cast<unsigned>(std::countr_zero(tnode->mask)))];
                    child.ptr = std::move(read_node);
                    auto const path_size = tnode->path.nibble_size();
                    create_node_compute_data_possibly_async(
                        *aux, *sm, *parent, entry, std::move(tnode), false);
                    sm->up(path_size + !parent->is_sentinel());
                    upward_update(*aux, *sm, parent);
                },
                child.offset};
            async_read(aux, std::move(recv));
            MONAD_DEBUG_ASSERT(parent.npending);
            return;
        }
    }
    auto node = create_node_from_children_if_any(
        aux,
        sm,
        tnode->orig_mask,
        tnode->mask,
        tnode->children,
        tnode->path,
        tnode->opt_leaf_data,
        tnode->version);
    MONAD_DEBUG_ASSERT(entry.branch < 16);
    if (node) {
        parent.version = std::max(parent.version, node->version);
        entry.finalize(std::move(node), sm.get_compute(), sm.cache());
        if (sm.auto_expire()) {
            MONAD_ASSERT(
                entry.subtrie_min_version >=
                aux.curr_upsert_auto_expire_version);
        }
    }
    else {
        parent.mask &= static_cast<uint16_t>(~(1u << entry.branch));
        entry.erase();
    }
    --parent.npending;
}

void update_value_and_subtrie_(
    UpdateAuxImpl &aux, StateMachine &sm, UpdateTNode &parent, ChildData &entry,
    Node::SharedPtr old, NibblesView const path, Update &update)
{
    if (update.is_deletion()) {
        parent.mask &= static_cast<uint16_t>(~(1u << entry.branch));
        entry.erase();
        --parent.npending;
        return;
    }
    // No need to check next is empty or not, following branches will handle it
    Requests requests;
    requests.split_into_sublists(std::move(update.next), 0);
    MONAD_ASSERT(requests.opt_leaf == std::nullopt);
    if (update.incarnation) {
        // handles empty requests sublist too
        create_new_trie_from_requests_(
            aux,
            sm,
            parent.version,
            entry,
            requests,
            path,
            0,
            update.value,
            update.version);
        --parent.npending;
    }
    else {
        auto const opt_leaf =
            update.value.has_value() ? update.value : old->opt_value();
        MONAD_ASSERT(update.version >= old->version);
        dispatch_updates_impl_(
            aux,
            sm,
            parent,
            entry,
            std::move(old),
            requests,
            0,
            path,
            opt_leaf,
            update.version);
    }
    return;
}

/////////////////////////////////////////////////////
// Create a new trie from a list of updates, no incarnation
/////////////////////////////////////////////////////
void create_new_trie_(
    UpdateAuxImpl &aux, StateMachine &sm, int64_t &parent_version,
    ChildData &entry, UpdateList &&updates, unsigned prefix_index)
{
    if (updates.empty()) {
        return;
    }
    if (updates.size() == 1) {
        Update &update = updates.front();
        MONAD_DEBUG_ASSERT(update.value.has_value());
        auto const path = update.key.substr(prefix_index);
        for (auto i = 0u; i < path.nibble_size(); ++i) {
            sm.down(path.get(i));
        }
        MONAD_DEBUG_ASSERT(update.value.has_value());
        MONAD_ASSERT(
            !sm.is_variable_length() || update.next.empty(),
            "Invalid update detected: variable-length tables do not "
            "support updates with a next list");
        Requests requests;
        // requests would be empty if update.next is empty
        requests.split_into_sublists(std::move(update.next), 0);
        MONAD_ASSERT(requests.opt_leaf == std::nullopt);
        create_new_trie_from_requests_(
            aux,
            sm,
            parent_version,
            entry,
            requests,
            path,
            0,
            update.value,
            update.version);

        if (path.nibble_size()) {
            sm.up(path.nibble_size());
        }
        return;
    }
    // Requests contain more than 2 updates
    Requests requests;
    auto const prefix_index_start = prefix_index;
    // Iterate to find the prefix index where update paths diverge due to key
    // termination or branching
    while (true) {
        unsigned const num_branches =
            requests.split_into_sublists(std::move(updates), prefix_index);
        MONAD_ASSERT(num_branches > 0); // because updates.size() > 1
        // sanity checks on user input
        MONAD_ASSERT(
            !requests.opt_leaf || sm.is_variable_length(),
            "Invalid update input: must mark the state machine as "
            "variable-length to allow variable length updates");
        if (num_branches > 1 || requests.opt_leaf) {
            break;
        }
        sm.down(requests.get_first_branch());
        updates = std::move(requests).first_and_only_list();
        ++prefix_index;
    }
    create_new_trie_from_requests_(
        aux,
        sm,
        parent_version,
        entry,
        requests,
        requests.get_first_path().substr(
            prefix_index_start, prefix_index - prefix_index_start),
        prefix_index,
        requests.opt_leaf.and_then(&Update::value),
        requests.opt_leaf.has_value() ? requests.opt_leaf.value().version : 0);
    if (prefix_index_start != prefix_index) {
        sm.up(prefix_index - prefix_index_start);
    }
}

void create_new_trie_from_requests_(
    UpdateAuxImpl &aux, StateMachine &sm, int64_t &parent_version,
    ChildData &entry, Requests &requests, NibblesView const path,
    unsigned const prefix_index,
    std::optional<byte_string_view> const opt_leaf_data, int64_t version)
{
    // version will be updated bottom up
    uint16_t const mask = requests.mask;
    std::vector<ChildData> children(size_t(std::popcount(mask)));
    for (auto const [index, branch] : NodeChildrenRange(mask)) {
        children[index].branch = branch;
        sm.down(branch);
        create_new_trie_(
            aux,
            sm,
            version,
            children[index],
            std::move(requests)[branch],
            prefix_index + 1);
        sm.up(1);
    }
    // can have empty children
    auto node = create_node_from_children_if_any(
        aux, sm, mask, mask, children, path, opt_leaf_data, version);
    MONAD_ASSERT(node);
    parent_version = std::max(parent_version, node->version);
    entry.finalize(std::move(node), sm.get_compute(), sm.cache());
    if (sm.auto_expire()) {
        MONAD_ASSERT(
            entry.subtrie_min_version >= aux.curr_upsert_auto_expire_version);
    }
}

/////////////////////////////////////////////////////
// Update existing subtrie
/////////////////////////////////////////////////////

void upsert_(
    UpdateAuxImpl &aux, StateMachine &sm, UpdateTNode &parent, ChildData &entry,
    Node::SharedPtr old, chunk_offset_t const old_offset, UpdateList &&updates,
    unsigned prefix_index, unsigned old_prefix_index)
{
    MONAD_ASSERT(!updates.empty());
    // Variable-length tables support only a one-time insert; no deletions or
    // further updates are allowed.
    MONAD_ASSERT(
        !sm.is_variable_length(),
        "Invalid update detected: current implementation does not "
        "support updating variable-length tables");
    if (!old) {
        node_receiver_t recv{
            [aux = &aux,
             entry = &entry,
             prefix_index = prefix_index,
             sm = sm.clone(),
             parent = &parent,
             updates = std::move(updates)](Node::SharedPtr read_node) mutable {
                // continue recurse down the trie starting from `old`
                upsert_(
                    *aux,
                    *sm,
                    *parent,
                    *entry,
                    std::move(read_node),
                    INVALID_OFFSET,
                    std::move(updates),
                    prefix_index);
                sm->up(1);
                upward_update(*aux, *sm, parent);
            },
            old_offset};
        async_read(aux, std::move(recv));
        return;
    }
    MONAD_ASSERT(old_prefix_index != INVALID_PATH_INDEX);
    auto const old_prefix_index_start = old_prefix_index;
    auto const prefix_index_start = prefix_index;
    Requests requests;
    while (true) {
        NibblesView path = old->path_nibble_view().substr(
            old_prefix_index_start, old_prefix_index - old_prefix_index_start);
        if (updates.size() == 1 &&
            prefix_index == updates.front().key.nibble_size()) {
            auto &update = updates.front();
            MONAD_ASSERT(old->path_nibbles_len() == old_prefix_index);
            MONAD_ASSERT(old->has_value());
            update_value_and_subtrie_(
                aux, sm, parent, entry, std::move(old), path, update);
            break;
        }
        unsigned const number_of_sublists = requests.split_into_sublists(
            std::move(updates), prefix_index); // NOLINT
        MONAD_ASSERT(requests.mask > 0);
        if (old_prefix_index == old->path_nibbles_len()) {
            MONAD_ASSERT(
                !requests.opt_leaf.has_value(),
                "Invalid update detected: cannot apply variable-length "
                "updates to a fixed-length table in the database");
            int64_t const version = old->version;
            auto const opt_leaf_data = old->opt_value();
            dispatch_updates_impl_(
                aux,
                sm,
                parent,
                entry,
                std::move(old),
                requests,
                prefix_index,
                path,
                opt_leaf_data,
                version);
            break;
        }
        if (auto old_nibble = old->path_nibble_view().get(old_prefix_index);
            number_of_sublists == 1 &&
            requests.get_first_branch() == old_nibble) {
            MONAD_DEBUG_ASSERT(requests.opt_leaf == std::nullopt);
            updates = std::move(requests)[old_nibble];
            sm.down(old_nibble);
            ++prefix_index;
            ++old_prefix_index;
            continue;
        }
        // meet a mismatch or split, not till the end of old path
        mismatch_handler_(
            aux,
            sm,
            parent,
            entry,
            std::move(old),
            requests,
            path,
            old_prefix_index,
            prefix_index);
        break;
    }
    if (prefix_index_start != prefix_index) {
        sm.up(prefix_index - prefix_index_start);
    }
}

void fillin_entry(
    UpdateAuxImpl &aux, StateMachine &sm, tnode_unique_ptr tnode,
    UpdateTNode &parent, ChildData &entry)
{
    if (tnode->npending) {
        tnode.release();
    }
    else {
        create_node_compute_data_possibly_async(
            aux, sm, parent, entry, std::move(tnode));
    }
}

/* dispatch updates at the end of old node's path. old node may have leaf data,
 * and there might be update to the leaf value. */
void dispatch_updates_impl_(
    UpdateAuxImpl &aux, StateMachine &sm, UpdateTNode &parent, ChildData &entry,
    Node::SharedPtr old_ptr, Requests &requests, unsigned const prefix_index,
    NibblesView const path, std::optional<byte_string_view> const opt_leaf_data,
    int64_t const version)
{
    Node *old = old_ptr.get();
    uint16_t const orig_mask = old->mask | requests.mask;
    // tnode->version will be updated bottom up
    auto tnode = make_tnode(
        orig_mask,
        &parent,
        entry.branch,
        path,
        version,
        opt_leaf_data,
        opt_leaf_data.has_value() ? old_ptr : Node::SharedPtr{});
    MONAD_DEBUG_ASSERT(
        tnode->children.size() == size_t(std::popcount(orig_mask)));
    auto &children = tnode->children;

    for (auto const [index, branch] : NodeChildrenRange(orig_mask)) {
        if ((1 << branch) & requests.mask) {
            children[index].branch = branch;
            sm.down(branch);
            if ((1 << branch) & old->mask) {
                upsert_(
                    aux,
                    sm,
                    *tnode,
                    children[index],
                    old->move_next(old->to_child_index(branch)),
                    old->fnext(old->to_child_index(branch)),
                    std::move(requests)[branch],
                    prefix_index + 1);
                sm.up(1);
            }
            else {
                create_new_trie_(
                    aux,
                    sm,
                    tnode->version,
                    children[index],
                    std::move(requests)[branch],
                    prefix_index + 1);
                --tnode->npending;
                sm.up(1);
            }
        }
        else if ((1 << branch) & old->mask) {
            auto &child = children[index];
            child.copy_old_child(old, branch);
            if (aux.is_on_disk()) {
                if (sm.auto_expire() &&
                    child.subtrie_min_version <
                        aux.curr_upsert_auto_expire_version) {
                    // expire_() is similar to dispatch_updates() except that it
                    // can cut off some branches for data expiration
                    auto expire_tnode = ExpireTNode::make(
                        tnode.get(), branch, index, std::move(child.ptr));
                    expire_(aux, sm, std::move(expire_tnode), child.offset);
                }
                else if (
                    sm.compact() &&
                    (child.min_offset_fast < aux.compact_offset_fast ||
                     child.min_offset_slow < aux.compact_offset_slow)) {
                    bool const copy_node_for_fast =
                        child.min_offset_fast < aux.compact_offset_fast;
                    auto compact_tnode = CompactTNode::make(
                        tnode.get(), index, std::move(child.ptr));
                    compact_(
                        aux,
                        sm,
                        std::move(compact_tnode),
                        child.offset,
                        copy_node_for_fast);
                }
                else {
                    --tnode->npending;
                }
            }
            else {
                --tnode->npending;
            }
        }
    }
    fillin_entry(aux, sm, std::move(tnode), parent, entry);
}

// Split `old` at old_prefix_index, `updates` are already splitted at
// prefix_index to `requests`, which can have 1 or more sublists.
void mismatch_handler_(
    UpdateAuxImpl &aux, StateMachine &sm, UpdateTNode &parent, ChildData &entry,
    Node::SharedPtr old_ptr, Requests &requests, NibblesView const path,
    unsigned const old_prefix_index, unsigned const prefix_index)
{
    MONAD_ASSERT(old_ptr);
    Node &old = *old_ptr;
    MONAD_DEBUG_ASSERT(old.has_path());
    // Note: no leaf can be created at an existing non-leaf node
    MONAD_DEBUG_ASSERT(!requests.opt_leaf.has_value());
    unsigned char const old_nibble =
        old.path_nibble_view().get(old_prefix_index);
    uint16_t const orig_mask =
        static_cast<uint16_t>(1u << old_nibble | requests.mask);
    auto tnode = make_tnode(orig_mask, &parent, entry.branch, path);
    auto const number_of_children =
        static_cast<unsigned>(std::popcount(orig_mask));
    MONAD_DEBUG_ASSERT(
        tnode->children.size() == number_of_children && number_of_children > 0);
    auto &children = tnode->children;

    for (auto const [index, branch] : NodeChildrenRange(orig_mask)) {
        if ((1 << branch) & requests.mask) {
            children[index].branch = branch;
            sm.down(branch);
            if (branch == old_nibble) {
                upsert_(
                    aux,
                    sm,
                    *tnode,
                    children[index],
                    std::move(old_ptr),
                    INVALID_OFFSET,
                    std::move(requests)[branch],
                    prefix_index + 1,
                    old_prefix_index + 1);
            }
            else {
                create_new_trie_(
                    aux,
                    sm,
                    tnode->version,
                    children[index],
                    std::move(requests)[branch],
                    prefix_index + 1);
                --tnode->npending;
            }
            sm.up(1);
        }
        else if (branch == old_nibble) {
            sm.down(old_nibble);
            // nexts[j] is a path-shortened old node, trim prefix
            NibblesView const path_suffix =
                old.path_nibble_view().substr(old_prefix_index + 1);
            for (auto i = 0u; i < path_suffix.nibble_size(); ++i) {
                sm.down(path_suffix.get(i));
            }
            auto &child = children[index];
            child.branch = branch;
            // Updated node inherits the version number directly from old node
            child.finalize(
                make_node(old, path_suffix, old.opt_value(), old.version),
                sm.get_compute(),
                sm.cache());
            MONAD_DEBUG_ASSERT(child.offset == INVALID_OFFSET);
            // Note that it is possible that we recreate this node later after
            // done expiring all subtries under it
            sm.up(path_suffix.nibble_size() + 1);
            if (aux.is_on_disk()) {
                if (sm.auto_expire() &&
                    child.subtrie_min_version <
                        aux.curr_upsert_auto_expire_version) {
                    auto expire_tnode = ExpireTNode::make(
                        tnode.get(), branch, index, std::move(child.ptr));
                    expire_(aux, sm, std::move(expire_tnode), INVALID_OFFSET);
                }
                else if (auto const [min_offset_fast, min_offset_slow] =
                             calc_min_offsets(*child.ptr);
                         // same as old, TODO: can optimize by passing in the
                         // min offsets stored in old's parent
                         sm.compact() &&
                         (min_offset_fast < aux.compact_offset_fast ||
                          min_offset_slow < aux.compact_offset_slow)) {
                    bool const copy_node_for_fast =
                        min_offset_fast < aux.compact_offset_fast;
                    auto compact_tnode = CompactTNode::make(
                        tnode.get(), index, std::move(child.ptr));
                    compact_(
                        aux,
                        sm,
                        std::move(compact_tnode),
                        INVALID_OFFSET,
                        copy_node_for_fast);
                }
                else {
                    --tnode->npending;
                }
            }
            else {
                --tnode->npending;
            }
        }
    }
    fillin_entry(aux, sm, std::move(tnode), parent, entry);
}

void expire_(
    UpdateAuxImpl &aux, StateMachine &sm, ExpireTNode::unique_ptr_type tnode,
    chunk_offset_t const node_offset)
{
    // might recreate node to store in child.ptr
    if (!tnode->node) {
        // expire receiver should be similar to update_receiver, only difference
        // is needs to call expire_() over the read node rather than upsert_(),
        // can pass in a flag to differentiate, or maybe a different receiver?
        MONAD_ASSERT(node_offset != INVALID_OFFSET);
        node_receiver_t recv{
            [aux = &aux, sm = sm.clone(), tnode = std::move(tnode)](
                Node::SharedPtr read_node) mutable {
                tnode->update_after_async_read(std::move(read_node));
                auto *parent = tnode->parent;
                MONAD_ASSERT(parent);
                expire_(*aux, *sm, std::move(tnode), INVALID_OFFSET);
                while (!parent->npending) {
                    if (parent->type == tnode_type::update) {
                        upward_update(*aux, *sm, (UpdateTNode *)parent);
                        return;
                    }
                    MONAD_DEBUG_ASSERT(parent->type == tnode_type::expire);
                    auto *next_parent = parent->parent;
                    MONAD_ASSERT(next_parent);
                    try_fillin_parent_after_expiration(
                        *aux, *sm, ExpireTNode::unique_ptr_type{parent});
                    // go one level up
                    parent = next_parent;
                }
            },
            node_offset};
        aux.collect_expire_stats(true);
        async_read(aux, std::move(recv));
        return;
    }
    auto *const parent = tnode->parent;
    // expire subtries whose subtrie_min_version(branch) <
    // curr_upsert_auto_expire_version, check for compaction on the rest of the
    // subtries
    MONAD_ASSERT(sm.auto_expire() == true && sm.compact() == true);
    auto &node = *tnode->node;
    if (node.version < aux.curr_upsert_auto_expire_version) { // early stop
        // this branch is expired, erase it from parent
        parent->mask &= static_cast<uint16_t>(~(1u << tnode->branch));
        if (parent->type == tnode_type::update) {
            ((UpdateTNode *)parent)->children[tnode->index].erase();
        }
        --parent->npending;
        return;
    }
    MONAD_ASSERT(node.mask);
    // this loop might remove or update some branches
    // any fnext updates can be directly to node->fnext(), and we keep a
    // npending + current mask
    for (auto const [index, branch] : NodeChildrenRange(node.mask)) {
        if (node.subtrie_min_version(index) <
            aux.curr_upsert_auto_expire_version) {
            auto child_tnode = ExpireTNode::make(
                tnode.get(), branch, index, node.move_next(index));
            expire_(aux, sm, std::move(child_tnode), node.fnext(index));
        }
        else if (
            node.min_offset_fast(index) < aux.compact_offset_fast ||
            node.min_offset_slow(index) < aux.compact_offset_slow) {
            auto child_tnode =
                CompactTNode::make(tnode.get(), index, node.move_next(index));
            compact_(
                aux,
                sm,
                std::move(child_tnode),
                node.fnext(index),
                node.min_offset_fast(index) < aux.compact_offset_fast);
        }
        else {
            --tnode->npending;
        }
    }
    try_fillin_parent_after_expiration(aux, sm, std::move(tnode));
}

void fillin_parent_after_expiration(
    UpdateAuxImpl &aux, Node::SharedPtr new_node, ExpireTNode *const parent,
    uint8_t const index, uint8_t const branch, bool const cache_node)
{
    if (new_node == nullptr) {
        // expire this branch from parent
        parent->mask &= static_cast<uint16_t>(~(1u << branch));
        if (parent->type == tnode_type::update) {
            ((UpdateTNode *)parent)->children[index].erase();
        }
    }
    else {
        auto const new_offset = async_write_node_set_spare(aux, new_node, true);
        auto const new_node_virtual_offset =
            aux.physical_to_virtual(new_offset);
        MONAD_DEBUG_ASSERT(new_node_virtual_offset != INVALID_VIRTUAL_OFFSET);
        auto const &[min_offset_fast, min_offset_slow] =
            calc_min_offsets(*new_node, new_node_virtual_offset);
        MONAD_DEBUG_ASSERT(
            min_offset_fast != INVALID_COMPACT_VIRTUAL_OFFSET ||
            min_offset_slow != INVALID_COMPACT_VIRTUAL_OFFSET);
        auto const min_version = calc_min_version(*new_node);
        MONAD_ASSERT(min_version >= aux.curr_upsert_auto_expire_version);
        if (parent->type == tnode_type::update) {
            auto &child = ((UpdateTNode *)parent)->children[index];
            MONAD_ASSERT(!child.ptr); // been transferred to tnode
            child.offset = new_offset;
            MONAD_DEBUG_ASSERT(cache_node);
            child.ptr = std::move(new_node);
            child.min_offset_fast = min_offset_fast;
            child.min_offset_slow = min_offset_slow;
            child.subtrie_min_version = min_version;
        }
        else {
            MONAD_ASSERT(parent->type == tnode_type::expire);
            if (cache_node) {
                parent->cache_mask |= static_cast<uint16_t>(1u << index);
            }
            parent->node->set_next(index, std::move(new_node));
            parent->node->set_subtrie_min_version(index, min_version);
            parent->node->set_min_offset_fast(index, min_offset_fast);
            parent->node->set_min_offset_slow(index, min_offset_slow);
            parent->node->set_fnext(index, new_offset);
        }
    }
    --parent->npending;
}

void try_fillin_parent_after_expiration(
    UpdateAuxImpl &aux, StateMachine &sm, ExpireTNode::unique_ptr_type tnode)
{
    if (tnode->npending) {
        tnode.release();
        return;
    }
    auto const index = tnode->index;
    auto const branch = tnode->branch;
    auto *const parent = tnode->parent;
    auto const cache_node = tnode->cache_node;
    aux.collect_expire_stats(false);
    auto [done, new_node] =
        create_node_with_expired_branches(aux, sm, std::move(tnode));
    if (!done) {
        return;
    }
    fillin_parent_after_expiration(
        aux, std::move(new_node), parent, index, branch, cache_node);
}

void compact_(
    UpdateAuxImpl &aux, StateMachine &sm, CompactTNode::unique_ptr_type tnode,
    chunk_offset_t const node_offset, bool const copy_node_for_fast_or_slow)
{
    MONAD_ASSERT(tnode->type == tnode_type::compact);
    if (!tnode->node) {
        node_receiver_t recv{
            [copy_node_for_fast_or_slow,
             node_offset,
             aux = &aux,
             sm = sm.clone(),
             tnode = std::move(tnode)](Node::SharedPtr read_node) mutable {
                tnode->update_after_async_read(std::move(read_node));
                auto *parent = tnode->parent;
                compact_(
                    *aux,
                    *sm,
                    std::move(tnode),
                    node_offset,
                    copy_node_for_fast_or_slow);
                while (!parent->npending) {
                    if (parent->type == tnode_type::update) {
                        upward_update(*aux, *sm, (UpdateTNode *)parent);
                        return;
                    }
                    auto *next_parent = parent->parent;
                    MONAD_ASSERT(next_parent);
                    if (parent->type == tnode_type::compact) {
                        try_fillin_parent_with_rewritten_node(
                            *aux, CompactTNode::unique_ptr_type{parent});
                    }
                    else {
                        try_fillin_parent_after_expiration(
                            *aux,
                            *sm,
                            ExpireTNode::unique_ptr_type{
                                (ExpireTNode *)parent});
                    }
                    // go one level up
                    parent = next_parent;
                }
            },
            node_offset};
        aux.collect_compaction_read_stats(node_offset, recv.bytes_to_read);
        async_read(aux, std::move(recv));
        return;
    }
    // Only compact nodes < compaction range (either fast or slow) to slow,
    // otherwise rewrite to fast list
    // INVALID_OFFSET indicates node is being updated and not yet written, that
    // case we write to fast
    auto const virtual_node_offset = aux.physical_to_virtual(node_offset);
    bool const rewrite_to_fast = [&aux, &virtual_node_offset] {
        if (virtual_node_offset == INVALID_VIRTUAL_OFFSET) {
            return true;
        }
        compact_virtual_chunk_offset_t const compacted_virtual_offset{
            virtual_node_offset};
        return (virtual_node_offset.in_fast_list() &&
                compacted_virtual_offset >= aux.compact_offset_fast) ||
               (!virtual_node_offset.in_fast_list() &&
                compacted_virtual_offset >= aux.compact_offset_slow);
    }();

    Node &node = *tnode->node;
    tnode->rewrite_to_fast = rewrite_to_fast;
    aux.collect_compacted_nodes_stats(
        copy_node_for_fast_or_slow,
        rewrite_to_fast,
        virtual_node_offset,
        node.get_disk_size());

    for (unsigned j = 0; j < node.number_of_children(); ++j) {
        if (node.min_offset_fast(j) < aux.compact_offset_fast ||
            node.min_offset_slow(j) < aux.compact_offset_slow) {
            auto child_tnode =
                CompactTNode::make(tnode.get(), j, node.move_next(j));
            compact_(
                aux,
                sm,
                std::move(child_tnode),
                node.fnext(j),
                node.min_offset_fast(j) < aux.compact_offset_fast);
        }
        else {
            --tnode->npending;
        }
    }
    // Compaction below `node` is completed, rewrite `node` to disk and put
    // offset and min_offset somewhere in parent depends on its type
    try_fillin_parent_with_rewritten_node(aux, std::move(tnode));
}

void try_fillin_parent_with_rewritten_node(
    UpdateAuxImpl &aux, CompactTNode::unique_ptr_type tnode)
{
    if (tnode->npending) { // there are unfinished async below node
        tnode.release();
        return;
    }
    auto [min_offset_fast, min_offset_slow] =
        calc_min_offsets(*tnode->node, INVALID_VIRTUAL_OFFSET);
    // If subtrie contains nodes from fast list, write itself to fast list too
    if (min_offset_fast != INVALID_COMPACT_VIRTUAL_OFFSET) {
        tnode->rewrite_to_fast = true; // override that
    }
    auto const new_offset =
        async_write_node_set_spare(aux, tnode->node, tnode->rewrite_to_fast);
    auto const new_node_virtual_offset = aux.physical_to_virtual(new_offset);
    MONAD_DEBUG_ASSERT(new_node_virtual_offset != INVALID_VIRTUAL_OFFSET);
    compact_virtual_chunk_offset_t const truncated_new_virtual_offset{
        new_node_virtual_offset};
    // update min offsets in subtrie
    if (tnode->rewrite_to_fast) {
        min_offset_fast =
            std::min(min_offset_fast, truncated_new_virtual_offset);
    }
    else {
        min_offset_slow =
            std::min(min_offset_slow, truncated_new_virtual_offset);
    }
    MONAD_DEBUG_ASSERT(min_offset_fast >= aux.compact_offset_fast);
    MONAD_DEBUG_ASSERT(min_offset_slow >= aux.compact_offset_slow);
    auto *parent = tnode->parent;
    auto const index = tnode->index;
    if (parent->type == tnode_type::update) {
        auto *const p = reinterpret_cast<UpdateTNode *>(parent);
        MONAD_DEBUG_ASSERT(tnode->cache_node);
        auto &child = p->children[index];
        child.ptr = std::move(tnode->node);
        child.offset = new_offset;
        child.min_offset_fast = min_offset_fast;
        child.min_offset_slow = min_offset_slow;
    }
    else {
        MONAD_DEBUG_ASSERT(
            parent->type == tnode_type::compact ||
            parent->type == tnode_type::expire);
        auto &node = (parent->type == tnode_type::compact)
                         ? parent->node
                         : ((ExpireTNode *)parent)->node;
        MONAD_ASSERT(node);
        node->set_fnext(index, new_offset);
        node->set_min_offset_fast(index, min_offset_fast);
        node->set_min_offset_slow(index, min_offset_slow);
        if (tnode->cache_node || parent->type == tnode_type::expire) {
            // Delay tnode->node deallocation to parent ExpireTNode
            node->set_next(index, std::move(tnode->node));
            if (tnode->cache_node && parent->type == tnode_type::expire) {
                ((ExpireTNode *)parent)->cache_mask |=
                    static_cast<uint16_t>(1u << tnode->index);
            }
        }
    }
    --parent->npending;
}

/////////////////////////////////////////////////////
// Async write
/////////////////////////////////////////////////////

node_writer_unique_ptr_type create_node_writer_at_offset(
    UpdateAuxImpl &aux, chunk_offset_t target_offset, bool is_fast);

// Pad node_writer's buffer to DISK_PAGE_SIZE (512-byte) alignment with zeros.
// Required before initiating any O_DIRECT write with a partially-filled buffer.
// Returns the number of padding bytes appended.
size_t
pad_writer_to_disk_page_alignment(node_writer_unique_ptr_type &node_writer)
{
    auto *sender = &node_writer->sender();
    auto const written = sender->written_buffer_bytes();
    auto const padded = round_up_align<DISK_PAGE_BITS>(written);
    auto const pad_bytes = padded - written;
    if (pad_bytes > 0) {
        auto *tozero = sender->advance_buffer_append(pad_bytes);
        memset(tozero, 0, pad_bytes);
    }
    return pad_bytes;
}

// Ensure ws.node_writer is positioned at target_offset, submitting the
// current buffer and repositioning as needed. Non-blocking: returns false
// if no write buffer is immediately available.
bool ensure_writer_at_offset(
    UpdateAuxImpl &aux, UpdateAuxImpl::WriterState &ws,
    chunk_offset_t target_offset, bool is_fast)
{
    if (ws.node_writer) {
        auto current_offset = ws.node_writer->sender().offset();
        auto current_pos = current_offset.offset +
                           ws.node_writer->sender().written_buffer_bytes();

        if (current_offset.id != target_offset.id) {
            // Different chunk - offset must be 0 (allocate_write_offset
            // always allocates new chunks at offset 0)
            MONAD_ASSERT_PRINTF(
                target_offset.offset == 0,
                "ensure_writer_at_offset: new chunk allocation must start at "
                "offset 0! chunk=%u offset=%u",
                target_offset.id,
                target_offset.offset);

            // Pad and flush current buffer before repositioning to new chunk
            if (ws.node_writer->sender().written_buffer_bytes() > 0) {
                pad_writer_to_disk_page_alignment(ws.node_writer);
                ws.node_writer->receiver().reset(
                    ws.node_writer->sender().written_buffer_bytes());
                ws.node_writer->initiate();
                ws.node_writer.release();
            }
            ws.node_writer =
                create_node_writer_at_offset(aux, target_offset, is_fast);
            return ws.node_writer != nullptr;
        }

        // Same chunk - buffer position MUST match allocated offset
        // (if not, write_position is out of sync with buffer)
        MONAD_ASSERT_PRINTF(
            current_pos == target_offset.offset,
            "ensure_writer_at_offset: buffer position mismatch! "
            "chunk=%u current_pos=%lu allocated_offset=%u",
            current_offset.id,
            (unsigned long)current_pos,
            target_offset.offset);
        return true;
    }

    // No buffer - create one at the target offset (non-blocking)
    ws.node_writer = create_node_writer_at_offset(aux, target_offset, is_fast);
    return ws.node_writer != nullptr;
}

// Non-blocking drain of delayed writes into available I/O buffers. Processes
// queued writes until buffer exhaustion: if no write buffer is immediately
// available, returns and lets I/O completion callbacks re-trigger draining.
// When a buffer completes, write_operation_io_receiver::set_value calls this
// again, creating a self-sustaining drain loop.
void process_delayed_writes(UpdateAuxImpl &aux, bool is_fast)
{
    auto &ws = aux.writer(is_fast);

    // Guard against recursive calls. Recursion occurs when an outer caller
    // (e.g., flush_buffered_writes) invokes process_delayed_writes, then polls
    // io_uring (via io->flush()), which completes a write whose set_value
    // callback re-invokes process_delayed_writes.
    if (ws.processing_delayed_writes) {
        return;
    }

    ws.processing_delayed_writes = true;
    auto guard = monad::make_scope_exit(
        [&ws]() noexcept { ws.processing_delayed_writes = false; });

    while (!ws.delayed_writes.empty()) {
        auto &delayed = ws.delayed_writes.front();

        // For a partially-written node (resuming after buffer exhaustion),
        // the resume position is past the allocated start by offset_in_data.
        // By construction this is already disk-page-aligned since we only
        // pause at buffer boundaries.
        auto target_offset = delayed.allocated_offset;
        if (delayed.offset_in_data > 0) {
            target_offset = chunk_offset_t{
                static_cast<uint32_t>(target_offset.id),
                static_cast<uint32_t>(
                    target_offset.offset + delayed.offset_in_data)};
            MONAD_ASSERT((target_offset.offset & (DISK_PAGE_SIZE - 1)) == 0);
        }

        if (!ensure_writer_at_offset(aux, ws, target_offset, is_fast)) {
            // All write buffers genuinely in flight. When one completes,
            // its I/O completion callback will re-invoke
            // process_delayed_writes to continue draining the queue.
            MONAD_ASSERT(aux.io->writes_in_flight() > 0);
            ++ws.buffer_alloc_failures;
            return;
        }

        auto *sender = &ws.node_writer->sender();
        auto const data_size = static_cast<size_t>(delayed.disk_size);
        unsigned &offset_in_data = delayed.offset_in_data;

        // Serialize delayed node into buffers, replacing when full
        while (offset_in_data < data_size) {
            auto remaining_buffer = sender->remaining_buffer_bytes();

            if (remaining_buffer == 0) {
                // Need new buffer - compute aligned position after current
                // buffer
                auto current_offset = sender->offset();
                auto written = sender->written_buffer_bytes();
                file_offset_t next_pos = current_offset.offset + written;
                next_pos = round_up_align<DISK_PAGE_BITS>(next_pos);

                chunk_offset_t next_offset{
                    static_cast<uint32_t>(current_offset.id),
                    static_cast<uint32_t>(next_pos)};

                // Nodes always fit within a single chunk (ensured by
                // allocate_write_offset), so we should never cross a chunk
                // boundary while writing a single node.
                MONAD_ASSERT_PRINTF(
                    next_pos < aux.io->chunk_capacity(current_offset.id),
                    "process_delayed_writes: node write crossed chunk "
                    "boundary! chunk=%u next_pos=%lu capacity=%lu",
                    current_offset.id,
                    (unsigned long)next_pos,
                    (unsigned long)aux.io->chunk_capacity(current_offset.id));

                // Initiate current buffer
                ws.node_writer->receiver().reset(
                    ws.node_writer->sender().written_buffer_bytes());
                ws.node_writer->initiate();
                ws.node_writer.release();

                // Create new buffer at computed position (non-blocking)
                ws.node_writer = replace_node_writer(aux, next_offset, is_fast);
                if (!ws.node_writer) {
                    // All buffers in flight. I/O completion callbacks will
                    // re-invoke process_delayed_writes to continue draining.
                    MONAD_ASSERT(aux.io->writes_in_flight() > 0);
                    ++ws.buffer_alloc_failures;
                    return;
                }
                sender = &ws.node_writer->sender();
                remaining_buffer = sender->remaining_buffer_bytes();
            }

            // Write what we can to current buffer
            auto bytes_to_write =
                std::min((size_t)remaining_buffer, data_size - offset_in_data);
            auto *where =
                (unsigned char *)sender->advance_buffer_append(bytes_to_write);
            serialize_node_to_buffer(
                where,
                static_cast<unsigned>(bytes_to_write),
                *delayed.node,
                delayed.disk_size,
                offset_in_data);
            offset_in_data += static_cast<unsigned>(bytes_to_write);
            MONAD_DEBUG_ASSERT(offset_in_data <= delayed.disk_size);
        }

        // Node fully written, remove from queue
        ws.delayed_writes.pop_front();
    }
}

node_writer_unique_ptr_type replace_node_writer(
    UpdateAuxImpl &aux, chunk_offset_t target_offset, bool is_fast)
{
    // Position new buffer at target_offset (provided by caller).
    // Target must be disk-page-aligned.

    auto const chunk_capacity = aux.io->chunk_capacity(target_offset.id);

    // Verify offset is 512-byte aligned for O_DIRECT I/O
    MONAD_ASSERT_PRINTF(
        (target_offset.offset & (DISK_PAGE_SIZE - 1)) == 0,
        "replace_node_writer: target offset %u is not 512-aligned! chunk=%u",
        target_offset.offset,
        target_offset.id);

    size_t const bytes_to_write = std::min(
        AsyncIO::WRITE_BUFFER_SIZE,
        (size_t)(chunk_capacity - target_offset.offset));

    return aux.io->try_make_connected(
        write_single_buffer_sender{target_offset, bytes_to_write},
        write_operation_io_receiver{bytes_to_write, &aux, is_fast});
}

// Create a node_writer positioned at a specific offset.
// Returns nullptr if no write buffer is available.
node_writer_unique_ptr_type create_node_writer_at_offset(
    UpdateAuxImpl &aux, chunk_offset_t target_offset, bool is_fast)
{
    // Note: We don't assert chunk.size() >= target_offset.offset because
    // delayed writes may allocate ahead of the physical write position

    auto const chunk_capacity = aux.io->chunk_capacity(target_offset.id);
    size_t const bytes_to_write = std::min(
        AsyncIO::WRITE_BUFFER_SIZE,
        (size_t)(chunk_capacity - target_offset.offset));

    auto ret = aux.io->try_make_connected(
        write_single_buffer_sender{target_offset, bytes_to_write},
        write_operation_io_receiver{bytes_to_write, &aux, is_fast});

    // Metadata (chunk list ownership) is managed solely by
    // allocate_write_offset(). This function only creates the I/O buffer; don't
    // update metadata here.

    return ret;
}

// Allocate offset for node write. Non-blocking (no I/O or polling).
// Aborts if free chunk list is exhausted when a new chunk is needed.
chunk_offset_t
allocate_write_offset(UpdateAuxImpl &aux, size_t node_size, bool is_fast)
{
    auto &write_pos = aux.writer(is_fast).write_position;
    auto const chunk_capacity =
        aux.io->chunk_capacity(write_pos.current_chunk_id);
    auto const chunk_remaining = chunk_capacity - write_pos.current_offset;

    chunk_offset_t allocated_offset{0, 0};

    if (node_size > chunk_remaining) {
        // Need new chunk - remove from free list and mark as allocated
        auto const *ci_ = aux.db_metadata()->free_list_end();
        MONAD_ASSERT(ci_ != nullptr);
        auto idx = ci_->index(aux.db_metadata());

        // Reserve this chunk by removing from free list and adding to
        // appropriate list
        aux.remove(idx);
        aux.append(
            is_fast ? UpdateAuxImpl::chunk_list::fast
                    : UpdateAuxImpl::chunk_list::slow,
            idx);

        // Allocate at start of new chunk
        MONAD_DEBUG_ASSERT(node_size <= aux.io->chunk_capacity(idx));
        allocated_offset = chunk_offset_t{idx, 0};
        write_pos.current_chunk_id = idx;
        write_pos.current_offset = node_size;
    }
    else {
        // Allocate in current chunk
        allocated_offset = write_pos.to_chunk_offset();
        write_pos.current_offset += node_size;

        // Sanity check: if we've exceeded chunk capacity, something is wrong
        MONAD_ASSERT(write_pos.current_offset <= chunk_capacity);
    }

    return allocated_offset;
}

// Return the allocated physical offset for this node. In the fast path the
// node is written immediately; otherwise the write is deferred to the delayed
// write queue.
async_write_node_result async_write_node(
    UpdateAuxImpl &aux, node_writer_unique_ptr_type &node_writer,
    Node::SharedPtr const &node, bool is_fast)
{
    auto const size = node->get_disk_size();

    aux.io->poll_nonblocking_if_not_within_completions(1);

    auto &delayed_writes = aux.writer(is_fast).delayed_writes;

    // If delay queue not empty or no buffer, queue to maintain order
    if (!delayed_writes.empty() || !node_writer) {
        chunk_offset_t allocated_offset =
            allocate_write_offset(aux, size, is_fast);

        delayed_writes.push_back(DelayedNodeWrite{
            .node = node,
            .disk_size = size,
            .allocated_offset = allocated_offset});

        process_delayed_writes(aux, is_fast);

        return async_write_node_result{
            .offset_written_to = allocated_offset, .bytes_appended = size};
    }

    // Fast path: node fits in current buffer
    auto *sender = &node_writer->sender();
    auto const remaining_bytes = sender->remaining_buffer_bytes();

    [[likely]] if (size <= remaining_bytes) {
        // Can write immediately without buffer allocation
        chunk_offset_t allocated_offset =
            allocate_write_offset(aux, size, is_fast);
        auto *where_to_serialize = sender->advance_buffer_append(size);
        serialize_node_to_buffer(
            (unsigned char *)where_to_serialize, size, *node, size);

        return async_write_node_result{
            .offset_written_to = allocated_offset, .bytes_appended = size};
    }

    // Slow path: node doesn't fit, queue it and return allocated offset
    chunk_offset_t allocated_offset = allocate_write_offset(aux, size, is_fast);

    delayed_writes.push_back(DelayedNodeWrite{
        .node = node, .disk_size = size, .allocated_offset = allocated_offset});

    // Attempt to drain delayed writes. Returns immediately if no buffers
    // are available; I/O completion callbacks will retry.
    process_delayed_writes(aux, is_fast);

    return async_write_node_result{
        .offset_written_to = allocated_offset, .bytes_appended = size};
}

// Return node's allocated physical offset. The actual write may be deferred.
// Triedb should not depend on any metadata to walk the data structure.
chunk_offset_t async_write_node_set_spare(
    UpdateAuxImpl &aux, Node::SharedPtr const &node, bool write_to_fast)
{
    write_to_fast &= aux.can_write_to_fast();
    if (aux.alternate_slow_fast_writer()) {
        // alternate between slow and fast writer
        aux.set_can_write_to_fast(!aux.can_write_to_fast());
    }

    auto off =
        async_write_node(
            aux, aux.writer(write_to_fast).node_writer, node, write_to_fast)
            .offset_written_to;
    MONAD_ASSERT(
        (write_to_fast && aux.db_metadata()->at(off.id)->in_fast_list) ||
        (!write_to_fast && aux.db_metadata()->at(off.id)->in_slow_list));
    unsigned const pages = num_pages(off.offset, node->get_disk_size());
    off.set_spare(static_cast<uint16_t>(node_disk_pages_spare_15{pages}));
    return off;
}

void flush_buffered_writes(UpdateAuxImpl &aux)
{
    // Non-blocking drain: process what we can with currently available buffers.
    process_delayed_writes(aux, true);
    process_delayed_writes(aux, false);

    // Submit current buffers. If node_writer is null, the buffer was already
    // submitted (all buffers in flight). If non-null, pad and submit it;
    // replacement allocation is non-blocking — if no buffer is available,
    // node_writer is left null (next write will allocate or enqueue).
    auto flush = [&](node_writer_unique_ptr_type &node_writer, bool is_fast) {
        if (!node_writer) {
            return;
        }

        // Nothing written (e.g. slow writer with no slow nodes) - skip flush
        if (node_writer->sender().written_buffer_bytes() == 0) {
            return;
        }

        // Pad to O_DIRECT alignment and advance write_position for the padding
        auto const pad_bytes = pad_writer_to_disk_page_alignment(node_writer);
        if (pad_bytes > 0) {
            allocate_write_offset(aux, pad_bytes, is_fast);
        }

        // Get current write_position for new buffer
        auto const next_offset =
            aux.writer(is_fast).write_position.to_chunk_offset();

        // Non-blocking replacement: null node_writer is fine
        auto new_node_writer = replace_node_writer(aux, next_offset, is_fast);
        auto to_initiate = std::move(node_writer);
        node_writer = std::move(new_node_writer);
        to_initiate->receiver().reset(
            to_initiate->sender().written_buffer_bytes());
        to_initiate->initiate();
        // Ownership transferred to I/O subsystem. On completion, the
        // receiver frees the buffer and triggers process_delayed_writes.
        to_initiate.release();
    };

    flush(aux.writer_fast.node_writer, true);
    flush(aux.writer_slow.node_writer, false);
    aux.io->flush();
    MONAD_ASSERT(aux.writer_fast.delayed_writes.empty());
    MONAD_ASSERT(aux.writer_slow.delayed_writes.empty());
}

// return root physical offset
chunk_offset_t write_new_root_node(
    UpdateAuxImpl &aux, Node::SharedPtr const &root, uint64_t const version)
{
    auto const offset_written_to = async_write_node_set_spare(aux, root, true);
    flush_buffered_writes(aux);
    // advance fast and slow ring's latest offset in db metadata
    auto const fast_offset = aux.writer_fast.write_position.to_chunk_offset();
    auto const slow_offset = aux.writer_slow.write_position.to_chunk_offset();
    aux.advance_db_offsets_to(fast_offset, slow_offset);
    // update root offset
    auto const max_version_in_db = aux.db_history_max_version();
    if (MONAD_UNLIKELY(max_version_in_db == INVALID_BLOCK_NUM)) {
        aux.fast_forward_next_version(version);
        aux.append_root_offset(offset_written_to);
        MONAD_ASSERT(aux.db_history_range_lower_bound() == version);
    }
    else if (version <= max_version_in_db) {
        MONAD_ASSERT(
            version >=
            ((max_version_in_db >= aux.version_history_length())
                 ? max_version_in_db - aux.version_history_length() + 1
                 : 0));
        auto const prev_lower_bound = aux.db_history_range_lower_bound();
        aux.update_root_offset(version, offset_written_to);
        MONAD_ASSERT(
            aux.db_history_range_lower_bound() ==
            std::min(version, prev_lower_bound));
    }
    else {
        MONAD_ASSERT(version == max_version_in_db + 1);
        // Erase the earliest valid version if it is going to be outdated after
        // writing a new version, must happen before appending new root offset
        if (version - aux.db_history_min_valid_version() >=
            aux.version_history_length()) { // if exceed history length
            aux.erase_versions_up_to_and_including(
                version - aux.version_history_length());
            MONAD_ASSERT(
                version - aux.db_history_min_valid_version() <
                aux.version_history_length());
        }
        aux.append_root_offset(offset_written_to);
    }
    return offset_written_to;
}

MONAD_MPT_NAMESPACE_END

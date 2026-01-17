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
#include <category/mpt/fiber_write_utils.hpp>
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

// invoke at the end of each block upsert
void flush_buffered_writes(UpdateAuxImpl &);
chunk_offset_t write_new_root_node(UpdateAuxImpl &, Node &, uint64_t);

// Fiber-based write functions (defined later in file)
chunk_offset_t fiber_write_node_set_spare(
    UpdateAuxImpl &, FiberWriteBuffer &, Node &, bool in_fast_list);
chunk_offset_t fiber_write_new_root_node(UpdateAuxImpl &, Node &, uint64_t);

Node::SharedPtr upsert(
    UpdateAuxImpl &aux, uint64_t const version, StateMachine &sm,
    Node::SharedPtr old, UpdateList &&updates, bool const write_root)
{
    auto impl = [&] {
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
            create_new_trie_(
                aux, sm, sentinel->version, entry, std::move(updates));
        }
        auto root = entry.ptr;
        if (aux.is_on_disk() && root) {
            if (write_root) {
                write_new_root_node(aux, *root, version);
            }
            else {
                flush_buffered_writes(aux);
            }
        }
        return root;
    };
    if (aux.is_current_thread_upserting()) {
        return impl();
    }
    else {
        auto g(aux.unique_lock());
        auto g2(aux.set_current_upsert_tid());
        return impl();
    }
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
                auto g(impl->aux.unique_lock());
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

/////////////////////////////////////////////////////
// Create Node
/////////////////////////////////////////////////////

std::pair<bool, Node::SharedPtr> create_node_with_expired_branches(
    UpdateAuxImpl &aux, StateMachine &sm, ExpireTNode::unique_ptr_type tnode)
{
    (void)sm; // Used in async path for upward_update, not needed in fiber path
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
            // Fiber read - direct synchronous-style IO
            auto read_node = fiber_read_node(*aux.io, orig->fnext(child_index));
            auto new_node = make_node(
                *read_node,
                concat(
                    tnode->node->path_nibble_view(),
                    child_branch,
                    read_node->path_nibble_view()),
                read_node->opt_value(),
                read_node->version);
            fillin_parent_after_expiration(
                aux,
                std::move(new_node),
                tnode->parent,
                tnode->index,
                tnode->branch,
                tnode->cache_node);
            // In fiber path, upward propagation happens through call stack.
            // Parent is still owned by caller, so we can't take ownership here.
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
                child.offset =
                    async_write_node_set_spare(aux, *child.ptr, true);
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
                // child offset is older than current writer's position
                auto const wip_offset =
                    virtual_child_offset.in_fast_list()
                        ? aux.fiber_write_buffer_->current_offset()
                        : aux.fiber_write_buffer_slow_->current_offset();
                MONAD_DEBUG_ASSERT(
                    virtual_child_offset < aux.physical_to_virtual(wip_offset));
            }
            // Fiber read - direct synchronous-style IO
            auto read_node = fiber_read_node(*aux.io, child.offset);
            auto *parent_ptr = tnode->parent;
            MONAD_DEBUG_ASSERT(parent_ptr);
            auto &entry_ref = parent_ptr->children[tnode->child_index()];
            MONAD_DEBUG_ASSERT(entry_ref.branch < 16);
            auto &child_ref = tnode->children[bitmask_index(
                tnode->orig_mask,
                static_cast<unsigned>(std::countr_zero(tnode->mask)))];
            child_ref.ptr = std::move(read_node);
            // No sm.up() needed here - the recursive call handles its own depth
            // tracking. On main, the async callback used a cloned state
            // machine, so the sm.up() operated on the clone. In the fiber path,
            // we use the same state machine instance.
            create_node_compute_data_possibly_async(
                aux, sm, *parent_ptr, entry_ref, std::move(tnode), false);
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
        // Fiber read - direct synchronous-style IO
        auto read_node = fiber_read_node(*aux.io, old_offset);
        // continue recurse down the trie starting from `old`
        // No sm.down() before this call, so no sm.up() after - the recursive
        // call handles its own depth tracking internally.
        upsert_(
            aux,
            sm,
            parent,
            entry,
            std::move(read_node),
            INVALID_OFFSET,
            std::move(updates),
            prefix_index);
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
        aux.collect_expire_stats(true);
        // Fiber read - direct synchronous-style IO
        auto read_node = fiber_read_node(*aux.io, node_offset);
        tnode->update_after_async_read(std::move(read_node));
        // Continue processing with populated node. Recursive call will
        // process tnode and decrement parent->npending. Upward propagation
        // happens through call stack - parent is still owned by caller.
        expire_(aux, sm, std::move(tnode), INVALID_OFFSET);
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
        auto const new_offset =
            async_write_node_set_spare(aux, *new_node, true);
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
        // Calculate bytes_to_read for stats (same calculation as
        // node_receiver_t)
        auto const rd_offset = round_down_align<DISK_PAGE_BITS>(node_offset);
        auto const pages = node_disk_pages_spare_15{rd_offset}.to_pages();
        auto const bytes_to_read =
            static_cast<unsigned>(pages << DISK_PAGE_BITS);
        aux.collect_compaction_read_stats(node_offset, bytes_to_read);

        // Fiber read - direct synchronous-style IO
        auto read_node = fiber_read_node(*aux.io, node_offset);
        tnode->update_after_async_read(std::move(read_node));
        // Continue processing with populated node. Recursive call will
        // process tnode and decrement parent->npending. Upward propagation
        // happens through call stack - parent is still owned by caller.
        compact_(
            aux, sm, std::move(tnode), node_offset, copy_node_for_fast_or_slow);
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
        async_write_node_set_spare(aux, *tnode->node, tnode->rewrite_to_fast);
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

// Return node's physical offset the node is written at, triedb should not
// depend on any metadata to walk the data structure.
chunk_offset_t
async_write_node_set_spare(UpdateAuxImpl &aux, Node &node, bool write_to_fast)
{
    write_to_fast &= aux.can_write_to_fast();
    if (aux.alternate_slow_fast_writer()) {
        aux.set_can_write_to_fast(!aux.can_write_to_fast());
    }
    auto &buffer = write_to_fast ? aux.fiber_write_buffer_fast_ref()
                                 : aux.fiber_write_buffer_slow_ref();
    return fiber_write_node_set_spare(aux, buffer, node, write_to_fast);
}

void flush_buffered_writes(UpdateAuxImpl &aux)
{
    aux.fiber_write_buffer_fast_ref().flush();
    auto &slow_buffer = aux.fiber_write_buffer_slow_ref();
    if (slow_buffer.written_bytes() > 0) {
        slow_buffer.flush();
    }
}

// return root physical offset
chunk_offset_t
write_new_root_node(UpdateAuxImpl &aux, Node &root, uint64_t const version)
{
    return fiber_write_new_root_node(aux, root, version);
}

// ============================================================================
// Fiber-based write functions
// These yield the fiber when waiting for IO instead of using callbacks.
// ============================================================================

// Write a node to disk using fiber-based IO. Yields fiber when buffer is full.
// Returns the offset where the node was written.
// in_fast_list indicates whether this buffer is for fast or slow chunk list.
chunk_offset_t fiber_write_node(
    UpdateAuxImpl &aux, FiberWriteBuffer &buffer, Node const &node,
    bool in_fast_list)
{
    auto const size = node.get_disk_size();
    auto const chunk_capacity =
        aux.io->chunk_capacity(buffer.start_offset().id);

    // Check if current buffer position would exceed chunk capacity.
    // This can happen after accumulating many small writes without flushing.
    auto const current_raw_offset =
        buffer.start_offset().offset + buffer.written_bytes();
    if (current_raw_offset + size > chunk_capacity) {
        // Either current offset or new write would exceed chunk - need to flush
        // and possibly get new chunk.
        auto const written_padded =
            round_up_align<DISK_PAGE_BITS>(buffer.written_bytes());
        auto const offset_after_flush =
            buffer.start_offset().offset + written_padded;

        if (offset_after_flush + size > chunk_capacity) {
            // Node won't fit even after flushing - need new chunk
            auto *ci = aux.db_metadata()->free_list_end();
            MONAD_ASSERT(ci != nullptr);
            auto const new_chunk_id = ci->index(aux.db_metadata());
            aux.remove(new_chunk_id);
            aux.append(
                in_fast_list ? UpdateAuxImpl::chunk_list::fast
                             : UpdateAuxImpl::chunk_list::slow,
                new_chunk_id);
            chunk_offset_t new_offset{new_chunk_id, 0};
            buffer.flush_and_reset(new_offset);
        }
        else if (buffer.written_bytes() > 0) {
            // After flush, node will fit - just flush
            buffer.flush();
        }
    }

    // Now safe to check if node fits in buffer
    if (size <= buffer.remaining()) {
        // Simple case: node fits in buffer
        auto const offset = buffer.current_offset();
        auto *where = buffer.reserve(size);
        MONAD_DEBUG_ASSERT(where != nullptr);
        serialize_node_to_buffer(
            reinterpret_cast<unsigned char *>(where), size, node, size);
        buffer.commit(size);
        return offset;
    }

    // Node doesn't fit in current buffer. Calculate chunk_remaining including
    // the unflushed buffer bytes (like async code does at lines 1456-1458).
    // This accounts for where we'll be AFTER flushing the current buffer.
    auto const written_padded =
        round_up_align<DISK_PAGE_BITS>(buffer.written_bytes());
    auto const offset_after_flush =
        buffer.start_offset().offset + written_padded;
    auto const chunk_remaining_after_flush =
        (offset_after_flush <= chunk_capacity)
            ? chunk_capacity - offset_after_flush
            : 0;

    if (size > chunk_remaining_after_flush) {
        // Node won't fit in current chunk after flushing. Get a new chunk.
        auto *ci = aux.db_metadata()->free_list_end();
        MONAD_ASSERT(ci != nullptr); // out of free chunks
        auto const new_chunk_id = ci->index(aux.db_metadata());
        // Remove from free list and add to appropriate used list
        aux.remove(new_chunk_id);
        aux.append(
            in_fast_list ? UpdateAuxImpl::chunk_list::fast
                         : UpdateAuxImpl::chunk_list::slow,
            new_chunk_id);
        chunk_offset_t new_offset{new_chunk_id, 0};
        buffer.flush_and_reset(new_offset);
    }
    else if (buffer.written_bytes() > 0) {
        // Node fits in chunk after flushing - just flush
        buffer.flush();
    }

    // Record the offset where node starts
    auto const node_offset = buffer.current_offset();

    // Serialize node, handling potential buffer overflow
    unsigned offset_in_node = 0;
    while (offset_in_node < size) {
        auto const bytes_to_write = std::min(
            buffer.remaining(), static_cast<size_t>(size - offset_in_node));
        auto *where = buffer.reserve(bytes_to_write);
        MONAD_DEBUG_ASSERT(where != nullptr);
        serialize_node_to_buffer(
            reinterpret_cast<unsigned char *>(where),
            static_cast<unsigned>(bytes_to_write),
            node,
            size,
            offset_in_node);
        buffer.commit(bytes_to_write);
        offset_in_node += static_cast<unsigned>(bytes_to_write);

        if (offset_in_node < size && buffer.remaining() == 0) {
            // Buffer full but node not done - check if flush would exceed
            // chunk boundary. If so, we have a problem since node was supposed
            // to fit in this chunk. This shouldn't happen if the initial check
            // was correct, but guard against it anyway.
            auto const loop_written_padded =
                round_up_align<DISK_PAGE_BITS>(buffer.written_bytes());
            auto const loop_offset_after_flush =
                buffer.start_offset().offset + loop_written_padded;
            auto const loop_chunk_capacity =
                aux.io->chunk_capacity(buffer.start_offset().id);

            if (loop_offset_after_flush >= loop_chunk_capacity) {
                // Would exceed chunk boundary - get new chunk
                auto *ci = aux.db_metadata()->free_list_end();
                MONAD_ASSERT(ci != nullptr);
                auto const new_chunk_id = ci->index(aux.db_metadata());
                aux.remove(new_chunk_id);
                aux.append(
                    in_fast_list ? UpdateAuxImpl::chunk_list::fast
                                 : UpdateAuxImpl::chunk_list::slow,
                    new_chunk_id);
                chunk_offset_t new_offset{new_chunk_id, 0};
                buffer.flush_and_reset(new_offset);
            }
            else {
                buffer.flush();
            }
        }
    }

    return node_offset;
}

// Write a node and set the spare bits encoding disk pages.
// This is the fiber equivalent of async_write_node_set_spare.
chunk_offset_t fiber_write_node_set_spare(
    UpdateAuxImpl &aux, FiberWriteBuffer &buffer, Node &node, bool in_fast_list)
{
    auto offset = fiber_write_node(aux, buffer, node, in_fast_list);
    unsigned const pages = num_pages(offset.offset, node.get_disk_size());
    offset.set_spare(static_cast<uint16_t>(node_disk_pages_spare_15{pages}));
    return offset;
}

// Fiber version of write_new_root_node.
// This writes the root node and flushes using fiber-based IO.
// The caller must ensure they're running in a fiber context where yielding is
// safe.
chunk_offset_t fiber_write_new_root_node(
    UpdateAuxImpl &aux, Node &root, uint64_t const version)
{
    // Root always goes to fast buffer (in_fast_list = true)
    auto const offset_written_to = fiber_write_node_set_spare(
        aux, aux.fiber_write_buffer_fast_ref(), root, true);

    // Flush both fast and slow buffers
    flush_buffered_writes(aux);

    // Advance both fast and slow ring offsets in db metadata
    aux.advance_db_offsets_to(
        aux.fiber_write_buffer_fast_ref().current_offset(),
        aux.fiber_write_buffer_slow_ref().current_offset());

    // Update root offset (same logic as non-fiber version)
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
        // Erase the earliest valid version if it is going to be outdated
        if (version - aux.db_history_min_valid_version() >=
            aux.version_history_length()) {
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

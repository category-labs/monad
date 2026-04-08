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
#include <category/core/likely.h>
#include <category/mpt/config.hpp>
#include <category/mpt/deserialize_node_from_receiver_result.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/node_cursor.hpp>
#include <category/mpt/request.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/update.hpp>
#include <category/mpt/upward_tnode.hpp>
#include <category/mpt/util.hpp>

#include <quill/Quill.h>

#include <algorithm>
#include <bit>
#include <cassert>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <memory>
#include <optional>
#include <span>
#include <utility>
#include <vector>

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

template <any_tnode Parent>
void compact_(
    UpdateAuxImpl &, StateMachine &, Parent &, unsigned index, Node::SharedPtr,
    chunk_offset_t node_offset, bool copy_node_for_fast_or_slow);

void expire_(
    UpdateAuxImpl &, StateMachine &, UpdateExpireBase &parent, unsigned branch,
    unsigned index, Node::SharedPtr node, chunk_offset_t node_offset,
    bool cache_node);

void try_fillin_parent_with_rewritten_node(
    UpdateAuxImpl &, CompactTNode::unique_ptr_type);

void try_fillin_parent_after_expiration(
    UpdateAuxImpl &, StateMachine &, ExpireTNode::unique_ptr_type);

void propagate_upward(UpdateAuxImpl &, StateMachine &, TNodeBase *);

void fillin_parent_after_expiration(
    UpdateAuxImpl &, Node::SharedPtr, UpdateExpireBase *const,
    uint8_t const index, uint8_t const branch, bool const cache_node);

struct async_write_node_result
{
    chunk_offset_t offset_written_to;
    unsigned bytes_appended;
    erased_connected_operation *io_state;
};

// invoke at the end of each block upsert
void flush_buffered_writes(UpdateAuxImpl &);
chunk_offset_t write_new_root_node(UpdateAuxImpl &, Node &, uint64_t);

void erase_child_from_parent(UpdateTNode &parent, ChildData &entry)
{
    parent.mask &= static_cast<uint16_t>(~(1u << entry.branch));
    entry.erase();
    parent.child_done();
}

void erase_child_from_parent(
    UpdateExpireBase &parent, uint8_t branch, uint8_t index)
{
    parent.mask &= static_cast<uint16_t>(~(1u << branch));
    if (parent.type == tnode_type::update) {
        static_cast<UpdateTNode *>(&parent)->children[index].erase();
    }
    parent.child_done();
}

template <std::derived_from<UpdateExpireBase> Parent>
void maybe_expire_or_compact_child(
    UpdateAuxImpl &aux, StateMachine &sm, Parent &tnode, unsigned index,
    unsigned branch, Node::SharedPtr &child_ptr, chunk_offset_t child_offset,
    int64_t subtrie_min_version, compact_offset_pair min_offsets)
{
    if constexpr (std::same_as<Parent, UpdateTNode>) {
        if (!aux.is_on_disk()) {
            tnode.child_done();
            return;
        }
    }
    if (sm.auto_expire() &&
        subtrie_min_version < aux.curr_upsert_auto_expire_version) {
        bool const cache = child_ptr != nullptr;
        expire_(
            aux,
            sm,
            tnode,
            branch,
            index,
            std::move(child_ptr),
            child_offset,
            cache);
        return;
    }
    if (sm.compact() && min_offsets.any_below(aux.compact_offsets)) {
        compact_(
            aux,
            sm,
            tnode,
            index,
            std::move(child_ptr),
            child_offset,
            min_offsets.fast_below(aux.compact_offsets));
    }
    else {
        tnode.child_done();
    }
}

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
        sentinel->child_done();
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
        auto const node = node_cursor.node;
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
    while (!tnode->npending && tnode->parent()) {
        MONAD_ASSERT(tnode->children.size()); // not a leaf
        auto *parent = tnode->parent();
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
    auto const &orig = tnode->node;
    auto const number_of_children = static_cast<size_t>(std::popcount(mask));
    if (number_of_children == 1 && !orig->has_value()) {
        auto const child_branch = static_cast<uint8_t>(std::countr_zero(mask));
        auto const child_index = orig->to_child_index(child_branch);
        auto const single_child = orig->move_next(child_index);
        if (!single_child) {
            node_receiver_t recv{
                [aux = &aux,
                 sm = sm.clone(),
                 tnode = std::move(tnode),
                 child_branch](Node::SharedPtr read_node) {
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
                        tnode->parent(),
                        tnode->index,
                        tnode->branch,
                        tnode->cache_node);
                    propagate_upward(*aux, *sm, tnode->parent());
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
    auto const orig_fast = orig->child_min_offset_fast_data();
    auto const orig_slow = orig->child_min_offset_slow_data();
    auto const orig_ver = orig->child_min_version_data();
    auto const node_fast = node->child_min_offset_fast_data();
    auto const node_slow = node->child_min_offset_slow_data();
    auto const node_ver = node->child_min_version_data();
    for (unsigned j = 0; j < number_of_children; ++j) {
        auto const orig_j = orig_indexes[j];
        node->set_fnext(j, orig->fnext(orig_j));
        node_fast[j] = orig_fast[orig_j];
        node_slow[j] = orig_slow[orig_j];
        auto const ver = orig_ver[orig_j];
        MONAD_ASSERT(ver >= aux.curr_upsert_auto_expire_version);
        node_ver[j] = ver;
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
                   ? make_node(0, {}, path, leaf_data, {}, version)
                   : Node::SharedPtr{};
    }
    else if (number_of_children == 1 && !leaf_data.has_value()) {
        auto const j = bitmask_index(
            orig_mask, static_cast<unsigned>(std::countr_zero(mask)));
        MONAD_ASSERT(children[j].ptr);
        auto const node = std::move(children[j].ptr);
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
    MONAD_ASSERT(
        number_of_children > 1 ||
        (number_of_children == 1 && leaf_data.has_value()));
    // write children to disk, free any if exceeds the cache level limit
    if (aux.is_on_disk()) {
        for (auto &child : children) {
            if (child.is_valid() && child.offset == INVALID_OFFSET) {
                // write updated node or node to be compacted to disk
                // won't duplicate write of unchanged old child
                MONAD_ASSERT(child.branch < 16);
                MONAD_ASSERT(child.ptr);
                child.offset =
                    async_write_node_set_spare(aux, *child.ptr, true);
                auto const child_virtual_offset =
                    aux.physical_to_virtual(child.offset);
                MONAD_ASSERT(child_virtual_offset != INVALID_VIRTUAL_OFFSET);
                child.min_offsets =
                    calc_min_offsets(*child.ptr, child_virtual_offset);
                MONAD_ASSERT(
                    !(sm.compact() &&
                      child.min_offsets.any_below(aux.compact_offsets)));
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
        auto const &child = tnode->children[bitmask_index(
            tnode->orig_mask,
            static_cast<unsigned>(std::countr_zero(tnode->mask)))];
        if (!child.ptr) {
            MONAD_ASSERT(aux.is_on_disk());
            MONAD_ASSERT(child.offset != INVALID_OFFSET);
            { // some sanity checks
                auto const virtual_child_offset =
                    aux.physical_to_virtual(child.offset);
                MONAD_ASSERT(virtual_child_offset != INVALID_VIRTUAL_OFFSET);
                // child offset is older than current node writer's start offset
                MONAD_ASSERT(
                    virtual_child_offset <
                    aux.physical_to_virtual((virtual_child_offset.in_fast_list()
                                                 ? aux.node_writer_fast
                                                 : aux.node_writer_slow)
                                                ->sender()
                                                .offset()));
            }
            node_receiver_t recv{
                [aux = &aux, sm = sm.clone(), tnode = std::move(tnode)](
                    Node::SharedPtr read_node) mutable {
                    auto *parent = tnode->parent();
                    MONAD_ASSERT(parent);
                    auto &entry = parent->children[tnode->child_index()];
                    MONAD_ASSERT(entry.branch < 16);
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
            MONAD_ASSERT(parent.npending);
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
    MONAD_ASSERT(entry.branch < 16);
    if (node) {
        parent.version = std::max(parent.version, node->version);
        entry.finalize(std::move(node), sm.get_compute(), sm.cache());
        if (sm.auto_expire()) {
            MONAD_ASSERT(
                entry.subtrie_min_version >=
                aux.curr_upsert_auto_expire_version);
        }
        parent.child_done();
    }
    else {
        erase_child_from_parent(parent, entry);
    }
}

void update_value_and_subtrie_(
    UpdateAuxImpl &aux, StateMachine &sm, UpdateTNode &parent, ChildData &entry,
    Node::SharedPtr old, NibblesView const path, Update &update)
{
    if (update.is_deletion()) {
        erase_child_from_parent(parent, entry);
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
        parent.child_done();
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
        MONAD_ASSERT(update.value.has_value());
        auto const path = update.key.substr(prefix_index);
        for (auto i = 0u; i < path.nibble_size(); ++i) {
            sm.down(path.get(i));
        }
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
        auto const branch = requests.get_first_branch();
        sm.down(branch);
        updates = std::move(requests[branch]);
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
            std::move(requests[branch]),
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
        NibblesView const path = old->path_nibble_view().substr(
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
        unsigned const number_of_sublists =
            requests.split_into_sublists(std::move(updates), prefix_index);
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
        if (auto const old_nibble =
                old->path_nibble_view().get(old_prefix_index);
            number_of_sublists == 1 &&
            requests.get_first_branch() == old_nibble) {
            MONAD_ASSERT(requests.opt_leaf == std::nullopt);
            updates = std::move(requests[old_nibble]);
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
        (void)tnode.release();
    }
    else {
        create_node_compute_data_possibly_async(
            aux, sm, parent, entry, std::move(tnode));
    }
} // NOLINT(clang-analyzer-unix.Malloc)
  // this is related to the `tnode.release()` call above

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
    MONAD_ASSERT(tnode->children.size() == size_t(std::popcount(orig_mask)));
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
                    std::move(requests[branch]),
                    prefix_index + 1);
                sm.up(1);
            }
            else {
                create_new_trie_(
                    aux,
                    sm,
                    tnode->version,
                    children[index],
                    std::move(requests[branch]),
                    prefix_index + 1);
                tnode->child_done();
                sm.up(1);
            }
        }
        else if ((1 << branch) & old->mask) {
            auto &child = children[index];
            child.copy_old_child(old, branch);
            maybe_expire_or_compact_child(
                aux,
                sm,
                *tnode,
                index,
                branch,
                child.ptr,
                child.offset,
                child.subtrie_min_version,
                child.min_offsets);
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
    MONAD_ASSERT(old.has_path());
    // Note: no leaf can be created at an existing non-leaf node
    MONAD_ASSERT(!requests.opt_leaf.has_value());
    unsigned char const old_nibble =
        old.path_nibble_view().get(old_prefix_index);
    uint16_t const orig_mask =
        static_cast<uint16_t>(1u << old_nibble | requests.mask);
    auto tnode = make_tnode(orig_mask, &parent, entry.branch, path);
    auto const number_of_children =
        static_cast<unsigned>(std::popcount(orig_mask));
    MONAD_ASSERT(
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
                    old_ptr,
                    INVALID_OFFSET,
                    std::move(requests[branch]),
                    prefix_index + 1,
                    old_prefix_index + 1);
            }
            else {
                create_new_trie_(
                    aux,
                    sm,
                    tnode->version,
                    children[index],
                    std::move(requests[branch]),
                    prefix_index + 1);
                tnode->child_done();
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
            MONAD_ASSERT(child.offset == INVALID_OFFSET);
            // Note that it is possible that we recreate this node later after
            // done expiring all subtries under it
            sm.up(path_suffix.nibble_size() + 1);
            auto const child_min_offsets = aux.is_on_disk()
                                               ? calc_min_offsets(*child.ptr)
                                               : compact_offset_pair{};
            maybe_expire_or_compact_child(
                aux,
                sm,
                *tnode,
                index,
                branch,
                child.ptr,
                INVALID_OFFSET,
                child.subtrie_min_version,
                child_min_offsets);
        }
    }
    fillin_entry(aux, sm, std::move(tnode), parent, entry);
}

void expire_(
    UpdateAuxImpl &aux, StateMachine &sm, UpdateExpireBase &parent,
    unsigned const branch, unsigned const index, Node::SharedPtr node,
    chunk_offset_t const node_offset, bool const cache_node)
{
    if (!node) {
        MONAD_ASSERT(node_offset != INVALID_OFFSET);
        node_receiver_t recv{
            [aux = &aux, sm = sm.clone(), parent = &parent, branch, index](
                Node::SharedPtr read_node) {
                expire_(
                    *aux,
                    *sm,
                    *parent,
                    branch,
                    index,
                    std::move(read_node),
                    INVALID_OFFSET,
                    false);
                propagate_upward(*aux, *sm, parent);
            },
            node_offset};
        aux.collect_expire_stats(true);
        async_read(aux, std::move(recv));
        return;
    }
    MONAD_ASSERT(sm.auto_expire() == true && sm.compact() == true);
    if (node->version < aux.curr_upsert_auto_expire_version) {
        // entire subtrie is expired, erase from parent
        erase_child_from_parent(
            parent, static_cast<uint8_t>(branch), static_cast<uint8_t>(index));
        return;
    }
    // Only create ExpireTNode when dispatching to children.
    MONAD_ASSERT(node->mask);
    auto tnode = ExpireTNode::make(
        &parent,
        branch,
        index,
        cache_node || parent.type == tnode_type::update,
        std::move(node));
    for (auto const [ci, cb] : NodeChildrenRange(tnode->node->mask)) {
        auto child_ptr = tnode->node->move_next(ci);
        maybe_expire_or_compact_child(
            aux,
            sm,
            *tnode,
            ci,
            cb,
            child_ptr,
            tnode->node->fnext(ci),
            tnode->node->subtrie_min_version(ci),
            tnode->node->min_offsets(ci));
    }
    try_fillin_parent_after_expiration(aux, sm, std::move(tnode));
}

void fillin_parent_after_expiration(
    UpdateAuxImpl &aux, Node::SharedPtr new_node,
    UpdateExpireBase *const parent, uint8_t const index, uint8_t const branch,
    bool const cache_node)
{
    if (new_node == nullptr) {
        // expire this branch from parent
        erase_child_from_parent(*parent, branch, index);
    }
    else {
        auto const new_offset =
            async_write_node_set_spare(aux, *new_node, true);
        auto const new_node_virtual_offset =
            aux.physical_to_virtual(new_offset);
        MONAD_ASSERT(new_node_virtual_offset != INVALID_VIRTUAL_OFFSET);
        auto const min_offsets =
            calc_min_offsets(*new_node, new_node_virtual_offset);
        MONAD_ASSERT(
            min_offsets.fast != INVALID_COMPACT_VIRTUAL_OFFSET ||
            min_offsets.slow != INVALID_COMPACT_VIRTUAL_OFFSET);
        auto const min_version = calc_min_version(*new_node);
        MONAD_ASSERT(min_version >= aux.curr_upsert_auto_expire_version);
        if (parent->type == tnode_type::update) {
            auto &child = static_cast<UpdateTNode *>(parent)->children[index];
            MONAD_ASSERT(!child.ptr); // been transferred to tnode
            child.offset = new_offset;
            MONAD_ASSERT(cache_node);
            child.ptr = std::move(new_node);
            child.min_offsets = min_offsets;
            child.subtrie_min_version = min_version;
        }
        else {
            MONAD_ASSERT(parent->type == tnode_type::expire);
            auto *const expire_parent = static_cast<ExpireTNode *>(parent);
            if (cache_node) {
                expire_parent->cache_mask |= static_cast<uint16_t>(1u << index);
            }
            expire_parent->node->set_next(index, std::move(new_node));
            expire_parent->node->set_subtrie_min_version(index, min_version);
            expire_parent->node->set_min_offsets(index, min_offsets);
            expire_parent->node->set_fnext(index, new_offset);
        }
        parent->child_done();
    }
}

void try_fillin_parent_after_expiration(
    UpdateAuxImpl &aux, StateMachine &sm, ExpireTNode::unique_ptr_type tnode)
{
    if (tnode->npending) {
        (void)tnode.release();
        return; // NOLINT(clang-analyzer-unix.Malloc) -- tnode is kept alive by
                // raw-ptr ownership until children call child_done()
    }
    auto const index = tnode->index;
    auto const branch = tnode->branch;
    auto *const parent = tnode->parent();
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

template <any_tnode Parent>
void compact_(
    UpdateAuxImpl &aux, StateMachine &sm, Parent &parent, unsigned const index,
    Node::SharedPtr node, chunk_offset_t const node_offset,
    bool const copy_node_for_fast_or_slow)
{
    if (!node) {
        MONAD_ASSERT(node_offset != INVALID_OFFSET);
        node_receiver_t recv{
            [copy_node_for_fast_or_slow,
             node_offset,
             aux = &aux,
             sm = sm.clone(),
             parent = &parent,
             index](Node::SharedPtr read_node) {
                compact_(
                    *aux,
                    *sm,
                    *parent,
                    index,
                    std::move(read_node),
                    node_offset,
                    copy_node_for_fast_or_slow);
                propagate_upward(*aux, *sm, parent);
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
    bool rewrite_to_fast = true;
    if (virtual_node_offset != INVALID_VIRTUAL_OFFSET) {
        compact_virtual_chunk_offset_t const compacted_virtual_offset{
            virtual_node_offset};
        auto const threshold = virtual_node_offset.in_fast_list()
                                   ? aux.compact_offsets.fast
                                   : aux.compact_offsets.slow;
        rewrite_to_fast = compacted_virtual_offset >= threshold;
    }

    // Only create CompactTNode when dispatching to children.
    auto tnode = CompactTNode::make(&parent, index, std::move(node));
    Node &compact_node = *tnode->node;
    tnode->rewrite_to_fast = rewrite_to_fast;
    aux.collect_compacted_nodes_stats(
        copy_node_for_fast_or_slow,
        rewrite_to_fast,
        virtual_node_offset,
        compact_node.get_disk_size());

    unsigned const n = compact_node.number_of_children();
    auto const fast = compact_node.child_min_offset_fast_data();
    auto const slow = compact_node.child_min_offset_slow_data();
    for (unsigned j = 0; j < n; ++j) {
        auto child_ptr = compact_node.move_next(j);
        compact_offset_pair const child_min_offsets{fast[j], slow[j]};
        if (sm.compact() && child_min_offsets.any_below(aux.compact_offsets)) {
            compact_(
                aux,
                sm,
                *tnode,
                j,
                std::move(child_ptr),
                compact_node.fnext(j),
                child_min_offsets.fast_below(aux.compact_offsets));
        }
        else {
            tnode->child_done();
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
        (void)tnode.release();
        return; // NOLINT(clang-analyzer-unix.Malloc)
    }
    auto min_offsets = calc_min_offsets(*tnode->node, INVALID_VIRTUAL_OFFSET);
    // If subtrie contains nodes from fast list, write itself to fast list too
    if (min_offsets.fast != INVALID_COMPACT_VIRTUAL_OFFSET) {
        tnode->rewrite_to_fast = true; // override that
    }
    auto const new_offset =
        async_write_node_set_spare(aux, *tnode->node, tnode->rewrite_to_fast);
    auto const new_node_virtual_offset = aux.physical_to_virtual(new_offset);
    MONAD_ASSERT(new_node_virtual_offset != INVALID_VIRTUAL_OFFSET);
    compact_virtual_chunk_offset_t const truncated_new_virtual_offset{
        new_node_virtual_offset};
    // update min offsets in subtrie
    if (tnode->rewrite_to_fast) {
        min_offsets.fast =
            std::min(min_offsets.fast, truncated_new_virtual_offset);
    }
    else {
        min_offsets.slow =
            std::min(min_offsets.slow, truncated_new_virtual_offset);
    }
    MONAD_ASSERT(!min_offsets.any_below(aux.compact_offsets));
    TNodeBase *parent = tnode->parent();
    auto const index = tnode->index;
    if (parent->type == tnode_type::update) {
        auto *const p = static_cast<UpdateTNode *>(parent);
        MONAD_ASSERT(tnode->cache_node);
        auto &child = p->children[index];
        child.ptr = std::move(tnode->node);
        child.offset = new_offset;
        child.min_offsets = min_offsets;
    }
    else if (parent->type == tnode_type::compact) {
        auto *const p = static_cast<CompactTNode *>(parent);
        MONAD_ASSERT(p->node);
        p->node->set_fnext(index, new_offset);
        p->node->set_min_offsets(index, min_offsets);
        if (tnode->cache_node) {
            p->node->set_next(index, std::move(tnode->node));
        }
    }
    else {
        MONAD_ASSERT(parent->type == tnode_type::expire);
        auto *const p = static_cast<ExpireTNode *>(parent);
        MONAD_ASSERT(p->node);
        p->node->set_fnext(index, new_offset);
        p->node->set_min_offsets(index, min_offsets);
        // Delay tnode->node deallocation to parent ExpireTNode
        p->node->set_next(index, std::move(tnode->node));
        if (tnode->cache_node) {
            p->cache_mask |= static_cast<uint16_t>(1u << tnode->index);
        }
    }
    parent->child_done();
}

void propagate_upward(UpdateAuxImpl &aux, StateMachine &sm, TNodeBase *parent)
{
    while (!parent->npending) {
        if (parent->type == tnode_type::update) {
            upward_update(aux, sm, static_cast<UpdateTNode *>(parent));
            return;
        }
        auto *next_parent = parent->parent();
        MONAD_ASSERT(next_parent);
        if (parent->type == tnode_type::compact) {
            try_fillin_parent_with_rewritten_node(
                aux,
                CompactTNode::unique_ptr_type{
                    static_cast<CompactTNode *>(parent)});
        }
        else {
            MONAD_ASSERT(parent->type == tnode_type::expire);
            try_fillin_parent_after_expiration(
                aux,
                sm,
                ExpireTNode::unique_ptr_type{
                    static_cast<ExpireTNode *>(parent)});
        }
        parent = next_parent;
    }
}

/////////////////////////////////////////////////////
// Async write
/////////////////////////////////////////////////////

node_writer_unique_ptr_type replace_node_writer_to_start_at_new_chunk(
    UpdateAuxImpl &aux, node_writer_unique_ptr_type &node_writer)
{
    auto *sender = &node_writer->sender();
    bool const in_fast_list =
        aux.db_metadata()->at(sender->offset().id)->in_fast_list;
    aux.assert_seq_chunk_budget();
    auto const idx = aux.io->storage_pool().allocate_seq_chunk(aux.db_id_);
    MONAD_ASSERT(idx != MONAD_ASYNC_NAMESPACE::storage_pool::ALLOC_FAILED);
    chunk_offset_t const offset_of_new_writer{idx, 0};
    // Pad buffer of existing node write that is about to get initiated so it's
    // O_DIRECT i/o aligned
    auto const remaining_buffer_bytes = sender->remaining_buffer_bytes();
    auto *tozero = sender->advance_buffer_append(remaining_buffer_bytes);
    MONAD_ASSERT(tozero != nullptr);
    memset(tozero, 0, remaining_buffer_bytes);

    /* If there aren't enough write buffers, this may poll uring until a free
    write buffer appears. However, that polling may write a node, causing
    this function to be reentered, and another free chunk allocated and now
    writes are being directed there instead. Obviously then replacing that new
    partially filled chunk with this new chunk is something which trips the
    asserts.

    Replacing the runloop exposed this bug much more clearly than before, but we
    had been seeing occasional issues somewhere around here for some time now,
    it just wasn't obvious the cause. Anyway detect when reentrancy occurs, and
    if so undo this operation and tell the caller to retry.
    */
    static thread_local struct reentrancy_detection_t
    {
        int count{0}, max_count{0};
    } reentrancy_detection;

    int const my_reentrancy_count = reentrancy_detection.count++;
    MONAD_ASSERT(my_reentrancy_count >= 0);
    if (my_reentrancy_count == 0) {
        // We are at the base
        reentrancy_detection.max_count = 0;
    }
    else if (my_reentrancy_count > reentrancy_detection.max_count) {
        // We are reentering
        LOG_INFO_CFORMAT(
            "replace_node_writer_to_start_at_new_chunk reenter "
            "my_reentrancy_count = "
            "%d max_count = %d",
            my_reentrancy_count,
            reentrancy_detection.max_count);
        reentrancy_detection.max_count = my_reentrancy_count;
    }
    auto ret = aux.io->make_connected(
        write_single_buffer_sender{
            offset_of_new_writer, AsyncIO::WRITE_BUFFER_SIZE},
        write_operation_io_receiver{AsyncIO::WRITE_BUFFER_SIZE});
    reentrancy_detection.count--;
    MONAD_ASSERT(reentrancy_detection.count >= 0);
    // The deepest-most reentrancy must succeed, and all less deep reentrancies
    // must retry
    if (my_reentrancy_count != reentrancy_detection.max_count) {
        // We reentered, please retry
        LOG_INFO_CFORMAT(
            "replace_node_writer_to_start_at_new_chunk retry "
            "my_reentrancy_count = "
            "%d max_count = %d",
            my_reentrancy_count,
            reentrancy_detection.max_count);
        aux.io->storage_pool().free_seq_chunk(idx);
        return {};
    }
    aux.append(
        in_fast_list ? UpdateAuxImpl::chunk_list::fast
                     : UpdateAuxImpl::chunk_list::slow,
        idx);
    aux.io->storage_pool().commit_seq_chunk(idx);
    return ret;
}

node_writer_unique_ptr_type replace_node_writer(
    UpdateAuxImpl &aux, node_writer_unique_ptr_type const &node_writer)
{
    // Can't use add_to_offset(), because it asserts if we go past the
    // capacity
    auto offset_of_next_writer = node_writer->sender().offset();
    bool const in_fast_list =
        aux.db_metadata()->at(offset_of_next_writer.id)->in_fast_list;
    file_offset_t offset = offset_of_next_writer.offset;
    offset += node_writer->sender().written_buffer_bytes();
    offset_of_next_writer.offset = offset & chunk_offset_t::max_offset;
    auto const chunk_capacity =
        aux.io->chunk_capacity(offset_of_next_writer.id);
    MONAD_ASSERT(offset <= chunk_capacity);
    bool new_chunk = false;
    uint32_t idx;
    if (offset == chunk_capacity) {
        // If after the current write buffer we're hitting chunk capacity, we
        // replace writer to the start of next chunk.
        aux.assert_seq_chunk_budget();
        idx = aux.io->storage_pool().allocate_seq_chunk(aux.db_id_);
        MONAD_ASSERT(idx != MONAD_ASYNC_NAMESPACE::storage_pool::ALLOC_FAILED);
        new_chunk = true;
        offset_of_next_writer.id = idx & 0xfffffU;
        offset_of_next_writer.offset = 0;
    }
    // See above about handling potential reentrancy correctly
    auto *const node_writer_ptr = node_writer.get();
    size_t const bytes_to_write = std::min(
        AsyncIO::WRITE_BUFFER_SIZE,
        (size_t)(chunk_capacity - offset_of_next_writer.offset));
    auto ret = aux.io->make_connected(
        write_single_buffer_sender{offset_of_next_writer, bytes_to_write},
        write_operation_io_receiver{bytes_to_write});
    if (node_writer.get() != node_writer_ptr) {
        // We reentered, please retry
        if (new_chunk) {
            aux.io->storage_pool().free_seq_chunk(idx);
        }
        return {};
    }
    if (new_chunk) {
        aux.append(
            in_fast_list ? UpdateAuxImpl::chunk_list::fast
                         : UpdateAuxImpl::chunk_list::slow,
            idx);
        aux.io->storage_pool().commit_seq_chunk(idx);
    }
    return ret;
}

// return physical offset the node is written at
async_write_node_result async_write_node(
    UpdateAuxImpl &aux, node_writer_unique_ptr_type &node_writer,
    Node const &node)
{
retry:
    aux.io->poll_nonblocking_if_not_within_completions(1);
    auto *sender = &node_writer->sender();
    auto const size = node.get_disk_size();
    auto const remaining_bytes = sender->remaining_buffer_bytes();
    async_write_node_result ret{
        .offset_written_to = INVALID_OFFSET,
        .bytes_appended = size,
        .io_state = node_writer.get()};
    [[likely]] if (size <= remaining_bytes) { // Node can fit into current
                                              // buffer
        ret.offset_written_to =
            sender->offset().add_to_offset(sender->written_buffer_bytes());
        auto *where_to_serialize = sender->advance_buffer_append(size);
        MONAD_ASSERT(where_to_serialize != nullptr);
        serialize_node_to_buffer(
            (unsigned char *)where_to_serialize, size, node, size);
    }
    else {
        auto const chunk_remaining_bytes =
            aux.io->chunk_capacity(sender->offset().id) -
            sender->offset().offset - sender->written_buffer_bytes();
        node_writer_unique_ptr_type new_node_writer{};
        unsigned offset_in_on_disk_node = 0;
        if (size > chunk_remaining_bytes) {
            // Node won't fit in the rest of current chunk, start at a new chunk
            new_node_writer =
                replace_node_writer_to_start_at_new_chunk(aux, node_writer);
            if (!new_node_writer) {
                goto retry;
            }
            ret.offset_written_to = new_node_writer->sender().offset();
        }
        else {
            // serialize node to current writer's remaining bytes because node
            // serialization will not cross chunk boundary
            ret.offset_written_to =
                sender->offset().add_to_offset(sender->written_buffer_bytes());
            auto const bytes_to_append = std::min(
                (unsigned)remaining_bytes, size - offset_in_on_disk_node);
            auto *where_to_serialize =
                (unsigned char *)node_writer->sender().advance_buffer_append(
                    bytes_to_append);
            MONAD_ASSERT(where_to_serialize != nullptr);
            serialize_node_to_buffer(
                where_to_serialize,
                bytes_to_append,
                node,
                size,
                offset_in_on_disk_node);
            offset_in_on_disk_node += bytes_to_append;
            new_node_writer = replace_node_writer(aux, node_writer);
            if (!new_node_writer) {
                goto retry;
            }
            MONAD_ASSERT(
                new_node_writer->sender().offset().id ==
                node_writer->sender().offset().id);
        }
        // initiate current node writer
        if (node_writer->sender().written_buffer_bytes() !=
            node_writer->sender().buffer().size()) {
            LOG_INFO_CFORMAT(
                "async_write_node %zu != %zu",
                node_writer->sender().written_buffer_bytes(),
                node_writer->sender().buffer().size());
        }
        MONAD_ASSERT(
            node_writer->sender().written_buffer_bytes() ==
            node_writer->sender().buffer().size());
        node_writer->initiate();
        // shall be recycled by the i/o receiver
        (void)node_writer.release();
        node_writer = std::move(new_node_writer);
        // serialize the rest of the node to buffer
        while (offset_in_on_disk_node < size) {
            auto *where_to_serialize =
                (unsigned char *)node_writer->sender().buffer().data();
            auto const bytes_to_append = std::min(
                (unsigned)node_writer->sender().remaining_buffer_bytes(),
                size - offset_in_on_disk_node);
            serialize_node_to_buffer(
                where_to_serialize,
                bytes_to_append,
                node,
                size,
                offset_in_on_disk_node);
            offset_in_on_disk_node += bytes_to_append;
            MONAD_ASSERT(offset_in_on_disk_node <= size);
            MONAD_ASSERT(
                node_writer->sender().advance_buffer_append(bytes_to_append) !=
                nullptr);
            if (offset_in_on_disk_node < size &&
                node_writer->sender().remaining_buffer_bytes() == 0) {
                // replace node writer
                new_node_writer = replace_node_writer(aux, node_writer);
                if (!new_node_writer) {
                    // Reentrance: the reentrant call may have interleaved
                    // data into the writer, so continuing would make this
                    // node non-contiguous on disk. Retry the entire write.
                    goto retry;
                }
                // initiate current node writer
                MONAD_ASSERT(
                    node_writer->sender().written_buffer_bytes() ==
                    node_writer->sender().buffer().size());
                node_writer->initiate();
                // shall be recycled by the i/o receiver
                (void)node_writer.release();
                node_writer = std::move(new_node_writer);
            }
        }
    }
    return ret;
}

// Return node's physical offset the node is written at, triedb should not
// depend on any metadata to walk the data structure.
chunk_offset_t
async_write_node_set_spare(UpdateAuxImpl &aux, Node &node, bool write_to_fast)
{
    write_to_fast &= aux.can_write_to_fast();
    if (aux.alternate_slow_fast_writer()) {
        // alternate between slow and fast writer
        aux.set_can_write_to_fast(!aux.can_write_to_fast());
    }

    auto off = async_write_node(
                   aux,
                   write_to_fast ? aux.node_writer_fast : aux.node_writer_slow,
                   node)
                   .offset_written_to;
    MONAD_ASSERT(
        (write_to_fast && aux.db_metadata()->at(off.id)->in_fast_list) ||
        (!write_to_fast && aux.db_metadata()->at(off.id)->in_slow_list));
    unsigned const pages = num_pages(off.offset, node.get_disk_size());
    off.set_spare(static_cast<uint16_t>(node_disk_pages_spare_15{pages}));
    return off;
}

void flush_buffered_writes(UpdateAuxImpl &aux)
{
    // Round up with all bits zero
    auto replace = [&](node_writer_unique_ptr_type &node_writer) {
        auto *sender = &node_writer->sender();
        auto const written = sender->written_buffer_bytes();
        auto const paddedup = round_up_align<DISK_PAGE_BITS>(written);
        auto const tozerobytes = paddedup - written;
        auto *tozero = sender->advance_buffer_append(tozerobytes);
        MONAD_ASSERT(tozero != nullptr);
        memset(tozero, 0, tozerobytes);
        // replace fast node writer
        auto new_node_writer = replace_node_writer(aux, node_writer);
        while (!new_node_writer) {
            new_node_writer = replace_node_writer(aux, node_writer);
        }
        auto to_initiate = std::move(node_writer);
        node_writer = std::move(new_node_writer);
        to_initiate->receiver().reset(
            to_initiate->sender().written_buffer_bytes());
        to_initiate->initiate();
        // shall be recycled by the i/o receiver
        (void)to_initiate.release();
    };
    replace(aux.node_writer_fast);
    if (aux.node_writer_slow->sender().written_buffer_bytes()) {
        // replace slow node writer
        replace(aux.node_writer_slow);
    }
    aux.io->flush();
}

// return root physical offset
chunk_offset_t
write_new_root_node(UpdateAuxImpl &aux, Node &root, uint64_t const version)
{
    auto const offset_written_to = async_write_node_set_spare(aux, root, true);
    flush_buffered_writes(aux);
    // advance fast and slow ring's latest offset in db metadata
    aux.advance_db_offsets_to(
        aux.node_writer_fast->sender().offset(),
        aux.node_writer_slow->sender().offset());
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

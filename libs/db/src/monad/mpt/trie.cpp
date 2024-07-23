#include <monad/mpt/trie.hpp>

#include <monad/async/concepts.hpp>
#include <monad/async/config.hpp>
#include <monad/async/erased_connected_operation.hpp>
#include <monad/async/io_senders.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/nibble.h>
#include <monad/mem/allocators.hpp>
#include <monad/mpt/config.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/request.hpp>
#include <monad/mpt/state_machine.hpp>
#include <monad/mpt/update.hpp>
#include <monad/mpt/upward_tnode.hpp>
#include <monad/mpt/util.hpp>

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

#include "deserialize_node_from_receiver_result.hpp"

MONAD_MPT_NAMESPACE_BEGIN

using namespace MONAD_ASYNC_NAMESPACE;

/* Names: `prefix_index` is nibble index in prefix of an update,
 `old_prefix_index` is nibble index of path in previous node - old.
 `*_prefix_index_start` is the starting nibble index in current function frame
*/
void dispatch_updates_flat_list_(
    UpdateAuxImpl &, StateMachine &, UpwardTreeNode &parent, ChildData &,
    Node::UniquePtr old, Requests &, NibblesView path, unsigned prefix_index);

void dispatch_updates_impl_(
    UpdateAuxImpl &, StateMachine &, UpwardTreeNode &parent, ChildData &,
    Node::UniquePtr old, Requests &, unsigned prefix_index, NibblesView path,
    std::optional<byte_string_view> opt_leaf_data, int64_t version);

void mismatch_handler_(
    UpdateAuxImpl &, StateMachine &, UpwardTreeNode &parent, ChildData &,
    Node::UniquePtr old, Requests &, NibblesView path,
    unsigned old_prefix_index, unsigned prefix_index);

void create_new_trie_(
    UpdateAuxImpl &aux, StateMachine &sm, int64_t &parent_version,
    ChildData &entry, UpdateList &&updates, unsigned prefix_index = 0);

void create_new_trie_from_requests_(
    UpdateAuxImpl &, StateMachine &, int64_t &parent_version, ChildData &,
    Requests &, NibblesView path, unsigned prefix_index,
    std::optional<byte_string_view> opt_leaf_data, int64_t version);

void upsert_(
    UpdateAuxImpl &, StateMachine &, UpwardTreeNode &parent, ChildData &,
    Node::UniquePtr old, chunk_offset_t offset, UpdateList &&,
    unsigned prefix_index = 0, unsigned old_prefix_index = 0);

void create_node_compute_data_possibly_async(
    UpdateAuxImpl &, StateMachine &, UpwardTreeNode &parent, ChildData &,
    tnode_unique_ptr, bool might_on_disk = true);

void compact_(
    UpdateAuxImpl &, StateMachine &, CompactTNode *parent, unsigned index,
    Node *, bool cached, chunk_offset_t node_offset,
    bool copy_node_for_fast_or_slow);

void try_fillin_parent_with_rewritten_node(
    UpdateAuxImpl &, CompactTNode::unique_ptr_type);

struct async_write_node_result
{
    chunk_offset_t offset_written_to;
    unsigned bytes_appended;
    erased_connected_operation *io_state;
};

// invoke at the end of each block upsert
chunk_offset_t write_new_root_node(UpdateAuxImpl &, Node &, uint64_t);

Node::UniquePtr upsert(
    UpdateAuxImpl &aux, uint64_t const version, StateMachine &sm,
    Node::UniquePtr old, UpdateList &&updates)
{
    auto impl = [&] {
        aux.reset_stats();
        auto sentinel = make_tnode(1 /*mask*/, 0 /*prefix_index*/);
        ChildData &entry = sentinel->children[0];
        sentinel->children[0] = ChildData{.branch = 0};
        if (old) {
            upsert_(
                aux,
                sm,
                *sentinel,
                entry,
                std::move(old),
                INVALID_OFFSET,
                std::move(updates));
            if (sentinel->npending) {
                aux.io->flush();
                MONAD_ASSERT(sentinel->npending == 0);
            }
        }
        else {
            create_new_trie_(
                aux, sm, sentinel->version, entry, std::move(updates));
        }
        auto *const root = entry.ptr;
        if (aux.is_on_disk()) {
            if (root) {
                write_new_root_node(aux, *root, version);
            }
            aux.print_update_stats();
        }
        return Node::UniquePtr{root};
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
            Node *node;
            {
                auto g(impl->aux.unique_lock());
                MONAD_ASSERT(root.node->next(branch_index) == nullptr);
                node = detail::deserialize_node_from_receiver_result(
                           std::move(buffer_), buffer_off, io_state)
                           .release();
                root.node->set_next(branch_index, node);
                impl->nodes_loaded++;
            }
            impl->process(NodeCursor{*node}, *sm);
        }
    };

    explicit constexpr load_all_impl_(UpdateAuxImpl &aux)
        : aux(aux)
    {
    }

    void process(NodeCursor const node_cursor, StateMachine &sm)
    {
        Node *const node = node_cursor.node;
        for (unsigned i = 0, idx = 0, bit = 1; idx < node->number_of_children();
             ++i, bit <<= 1) {
            if (node->mask & bit) {
                NibblesView const nv(
                    node_cursor.prefix_index,
                    node->path_nibble_index_end,
                    node->path_data());
                for (uint8_t n = 0; n < nv.nibble_size(); n++) {
                    sm.down(nv.get(n));
                }
                sm.down((unsigned char)i);
                if (sm.cache()) {
                    auto *const next = node->next(idx);
                    if (next == nullptr) {
                        receiver_t receiver(
                            this, *node, uint8_t(idx), sm.clone());
                        async_read(aux, std::move(receiver));
                    }
                    else {
                        process(NodeCursor{*next}, sm);
                    }
                }
                sm.up(1 + nv.nibble_size());
                ++idx;
            }
        }
    }
};

size_t load_all(UpdateAuxImpl &aux, StateMachine &sm, NodeCursor const root)
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
void upward_update(UpdateAuxImpl &aux, StateMachine &sm, UpwardTreeNode *tnode)
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

struct update_receiver
{
    static constexpr bool lifetime_managed_internally = true;

    UpdateAuxImpl *aux;
    std::unique_ptr<StateMachine> sm;
    UpdateList updates;
    UpwardTreeNode *parent;
    ChildData &entry;
    chunk_offset_t rd_offset;
    unsigned bytes_to_read;
    uint16_t buffer_off;
    uint8_t prefix_index;

    update_receiver(
        UpdateAuxImpl *aux, std::unique_ptr<StateMachine> sm, ChildData &entry,
        chunk_offset_t offset, UpdateList &&updates, UpwardTreeNode *parent,
        unsigned const prefix_index)
        : aux(aux)
        , sm(std::move(sm))
        , updates(std::move(updates))
        , parent(parent)
        , entry(entry)
        , rd_offset(round_down_align<DISK_PAGE_BITS>(offset))
        , prefix_index(static_cast<uint8_t>(prefix_index))
    {
        // prep uring data
        buffer_off = uint16_t(offset.offset - rd_offset.offset);
        // spare bits are number of pages needed to load node
        auto const num_pages_to_load_node =
            node_disk_pages_spare_15(rd_offset).to_pages();
        MONAD_DEBUG_ASSERT(
            num_pages_to_load_node <=
            round_up_align<DISK_PAGE_BITS>(Node::max_disk_size));
        bytes_to_read =
            static_cast<unsigned>(num_pages_to_load_node << DISK_PAGE_BITS);
        rd_offset.set_spare(0);
    }

    template <class ResultType>
    void set_value(erased_connected_operation *io_state, ResultType buffer_)
    {
        MONAD_ASSERT(buffer_);
        Node::UniquePtr old = detail::deserialize_node_from_receiver_result(
            std::move(buffer_), buffer_off, io_state);
        // continue recurse down the trie starting from `old`
        unsigned const old_prefix_index = old->path_start_nibble();
        upsert_(
            *aux,
            *sm,
            *parent,
            entry,
            std::move(old),
            INVALID_OFFSET,
            std::move(updates),
            prefix_index,
            old_prefix_index);
        sm->up(1);
        upward_update(*aux, *sm, parent);
    }
};

static_assert(sizeof(update_receiver) == 64);
static_assert(alignof(update_receiver) == 8);

struct read_single_child_receiver
{
    static constexpr bool lifetime_managed_internally = true;

    UpdateAuxImpl *aux;
    chunk_offset_t rd_offset;
    UpwardTreeNode *tnode; // single child tnode
    ChildData &child;
    unsigned bytes_to_read;
    uint16_t buffer_off;
    std::unique_ptr<StateMachine> sm;

    read_single_child_receiver(
        UpdateAuxImpl *const aux, std::unique_ptr<StateMachine> sm,
        UpwardTreeNode *const tnode, ChildData &child)
        : aux(aux)
        , rd_offset(0, 0)
        , tnode(tnode)
        , child(child)
        , sm(std::move(sm))
    {
        // prep uring data
        if (auto const virtual_child_offset =
                aux->physical_to_virtual(child.offset);
            !virtual_child_offset.in_fast_list()) { // some sanity checks
            MONAD_DEBUG_ASSERT(
                virtual_child_offset.count <=
                aux->num_chunks(
                    virtual_child_offset.in_fast_list()
                        ? UpdateAuxImpl::chunk_list::fast
                        : UpdateAuxImpl::chunk_list::slow));
            // child offset is older than current node writer's start offset
            MONAD_DEBUG_ASSERT(
                virtual_child_offset <
                aux->physical_to_virtual((virtual_child_offset.in_fast_list()
                                              ? aux->node_writer_fast
                                              : aux->node_writer_slow)
                                             ->sender()
                                             .offset()));
        }
        rd_offset = round_down_align<DISK_PAGE_BITS>(child.offset);
        rd_offset.set_spare(0);
        buffer_off = uint16_t(child.offset.offset - rd_offset.offset);
        // spare bits are number of pages needed to load node
        auto const num_pages_to_load_node =
            node_disk_pages_spare_15{child.offset}.to_pages();
        MONAD_DEBUG_ASSERT(
            num_pages_to_load_node <=
            round_up_align<DISK_PAGE_BITS>(Node::max_disk_size));
        bytes_to_read =
            static_cast<unsigned>(num_pages_to_load_node << DISK_PAGE_BITS);
    }

    template <class ResultType>
    void set_value(erased_connected_operation *io_state, ResultType buffer_)
    {
        MONAD_ASSERT(buffer_);
        // load node from read buffer
        auto *parent = tnode->parent;
        MONAD_DEBUG_ASSERT(parent);
        auto &entry = parent->children[tnode->child_index()];
        MONAD_DEBUG_ASSERT(entry.branch < 16);
        auto &child = tnode->children[bitmask_index(
            tnode->orig_mask,
            static_cast<unsigned>(std::countr_zero(tnode->mask)))];
        child.ptr = detail::deserialize_node_from_receiver_result(
                        std::move(buffer_), buffer_off, io_state)
                        .release();
        auto const path_size = tnode->path.nibble_size();
        create_node_compute_data_possibly_async(
            *aux, *sm, *parent, entry, tnode_unique_ptr{tnode}, false);
        sm->up(path_size + !parent->is_sentinel());
        upward_update(*aux, *sm, parent);
    }
};

static_assert(sizeof(read_single_child_receiver) == 48);
static_assert(alignof(read_single_child_receiver) == 8);

struct compaction_receiver
{
    static constexpr bool lifetime_managed_internally = true;

    UpdateAuxImpl *aux;
    chunk_offset_t rd_offset;
    chunk_offset_t orig_offset;
    CompactTNode *tnode;
    uint8_t index;
    unsigned bytes_to_read;
    uint16_t buffer_off;
    std::unique_ptr<StateMachine> sm;
    bool copy_node_for_fast_or_slow;

    compaction_receiver(
        UpdateAuxImpl *aux_, std::unique_ptr<StateMachine> sm_,
        CompactTNode *tnode_, unsigned const index_,
        chunk_offset_t const offset, bool const copy_node_for_fast_or_slow_)
        : aux(aux_)
        , rd_offset({0, 0})
        , orig_offset(offset)
        , tnode(tnode_)
        , index(static_cast<uint8_t>(index_))
        , sm(std::move(sm_))
        , copy_node_for_fast_or_slow(copy_node_for_fast_or_slow_)
    {
        MONAD_ASSERT(tnode);
        rd_offset = round_down_align<DISK_PAGE_BITS>(offset);
        auto const num_pages_to_load_node =
            node_disk_pages_spare_15{rd_offset}.to_pages();
        buffer_off = uint16_t(offset.offset - rd_offset.offset);
        MONAD_DEBUG_ASSERT(
            num_pages_to_load_node <=
            round_up_align<DISK_PAGE_BITS>(Node::max_disk_size));
        bytes_to_read =
            static_cast<unsigned>(num_pages_to_load_node << DISK_PAGE_BITS);
        rd_offset.set_spare(0);

        aux->collect_compaction_read_stats(offset, bytes_to_read);
    }

    template <class ResultType>
    void set_value(erased_connected_operation *io_state, ResultType buffer_)
    {
        MONAD_ASSERT(buffer_);
        Node *node = detail::deserialize_node_from_receiver_result(
                         std::move(buffer_), buffer_off, io_state)
                         .release();
        compact_(
            *aux,
            *sm,
            tnode,
            index,
            node,
            false,
            orig_offset,
            copy_node_for_fast_or_slow);
        // now if tnode has everything it needs
        while (!tnode->npending) {
            if (tnode->type == tnode_type::update) {
                upward_update(*aux, *sm, (UpwardTreeNode *)tnode);
                return;
            }
            auto *parent = tnode->parent;
            MONAD_ASSERT(parent);
            // tnode is freed after this call
            try_fillin_parent_with_rewritten_node(
                *aux, CompactTNode::unique_ptr_type{tnode});
            // upward by one level
            tnode = parent;
        }
    }
};

/////////////////////////////////////////////////////
// Create Node
/////////////////////////////////////////////////////
Node *create_node_from_children_if_any(
    UpdateAuxImpl &aux, StateMachine &sm, uint16_t const orig_mask,
    uint16_t const mask, std::span<ChildData> children, NibblesView const path,
    std::optional<byte_string_view> const leaf_data, int64_t const version)
{
    aux.collect_number_nodes_created_stats();
    // handle non child and single child cases
    auto const number_of_children = static_cast<unsigned>(std::popcount(mask));
    if (number_of_children == 0) {
        return leaf_data.has_value()
                   ? make_node(0, {}, path, leaf_data.value(), {}, version)
                         .release()
                   : nullptr;
    }
    else if (number_of_children == 1 && !leaf_data.has_value()) {
        auto const j = bitmask_index(
            orig_mask, static_cast<unsigned>(std::countr_zero(mask)));
        MONAD_DEBUG_ASSERT(children[j].ptr);
        auto const node = Node::UniquePtr{children[j].ptr};
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
                   version)
            .release();
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
                std::tie(child.min_offset_fast, child.min_offset_slow) =
                    calc_min_offsets(
                        *child.ptr, aux.physical_to_virtual(child.offset));
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
                {
                    Node::UniquePtr const _{child.ptr};
                }
                child.ptr = nullptr;
            }
        }
    }
    return create_node_with_children(
        sm.get_compute(), mask, children, path, leaf_data, version);
}

void create_node_compute_data_possibly_async(
    UpdateAuxImpl &aux, StateMachine &sm, UpwardTreeNode &parent,
    ChildData &entry, tnode_unique_ptr tnode, bool const might_on_disk)
{
    if (might_on_disk && tnode->number_of_children() == 1) {
        auto &child = tnode->children[bitmask_index(
            tnode->orig_mask,
            static_cast<unsigned>(std::countr_zero(tnode->mask)))];
        if (!child.ptr) {
            MONAD_DEBUG_ASSERT(aux.is_on_disk());
            MONAD_ASSERT(child.offset != INVALID_OFFSET);
            read_single_child_receiver receiver(
                &aux, sm.clone(), tnode.release(), child);
            async_read(aux, std::move(receiver));
            MONAD_DEBUG_ASSERT(parent.npending);
            return;
        }
    }
    Node *node = create_node_from_children_if_any(
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
        entry.finalize(*node, sm.get_compute(), sm.cache());
        parent.version = std::max(parent.version, node->version);
    }
    else {
        parent.mask &=
            static_cast<uint16_t>(~(static_cast<uint16_t>(1u << entry.branch)));
        entry.erase();
    }
    --parent.npending;
}

void update_value_and_subtrie_(
    UpdateAuxImpl &aux, StateMachine &sm, UpwardTreeNode &parent,
    ChildData &entry, Node::UniquePtr old, NibblesView const path,
    Update &update)
{
    if (update.is_deletion()) {
        parent.mask &= static_cast<uint16_t>(~(1u << entry.branch));
        entry.erase();
        MONAD_DEBUG_ASSERT(entry.ptr == nullptr);
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
        if (!update.next.empty()) { // nested updates
            MONAD_DEBUG_ASSERT(update.value.has_value());
            Requests requests;
            requests.split_into_sublists(std::move(update.next), 0);
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
        }
        else {
            aux.collect_number_nodes_created_stats();
            entry.finalize(
                *make_node(
                     0, {}, path, update.value.value(), {}, update.version)
                     .release(),
                sm.get_compute(),
                sm.cache());
            parent_version = std::max(parent_version, entry.ptr->version);
        }

        if (path.nibble_size()) {
            sm.up(path.nibble_size());
        }
        return;
    }
    Requests requests;
    auto const prefix_index_start = prefix_index;
    while (requests.split_into_sublists(
               std::move(updates), prefix_index) == // NOLINT
               1 &&
           !requests.opt_leaf) {
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
    auto const number_of_children =
        static_cast<unsigned>(std::popcount(requests.mask));
    uint16_t const mask = requests.mask;
    allocators::owning_span<ChildData> const children(number_of_children);
    for (unsigned i = 0, j = 0, bit = 1; j < number_of_children;
         ++i, bit <<= 1) {
        if (bit & requests.mask) {
            children[j] = ChildData{.branch = static_cast<uint8_t>(i)};
            sm.down(children[j].branch);
            create_new_trie_(
                aux,
                sm,
                version,
                children[j],
                std::move(requests)[i],
                prefix_index + 1);
            sm.up(1);
            ++j;
        }
    }
    // can have empty children
    auto *node = create_node_from_children_if_any(
        aux, sm, mask, mask, children, path, opt_leaf_data, version);
    MONAD_ASSERT(node);
    parent_version = std::max(parent_version, node->version);
    entry.finalize(*node, sm.get_compute(), sm.cache());
}

/////////////////////////////////////////////////////
// Update existing subtrie
/////////////////////////////////////////////////////

void upsert_(
    UpdateAuxImpl &aux, StateMachine &sm, UpwardTreeNode &parent,
    ChildData &entry, Node::UniquePtr old, chunk_offset_t const old_offset,
    UpdateList &&updates, unsigned prefix_index, unsigned old_prefix_index)
{
    if (!old) {
        update_receiver receiver(
            &aux,
            sm.clone(),
            entry,
            old_offset,
            std::move(updates),
            &parent,
            prefix_index);
        async_read(aux, std::move(receiver));
        return;
    }
    if (old_prefix_index == INVALID_PATH_INDEX) {
        old_prefix_index = old->path_start_nibble();
        MONAD_DEBUG_ASSERT(old_prefix_index != INVALID_PATH_INDEX);
    }
    unsigned const old_prefix_index_start = old_prefix_index;
    auto const prefix_index_start = prefix_index;
    Requests requests;
    while (true) {
        NibblesView path{
            old_prefix_index_start, old_prefix_index, old->path_data()};
        auto const update_size = updates.size();
        if (update_size == 1 &&
            prefix_index == updates.front().key.nibble_size()) {
            auto &update = updates.front();
            MONAD_ASSERT(old->path_nibble_index_end == old_prefix_index);
            MONAD_ASSERT(old->has_value());
            update_value_and_subtrie_(
                aux, sm, parent, entry, std::move(old), path, update);
            break;
        }
        unsigned const number_of_sublists = requests.split_into_sublists(
            std::move(updates), prefix_index); // NOLINT
        if (!update_size) { // no updates at all
            for (unsigned n = 0;
                 n < old->path_nibble_index_end - old_prefix_index;
                 ++n) { // continue going down to the end of old path
                sm.down(old->path_nibble_view().get(n));
            }
            MONAD_ASSERT(number_of_sublists == 0);
            MONAD_ASSERT(requests.opt_leaf == std::nullopt);
            prefix_index += old->path_nibble_index_end - old_prefix_index;
            old_prefix_index = old->path_nibble_index_end;
            path = NibblesView{
                old_prefix_index_start, old_prefix_index, old->path_data()};
            // will just call dispatch and break;
        }
        if (old_prefix_index == old->path_nibble_index_end) {
            dispatch_updates_flat_list_(
                aux,
                sm,
                parent,
                entry,
                std::move(old),
                requests,
                path,
                prefix_index);
            break;
        }
        if (auto old_nibble = get_nibble(old->path_data(), old_prefix_index);
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
    UpwardTreeNode &parent, ChildData &entry)
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
    UpdateAuxImpl &aux, StateMachine &sm, UpwardTreeNode &parent,
    ChildData &entry, Node::UniquePtr old_ptr, Requests &requests,
    unsigned const prefix_index, NibblesView const path,
    std::optional<byte_string_view> const opt_leaf_data, int64_t const version)
{
    Node *old = old_ptr.get();
    uint16_t const orig_mask = old->mask | requests.mask;
    auto const number_of_children =
        static_cast<unsigned>(std::popcount(orig_mask));
    // tnode->version will be updated bottom up
    auto tnode = make_tnode(
        orig_mask,
        prefix_index,
        &parent,
        entry.branch,
        path,
        version,
        opt_leaf_data,
        opt_leaf_data.has_value() ? std::move(old_ptr) : Node::UniquePtr{});
    MONAD_DEBUG_ASSERT(tnode->children.size() == number_of_children);
    auto &children = tnode->children;

    for (unsigned i = 0, j = 0, bit = 1; j < number_of_children;
         ++i, bit <<= 1) {
        MONAD_DEBUG_ASSERT(i <= std::numeric_limits<uint8_t>::max());
        if (bit & requests.mask) {
            children[j] = ChildData{.branch = static_cast<uint8_t>(i)};
            sm.down(children[j].branch);
            if (bit & old->mask) {
                upsert_(
                    aux,
                    sm,
                    *tnode,
                    children[j],
                    old->next_ptr(old->to_child_index(i)),
                    old->fnext(old->to_child_index(i)),
                    std::move(requests)[i],
                    prefix_index + 1,
                    INVALID_PATH_INDEX);
                sm.up(1);
            }
            else {
                create_new_trie_(
                    aux,
                    sm,
                    tnode->version,
                    children[j],
                    std::move(requests)[i],
                    prefix_index + 1);
                --tnode->npending;
                sm.up(1);
            }
            ++j;
        }
        else if (bit & old->mask) {
            auto &child = children[j];
            child.copy_old_child(old, i);
            auto const old_index = old->to_child_index(i);
            auto const orig_child_offset = old->fnext(old_index);
            if (aux.is_on_disk() && sm.compact() &&
                (old->min_offset_fast(old_index) < aux.compact_offset_fast ||
                 old->min_offset_slow(old_index) < aux.compact_offset_slow)) {
                child.offset = INVALID_OFFSET; // to be rewritten
                bool const copy_node_for_fast =
                    old->min_offset_fast(old_index) < aux.compact_offset_fast;
                compact_(
                    aux,
                    sm,
                    reinterpret_cast<CompactTNode *>(tnode.get()),
                    j,
                    child.ptr,
                    true,
                    orig_child_offset,
                    copy_node_for_fast);
            }
            else {
                --tnode->npending;
            }
            ++j;
        }
    }
    fillin_entry(aux, sm, std::move(tnode), parent, entry);
}

void dispatch_updates_flat_list_(
    UpdateAuxImpl &aux, StateMachine &sm, UpwardTreeNode &parent,
    ChildData &entry, Node::UniquePtr old, Requests &requests,
    NibblesView const path, unsigned prefix_index)
{
    auto &opt_leaf = requests.opt_leaf;
    auto opt_leaf_data = old->opt_value();
    if (opt_leaf.has_value()) {
        MONAD_ASSERT(opt_leaf->next.empty());
        if (opt_leaf.value().incarnation) {
            // incarnation means there are new children keys longer than
            // curr update's key
            MONAD_DEBUG_ASSERT(!opt_leaf.value().is_deletion());
            create_new_trie_from_requests_(
                aux,
                sm,
                parent.version,
                entry,
                requests,
                path,
                prefix_index,
                opt_leaf.value().value,
                opt_leaf.value().version);
            --parent.npending;
            return;
        }
        else if (opt_leaf.value().is_deletion()) {
            parent.mask &= static_cast<uint16_t>(~(1u << entry.branch));
            entry.erase();
            --parent.npending;
            return;
        }
        if (opt_leaf.value().value.has_value()) {
            opt_leaf_data = opt_leaf.value().value;
        }
    }
    int64_t const version =
        opt_leaf.has_value() ? opt_leaf.value().version : old->version;
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
}

// Split `old` at old_prefix_index, `updates` are already splitted at
// prefix_index to `requests`, which can have 1 or more sublists.
void mismatch_handler_(
    UpdateAuxImpl &aux, StateMachine &sm, UpwardTreeNode &parent,
    ChildData &entry, Node::UniquePtr old_ptr, Requests &requests,
    NibblesView const path, unsigned const old_prefix_index,
    unsigned const prefix_index)
{
    Node &old = *old_ptr;
    MONAD_DEBUG_ASSERT(old.has_path());
    // Note: no leaf can be created at an existing non-leaf node
    MONAD_DEBUG_ASSERT(!requests.opt_leaf.has_value());
    unsigned char const old_nibble =
        get_nibble(old.path_data(), old_prefix_index);
    uint16_t const orig_mask =
        static_cast<uint16_t>(1u << old_nibble | requests.mask);
    auto tnode =
        make_tnode(orig_mask, prefix_index, &parent, entry.branch, path);
    auto const number_of_children =
        static_cast<unsigned>(std::popcount(orig_mask));
    MONAD_DEBUG_ASSERT(
        tnode->children.size() == number_of_children && number_of_children > 0);
    auto &children = tnode->children;

    for (unsigned i = 0, j = 0, bit = 1; j < number_of_children;
         ++i, bit <<= 1) {
        if (bit & requests.mask) {
            children[j] = ChildData{.branch = static_cast<uint8_t>(i)};
            sm.down(children[j].branch);
            if (i == old_nibble) {
                upsert_(
                    aux,
                    sm,
                    *tnode,
                    children[j],
                    std::move(old_ptr),
                    INVALID_OFFSET,
                    std::move(requests)[i],
                    prefix_index + 1,
                    old_prefix_index + 1);
            }
            else {
                create_new_trie_(
                    aux,
                    sm,
                    tnode->version,
                    children[j],
                    std::move(requests)[i],
                    prefix_index + 1);
                --tnode->npending;
            }
            ++j;
            sm.up(1);
        }
        else if (i == old_nibble) {
            sm.down(old_nibble);
            // nexts[j] is a path-shortened old node, trim prefix
            NibblesView const path_suffix{
                old_prefix_index + 1,
                old.path_nibble_index_end,
                old.path_data()};
            for (auto i = 0u; i < path_suffix.nibble_size(); ++i) {
                sm.down(path_suffix.get(i));
            }
            auto &child = children[j];
            child = ChildData{.branch = static_cast<uint8_t>(i)};
            // Updated node inherits the version number directly from old node
            child.finalize(
                *make_node(old, path_suffix, old.opt_value(), old.version)
                     .release(),
                sm.get_compute(),
                sm.cache());
            sm.up(path_suffix.nibble_size() + 1);
            if (auto const [min_offset_fast, min_offset_slow] =
                    calc_min_offsets(*child.ptr);
                aux.is_on_disk() && sm.compact() &&
                (min_offset_fast < aux.compact_offset_fast ||
                 min_offset_slow < aux.compact_offset_slow)) {
                bool const copy_node_for_fast =
                    min_offset_fast < aux.compact_offset_fast;
                compact_(
                    aux,
                    sm,
                    (CompactTNode *)tnode.get(),
                    j,
                    child.ptr,
                    true,
                    INVALID_OFFSET,
                    copy_node_for_fast);
            }
            else {
                --tnode->npending;
            }
            ++j;
        }
    }
    fillin_entry(aux, sm, std::move(tnode), parent, entry);
}

void compact_(
    UpdateAuxImpl &aux, StateMachine &sm, CompactTNode *const parent,
    unsigned const index, Node *const node, bool const cached,
    chunk_offset_t const node_offset, bool const copy_node_for_fast_or_slow)
{
    if (!node) {
        compaction_receiver receiver(
            &aux,
            sm.clone(),
            parent,
            index,
            node_offset,
            copy_node_for_fast_or_slow);
        async_read(aux, std::move(receiver));
        return;
    }
    // Only compact nodes < compaction range (either fast or slow) to slow,
    // otherwise rewrite to fast list
    // INVALID_OFFSET indicates node is being updated and not yet written, that
    // case we write to fast
    auto const virtual_node_offset = node_offset == INVALID_OFFSET
                                         ? INVALID_VIRTUAL_OFFSET
                                         : aux.physical_to_virtual(node_offset);
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
    auto tnode =
        CompactTNode::make(parent, index, node, rewrite_to_fast, cached);

    aux.collect_compacted_nodes_stats(
        copy_node_for_fast_or_slow,
        rewrite_to_fast,
        virtual_node_offset,
        node->get_disk_size());

    for (unsigned j = 0; j < node->number_of_children(); ++j) {
        if (node->min_offset_fast(j) < aux.compact_offset_fast ||
            node->min_offset_slow(j) < aux.compact_offset_slow) {
            compact_(
                aux,
                sm,
                tnode.get(),
                j,
                node->next(j),
                true,
                node->fnext(j),
                node->min_offset_fast(j) < aux.compact_offset_fast);
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
    compact_virtual_chunk_offset_t const truncated_new_virtual_offset{
        aux.physical_to_virtual(new_offset)};
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
    if (parent->type == tnode_type::copy) {
        parent->node->set_fnext(index, new_offset);
        parent->node->set_min_offset_fast(index, min_offset_fast);
        parent->node->set_min_offset_slow(index, min_offset_slow);
        if (tnode->cached) { // debug
            MONAD_DEBUG_ASSERT(parent->node->next(index) == tnode->node);
        }
    }
    else { // parent tnode is an update tnode
        auto *const p = reinterpret_cast<UpwardTreeNode *>(parent);
        MONAD_DEBUG_ASSERT(tnode->cached);
        MONAD_DEBUG_ASSERT(p->children[index].offset == INVALID_OFFSET);
        auto &child = p->children[index];
        child.ptr =
            tnode->node; // let parent tnode manage tnode->node's lifetime
        child.offset = new_offset;
        child.min_offset_fast = min_offset_fast;
        child.min_offset_slow = min_offset_slow;
    }
    --parent->npending;
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
    auto const *ci_ = aux.db_metadata()->free_list_end();
    MONAD_ASSERT(ci_ != nullptr); // we are out of free blocks!
    auto idx = ci_->index(aux.db_metadata());
    chunk_offset_t const offset_of_new_writer{idx, 0};
    // Pad buffer of existing node write that is about to get initiated so it's
    // O_DIRECT i/o aligned
    auto const remaining_buffer_bytes = sender->remaining_buffer_bytes();
    auto *tozero = sender->advance_buffer_append(remaining_buffer_bytes);
    MONAD_DEBUG_ASSERT(tozero != nullptr);
    memset(tozero, 0, remaining_buffer_bytes);
    /* If there aren't enough write buffers, this may poll uring until a free
    write buffer appears. However, that polling may write a node, causing
    this function to be reentered, and another free chunk allocated and now
    writes are being directed there instead. Obviously then replacing that new
    partially filled chunk with this new chunk is something which trips the
    assets.

    Replacing the runloop exposed this bug much more clearly than before, but we
    had been seeing occasional issues somewhere around here for some time now,
    it just wasn't obvious the cause. Anyway detect when reentrancy occurs, and
    if so undo this operation and tell the caller to retry.
    */
    auto ret = aux.io->make_connected(
        write_single_buffer_sender{
            offset_of_new_writer, AsyncIO::WRITE_BUFFER_SIZE},
        write_operation_io_receiver{});
    if (ci_ != aux.db_metadata()->free_list_end()) {
        // We reentered, please retry
        return {};
    }
    aux.remove(idx);
    aux.append(
        in_fast_list ? UpdateAuxImpl::chunk_list::fast
                     : UpdateAuxImpl::chunk_list::slow,
        idx);
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
    detail::db_metadata::chunk_info_t const *ci_ = nullptr;
    uint32_t idx;
    if (offset == chunk_capacity) {
        // If after the current write buffer we're hitting chunk capacity, we
        // replace writer to the start of next chunk.
        ci_ = aux.db_metadata()->free_list_end();
        MONAD_ASSERT(ci_ != nullptr); // we are out of free blocks!
        idx = ci_->index(aux.db_metadata());
        offset_of_next_writer.id = idx & 0xfffffU;
        offset_of_next_writer.offset = 0;
    }
    // See above about handling potential reentrancy correctly
    auto *const node_writer_ptr = node_writer.get();
    auto ret = aux.io->make_connected(
        write_single_buffer_sender{
            offset_of_next_writer,
            std::min(
                AsyncIO::WRITE_BUFFER_SIZE,
                (size_t)(chunk_capacity - offset_of_next_writer.offset))},
        write_operation_io_receiver{});
    if (node_writer.get() != node_writer_ptr) {
        // We reentered, please retry
        return {};
    }
    if (ci_ != nullptr) {
        MONAD_DEBUG_ASSERT(ci_ == aux.db_metadata()->free_list_end());
        aux.remove(idx);
        aux.append(
            in_fast_list ? UpdateAuxImpl::chunk_list::fast
                         : UpdateAuxImpl::chunk_list::slow,
            idx);
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
        MONAD_DEBUG_ASSERT(where_to_serialize != nullptr);
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
            auto bytes_to_append = std::min(
                (unsigned)remaining_bytes, size - offset_in_on_disk_node);
            auto *where_to_serialize =
                (unsigned char *)node_writer->sender().advance_buffer_append(
                    bytes_to_append);
            MONAD_DEBUG_ASSERT(where_to_serialize != nullptr);
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
            MONAD_DEBUG_ASSERT(
                new_node_writer->sender().offset().id ==
                node_writer->sender().offset().id);
        }
        // initiate current node writer
        if (node_writer->sender().written_buffer_bytes() !=
            node_writer->sender().buffer().size()) {
            std::cout << "async_write_node "
                      << node_writer->sender().written_buffer_bytes()
                      << " != " << node_writer->sender().buffer().size()
                      << std::endl;
        }
        MONAD_ASSERT(
            node_writer->sender().written_buffer_bytes() ==
            node_writer->sender().buffer().size());
        node_writer->initiate();
        // shall be recycled by the i/o receiver
        node_writer.release();
        node_writer = std::move(new_node_writer);
        // serialize the rest of the node to buffer
        while (offset_in_on_disk_node < size) {
            auto *where_to_serialize =
                (unsigned char *)node_writer->sender().buffer().data();
            auto bytes_to_append = std::min(
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
            if (node_writer->sender().remaining_buffer_bytes() == 0) {
                MONAD_ASSERT(offset_in_on_disk_node < size);
                // replace node writer
                new_node_writer = replace_node_writer(aux, node_writer);
                if (new_node_writer) {
                    // initiate current node writer
                    MONAD_DEBUG_ASSERT(
                        node_writer->sender().written_buffer_bytes() ==
                        node_writer->sender().buffer().size());
                    node_writer->initiate();
                    // shall be recycled by the i/o receiver
                    node_writer.release();
                    node_writer = std::move(new_node_writer);
                }
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

// return root physical offset
chunk_offset_t
write_new_root_node(UpdateAuxImpl &aux, Node &root, uint64_t const version)
{
    auto const offset_written_to = async_write_node_set_spare(aux, root, true);
    // Round up with all bits zero
    auto replace = [&](node_writer_unique_ptr_type &node_writer) {
        auto *sender = &node_writer->sender();
        auto written = sender->written_buffer_bytes();
        auto paddedup = round_up_align<DISK_PAGE_BITS>(written);
        auto const tozerobytes = paddedup - written;
        auto *tozero = sender->advance_buffer_append(tozerobytes);
        MONAD_DEBUG_ASSERT(tozero != nullptr);
        memset(tozero, 0, tozerobytes);
        // replace fast node writer
        auto new_node_writer = replace_node_writer(aux, node_writer);
        while (!new_node_writer) {
            new_node_writer = replace_node_writer(aux, node_writer);
        }
        auto to_initiate = std::move(node_writer);
        node_writer = std::move(new_node_writer);
        to_initiate->initiate();
        // shall be recycled by the i/o receiver
        to_initiate.release();
    };
    replace(aux.node_writer_fast);
    if (aux.node_writer_slow->sender().written_buffer_bytes()) {
        // replace slow node writer
        replace(aux.node_writer_slow);
    }
    // flush async write root and slow writer
    aux.io->flush();
    // update root offset
    auto const last_version_in_db = aux.db_history_max_version();
    MONAD_ASSERT(
        last_version_in_db == INVALID_BLOCK_ID ||
        version == last_version_in_db || version == last_version_in_db + 1);
    if (last_version_in_db == version) {
        aux.update_root_offset(version, offset_written_to);
    }
    else {
        if (MONAD_UNLIKELY(version != last_version_in_db + 1)) {
            MONAD_ASSERT(last_version_in_db == INVALID_BLOCK_ID);
            aux.fast_forward_next_version(version);
        }
        aux.append_root_offset(offset_written_to);
    }
    // advance fast and slow ring's latest offset in db metadata
    aux.advance_db_offsets_to(
        aux.node_writer_fast->sender().offset(),
        aux.node_writer_slow->sender().offset());
    return offset_written_to;
}

MONAD_MPT_NAMESPACE_END

// Copyright (C) 2025-26 Category Labs, Inc.
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

#pragma once

// Async on-disk preorder traversal that visits nodes in key order. Reads are
// still issued concurrently and complete in any order; a node whose read lands
// early is held until every node before it in key order has been visited.
// Pending reads are issued lowest key first, and reads of adjacent or
// overlapping disk ranges are merged into a single i/o.

#include <category/async/erased_connected_operation.hpp>
#include <category/async/io.hpp>
#include <category/core/assert.h>
#include <category/core/nibble.h>
#include <category/mpt/config.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/util.hpp>

#include <algorithm>
#include <cstdint>
#include <cstring>
#include <memory>

#include <boost/container/small_vector.hpp>
#include <boost/intrusive/list.hpp>
#include <boost/intrusive/set.hpp>

MONAD_MPT_NAMESPACE_BEGIN

struct OrderedTraverseMachine;

namespace ordered_detail
{
    // Nibbles are packed two to a byte, high nibble first. Unused trailing
    // nibbles are kept zero so that a bytewise compare orders paths as keys.
    struct TraversePath
    {
        static constexpr uint32_t bytes_for(uint32_t const nibbles)
        {
            return (nibbles + 1) / 2;
        }

        TraversePath()
            : size(0)
            , capacity(32)
            , data(static_cast<unsigned char *>(operator new(capacity)))
        {
        }

        TraversePath(TraversePath const &other, unsigned char const branch)
            : size(other.size)
        {
            if (branch != INVALID_BRANCH) {
                capacity = bytes_for(size + 1) + 32;
                data = static_cast<unsigned char *>(operator new(capacity));
                std::memcpy(data, other.data, bytes_for(size));
                if (size % 2 == 0) {
                    data[size / 2] = static_cast<unsigned char>(branch << 4);
                }
                else {
                    data[size / 2] |= branch;
                }
                ++size;
            }
            else {
                capacity = other.capacity;
                data = static_cast<unsigned char *>(operator new(capacity));
                std::memcpy(data, other.data, bytes_for(size));
            }
        }

        TraversePath(TraversePath &&other) = delete;
        TraversePath &operator=(TraversePath &&other) = delete;
        TraversePath &operator=(TraversePath const &other) = delete;

        ~TraversePath()
        {
            operator delete(data);
        }

        bool operator<(TraversePath const &other) const
        {
            auto const min_size = std::min(size, other.size);
            auto const ret = std::memcmp(data, other.data, bytes_for(min_size));
            if (ret != 0) {
                return ret < 0;
            }
            return size < other.size;
        }

        void
        append(unsigned start, unsigned const end, unsigned char const *const d)
        {
            if (start >= end) {
                return;
            }

            auto sz = this->size;
            auto const required_capacity = bytes_for(sz + end - start);
            if (required_capacity > capacity) {
                capacity = required_capacity;
                auto *const new_data =
                    static_cast<unsigned char *>(operator new(capacity));
                std::memcpy(new_data, this->data, bytes_for(sz));
                operator delete(this->data);
                this->data = new_data;
            }
            if (sz % 2 != 0) {
                this->data[sz / 2] |= get_nibble(d, start);
                ++start;
                ++sz;
            }
            if (start % 2 == 0) {
                auto const bytes = (end - start) / 2;
                std::memcpy(this->data + sz / 2, d + start / 2, bytes);
                sz += bytes * 2;
                start += bytes * 2;
            }
            else {
                for (; start + 1 < end; start += 2, sz += 2) {
                    this->data[sz / 2] = static_cast<unsigned char>(
                        ((d[start / 2] & 0xF) << 4) |
                        ((d[start / 2 + 1] & 0xF0) >> 4));
                }
            }
            if (start < end) {
                this->data[sz / 2] =
                    static_cast<unsigned char>(get_nibble(d, start) << 4);
                ++sz;
            }
            this->size = sz;
        }

        uint32_t size;
        uint32_t capacity; // bytes
        unsigned char *data;
    };

    struct TraverseSender;

    void async_parallel_ordered_traverse_init(
        TraverseSender &, async::erased_connected_operation *);

    void async_parallel_ordered_traverse_impl(
        TraverseSender &sender,
        async::erased_connected_operation *traverse_state, Node::SharedPtr node,
        OrderedTraverseMachine &machine);
}

// One machine per node, cloned from its parent's machine before the parent is
// visited, so a machine cannot carry state from one node to the next; state
// that must flow between nodes in key order has to live outside the machines.
struct OrderedTraverseMachine
{
    unsigned char branch{INVALID_BRANCH};
    boost::intrusive::list_member_hook<> hook;

    virtual ~OrderedTraverseMachine() = default;
    OrderedTraverseMachine() = default;

    OrderedTraverseMachine(
        OrderedTraverseMachine const &other, unsigned char const branch)
        : branch(branch)
        , path_(other.path_, branch)
    {
    }

    OrderedTraverseMachine(OrderedTraverseMachine const &) = delete;
    OrderedTraverseMachine(OrderedTraverseMachine &&) = delete;

    virtual void visit(unsigned char parent_branch, Node const &node) = 0;

    virtual std::unique_ptr<OrderedTraverseMachine>
    clone(unsigned char branch) const = 0;

    // Returning false skips this node and its entire subtree.
    virtual bool should_visit_node(Node const &, unsigned char /*branch*/)
    {
        return true;
    }

    virtual bool should_visit_child(Node const &, unsigned char /*branch*/)
    {
        return true;
    }

    // Full key path from the traverse root, up to and including this node.
    NibblesView path() const
    {
        return NibblesView{0, path_.size, path_.data};
    }

    ordered_detail::TraversePath const &path_ref() const
    {
        return path_;
    }

private:
    void update_path(Node const &node)
    {
        if (node.path_nibbles_len() != 0) {
            path_.append(
                node.bitpacked.path_nibble_index_start,
                node.path_nibble_index_end,
                node.path_data());
        }
    }

    friend void ordered_detail::async_parallel_ordered_traverse_impl(
        ordered_detail::TraverseSender &sender,
        async::erased_connected_operation *traverse_state, Node::SharedPtr node,
        OrderedTraverseMachine &machine);

    ordered_detail::TraversePath path_{};
    // Null until the node has loaded.
    Node::SharedPtr node;
};

namespace ordered_detail
{
    using TraverseList = boost::intrusive::list<
        OrderedTraverseMachine,
        boost::intrusive::member_hook<
            OrderedTraverseMachine, boost::intrusive::list_member_hook<>,
            &OrderedTraverseMachine::hook>>;

    struct TraverseSender
    {
        struct NodeBufferSlice
        {
            // Where this machine's node starts in its chunk; a merged read
            // never spans chunks, so this stays valid as the read grows.
            uint32_t chunk_off;
            // Bytes from chunk_off to the end of the node's own read, which
            // bounds it within a merged read.
            uint32_t node_bytes;
            OrderedTraverseMachine *machine; // owned by TraverseSender::list
        };

        struct NodeRead
        {
            NodeRead(
                chunk_offset_t const offset, OrderedTraverseMachine &machine)
                : rd_offset(offset)
                , path(&machine.path_ref())
            {
                auto const num_pages_to_load_node =
                    node_disk_pages_spare_15{offset}.to_pages();
                bytes_to_read = static_cast<unsigned>(
                    num_pages_to_load_node << DISK_PAGE_BITS);
                auto const new_offset =
                    round_down_align<DISK_PAGE_BITS>(offset.offset);
                MONAD_DEBUG_ASSERT(new_offset <= chunk_offset_t::max_offset);
                rd_offset.offset = new_offset & chunk_offset_t::max_offset;
                auto const buffer_off =
                    uint32_t(offset.offset - rd_offset.offset);
                MONAD_ASSERT(buffer_off < bytes_to_read);
                node_slices.emplace_back(NodeBufferSlice{
                    uint32_t(offset.offset),
                    bytes_to_read - buffer_off,
                    &machine});
            }

            NodeRead(NodeRead &&other) = default;
            NodeRead(NodeRead const &other) = delete;
            NodeRead &operator=(NodeRead &&other) = default;
            NodeRead &operator=(NodeRead const &other) = delete;

            static constexpr bool lifetime_managed_internally = true;

            file_offset_t begin() const
            {
                return rd_offset.raw();
            }

            file_offset_t end() const
            {
                return rd_offset.raw() + bytes_to_read;
            }

            chunk_offset_t rd_offset;
            unsigned bytes_to_read;
            // Lowest key among the merged machines; orders pending reads.
            TraversePath const *path;
            boost::container::small_vector<NodeBufferSlice, 4> node_slices;

            struct compare_path
            {
                bool operator()(NodeRead const &a, NodeRead const &b) const
                {
                    return *a.path < *b.path;
                }
            };

            struct compare_offset
            {
                bool operator()(NodeRead const &a, NodeRead const &b) const
                {
                    return a.begin() < b.begin();
                }
            };

            struct compare_end
            {
                bool operator()(file_offset_t const a, NodeRead const &b) const
                {
                    return a < b.end();
                }

                bool operator()(NodeRead const &a, file_offset_t const b) const
                {
                    return a.end() < b;
                }
            };
        };

        struct PendingNodeRead : public NodeRead
        {
            explicit PendingNodeRead(NodeRead &&read)
                : NodeRead(std::move(read))
            {
            }

            boost::intrusive::set_member_hook<> path_hook;
            boost::intrusive::set_member_hook<> offset_hook;
        };

        // The same reads are in both sets, which hold no two mergeable reads.
        using PendingReadsByKey = boost::intrusive::set<
            PendingNodeRead,
            boost::intrusive::member_hook<
                PendingNodeRead, boost::intrusive::set_member_hook<>,
                &PendingNodeRead::path_hook>,
            boost::intrusive::compare<NodeRead::compare_path>>;

        using PendingReadsByOffset = boost::intrusive::set<
            PendingNodeRead,
            boost::intrusive::member_hook<
                PendingNodeRead, boost::intrusive::set_member_hook<>,
                &PendingNodeRead::offset_hook>,
            boost::intrusive::compare<NodeRead::compare_offset>>;

        struct receiver_t : public NodeRead
        {
            static constexpr bool lifetime_managed_internally = true;

            TraverseSender *sender;
            async::erased_connected_operation *traverse_state;

            receiver_t(
                TraverseSender *const sender,
                async::erased_connected_operation *const traverse_state,
                NodeRead &&read)
                : NodeRead(std::move(read))
                , sender(sender)
                , traverse_state(traverse_state)
            {
            }

            receiver_t(receiver_t const &) = delete;
            receiver_t(receiver_t &&) = default;
            receiver_t &operator=(receiver_t const &) = delete;
            receiver_t &operator=(receiver_t &&other) = default;

            template <class ResultType>
            void set_value(
                async::erased_connected_operation *const io_state,
                ResultType buffer_)
            {
                MONAD_ASSERT(buffer_);
                --sender->outstanding_reads;
                if (sender->version_expired_before_complete ||
                    !sender->aux.metadata_ctx().version_is_valid_ondisk(
                        sender->version, sender->tid)) {
                    sender->version_expired_before_complete = true;
                    sender->clear_pending_reads();
                }
                else if constexpr (std::is_same_v<
                                       std::decay_t<ResultType>,
                                       typename async::
                                           read_single_buffer_sender::
                                               result_type>) {
                    auto &buffer = std::move(buffer_).assume_value().get();
                    visit_nodes(
                        reinterpret_cast<unsigned char const *>(buffer.data()),
                        buffer.size());
                    buffer.reset();
                }
                else if constexpr (std::is_same_v<
                                       std::decay_t<ResultType>,
                                       typename async::
                                           read_multiple_buffer_sender::
                                               result_type>) {
                    // read_long_update_sender always allocates one buffer.
                    MONAD_ASSERT(buffer_.assume_value().size() == 1);
                    auto const &buffer = buffer_.assume_value().front();
                    MONAD_ASSERT(io_state->lifetime_is_managed_internally());
                    visit_nodes(
                        reinterpret_cast<unsigned char const *>(buffer.data()),
                        buffer.size());
                }
                else {
                    static_assert(false);
                }
                if (sender->within_recursion_count == 0 &&
                    sender->pending_reads_by_key.empty() &&
                    sender->outstanding_reads == 0) {
                    MONAD_ASSERT(
                        sender->version_expired_before_complete ||
                        sender->list.empty());
                    traverse_state->completed(async::success());
                }
            }

            void visit_nodes(unsigned char const *const data, size_t const size)
            {
                for (auto const &slice : node_slices) {
                    size_t const buffer_off =
                        slice.chunk_off - uint32_t(rd_offset.offset);
                    MONAD_ASSERT(buffer_off < size);
                    async_parallel_ordered_traverse_impl(
                        *sender,
                        traverse_state,
                        deserialize_node_from_buffer(
                            data + buffer_off,
                            std::min<size_t>(
                                slice.node_bytes, size - buffer_off)),
                        *slice.machine);
                }
            }
        };

        using result_type = async::result<bool>;

        UpdateAux &aux;
        Node::SharedPtr traverse_root;
        std::unique_ptr<OrderedTraverseMachine> machine;
        uint64_t const version;
        timeline_id const tid;
        size_t const max_outstanding_reads;
        size_t outstanding_reads{0};
        size_t within_recursion_count{0};
        bool version_expired_before_complete{false};
        // Every live machine, in key order. A machine leaves the list once it
        // has been visited or skipped.
        TraverseList list;
        PendingReadsByKey pending_reads_by_key;
        PendingReadsByOffset pending_reads_by_offset;

        TraverseSender(
            UpdateAux &aux, Node::SharedPtr traverse_root,
            std::unique_ptr<OrderedTraverseMachine> machine,
            uint64_t const version, timeline_id const tid,
            size_t const concurrency_limit)
            : aux(aux)
            , traverse_root(std::move(traverse_root))
            , machine(std::move(machine))
            , version(version)
            , tid(tid)
            , max_outstanding_reads(concurrency_limit)
        {
        }

        TraverseSender(TraverseSender const &) = delete;
        TraverseSender(TraverseSender &&) = default;
        TraverseSender &operator=(TraverseSender const &) = delete;
        TraverseSender &operator=(TraverseSender &&) = delete;

        ~TraverseSender()
        {
            list.clear_and_dispose(delete_machine);
            clear_pending_reads();
        }

        async::result<void>
        operator()(async::erased_connected_operation *const traverse_state)
        {
            MONAD_ASSERT(traverse_root != nullptr);
            async_parallel_ordered_traverse_init(*this, traverse_state);
            return async::success();
        }

        // Whether the traverse ran to completion.
        async::result<bool> completed(
            async::erased_connected_operation *,
            async::result<void> res) noexcept
        {
            BOOST_OUTCOME_TRY(std::move(res));
            MONAD_ASSERT(within_recursion_count == 0);
            return async::success(!version_expired_before_complete);
        }

        TraverseList::iterator insert_machine(
            TraverseList::const_iterator const pos,
            std::unique_ptr<OrderedTraverseMachine> machine)
        {
            return list.insert(pos, *machine.release());
        }

        static void delete_machine(OrderedTraverseMachine *const machine)
        {
            delete machine;
        }

        void clear_pending_reads()
        {
            pending_reads_by_key.clear();
            pending_reads_by_offset.clear_and_dispose(
                [](auto *const r) { delete r; });
        }

        void issue_read(
            async::erased_connected_operation *const traverse_state,
            NodeRead &&read)
        {
            async_read(aux, receiver_t(this, traverse_state, std::move(read)));
            ++outstanding_reads;
        }

        void initiate_pending_reads(
            async::erased_connected_operation *const traverse_state)
        {
            while (outstanding_reads < max_outstanding_reads &&
                   !pending_reads_by_key.empty()) {
                auto const it = pending_reads_by_key.begin();
                std::unique_ptr<PendingNodeRead> const read{&*it};
                pending_reads_by_offset.erase(
                    pending_reads_by_offset.iterator_to(*read));
                pending_reads_by_key.erase(it);
                issue_read(traverse_state, std::move(*read));
            }
        }

        // Reads in different chunks never merge: chunks with consecutive ids
        // need not be adjacent on disk.
        static bool can_merge(NodeRead const &lhs, NodeRead const &rhs)
        {
            return lhs.rd_offset.id == rhs.rd_offset.id &&
                   lhs.end() >= rhs.begin() && rhs.end() >= lhs.begin();
        }

        // Folds `rhs` into `lhs`, leaving `rhs` with no machines.
        static bool try_merge(NodeRead &lhs, NodeRead &rhs)
        {
            if (!can_merge(lhs, rhs)) {
                return false;
            }
            auto const begin = std::min(lhs.begin(), rhs.begin());
            auto const end = std::max(lhs.end(), rhs.end());

            lhs.bytes_to_read = unsigned(end - begin);
            lhs.rd_offset.offset = begin & chunk_offset_t::max_offset;
            lhs.rd_offset.spare = 0;
            lhs.node_slices.insert(
                lhs.node_slices.end(),
                rhs.node_slices.begin(),
                rhs.node_slices.end());
            rhs.node_slices.clear();
            if (*rhs.path < *lhs.path) {
                lhs.path = rhs.path;
            }
            return true;
        }

        void add_pending_read(NodeRead &&read)
        {
            auto *new_read = new PendingNodeRead(std::move(read));
            // Every read that overlaps or abuts new_read lies in
            // [lower_bound, first read beginning after new_read ends).
            auto it = pending_reads_by_offset.lower_bound(
                new_read->begin(), NodeRead::compare_end{});
            while (it != pending_reads_by_offset.end() &&
                   it->begin() <= new_read->end()) {
                if (!can_merge(*it, *new_read)) {
                    ++it;
                    continue;
                }
                auto &existing_read = *it;
                it = pending_reads_by_offset.erase(it);
                pending_reads_by_key.erase(
                    pending_reads_by_key.iterator_to(existing_read));
                MONAD_ASSERT(try_merge(existing_read, *new_read));
                delete new_read;
                new_read = &existing_read;
            }

            MONAD_ASSERT(pending_reads_by_key.insert(*new_read).second);
            MONAD_ASSERT(pending_reads_by_offset.insert(*new_read).second);
        }
    };

    inline void async_parallel_ordered_traverse_init(
        TraverseSender &sender,
        async::erased_connected_operation *const traverse_state)
    {
        // False positive: the analyzer does not model copy elision of the
        // sender into the non-movable operation state that
        // `new auto(async::connect(...))` creates, so it treats aux as never
        // initialized.
        // NOLINTNEXTLINE(clang-analyzer-core.CallAndMessage)
        if (!sender.aux.metadata_ctx().version_is_valid_ondisk(
                sender.version, sender.tid)) {
            sender.version_expired_before_complete = true;
            traverse_state->completed(async::success());
            return;
        }
        auto &root_machine = *sender.insert_machine(
            sender.list.end(), std::move(sender.machine));
        root_machine.branch = INVALID_BRANCH;
        async_parallel_ordered_traverse_impl(
            sender, traverse_state, sender.traverse_root, root_machine);
        MONAD_ASSERT(sender.within_recursion_count == 0);

        if (sender.pending_reads_by_key.empty() &&
            sender.outstanding_reads == 0) {
            traverse_state->completed(async::success());
        }
    }

    // Only the outermost impl call on the stack visits, and it keeps
    // within_recursion_count raised while it does. Otherwise a nested call
    // could free a machine whose children loop or visit() is still running
    // further up the stack, and a completion polled from inside visit() could
    // complete the traverse under it.
    inline void async_parallel_ordered_traverse_impl(
        TraverseSender &sender,
        async::erased_connected_operation *const traverse_state,
        Node::SharedPtr node, OrderedTraverseMachine &machine)
    {
        ++sender.within_recursion_count;
        machine.node = std::move(node);
        sender.initiate_pending_reads(traverse_state);
        if (machine.branch != INVALID_BRANCH) {
            machine.update_path(*machine.node);
        }
        auto const it = sender.list.iterator_to(machine);
        if (machine.should_visit_node(*machine.node, machine.branch)) {
            // All children enter the list before any is descended into, so
            // that a child's subtree lands between it and its next sibling.
            struct Child
            {
                OrderedTraverseMachine *machine;
                uint8_t idx;
            };

            boost::container::small_vector<Child, 16> children;
            auto insert_it = it;
            for (auto const [idx, child_branch] :
                 NodeChildrenRange(machine.node->mask)) {
                if (machine.should_visit_child(*machine.node, child_branch)) {
                    insert_it = sender.insert_machine(
                        std::next(insert_it), machine.clone(child_branch));
                    children.push_back(
                        Child{&*insert_it, static_cast<uint8_t>(idx)});
                }
            }

            boost::container::small_vector<TraverseSender::NodeRead, 16> reads;
            for (auto const &child : children) {
                Node::SharedPtr const &next = machine.node->next(child.idx);
                if (next == nullptr) {
                    MONAD_ASSERT(sender.aux.is_on_disk());
                    reads.emplace_back(
                        machine.node->fnext(child.idx), *child.machine);
                }
                else {
                    async_parallel_ordered_traverse_impl(
                        sender, traverse_state, next, *child.machine);
                }
            }
            std::sort(
                reads.begin(),
                reads.end(),
                TraverseSender::NodeRead::compare_offset{});
            for (size_t i = 0, j = 1; j < reads.size(); ++j) {
                if (!TraverseSender::try_merge(reads[i], reads[j])) {
                    i = j;
                }
            }

            for (auto &read : reads) {
                if (read.node_slices.empty()) {
                    continue;
                }
                if (sender.outstanding_reads >= sender.max_outstanding_reads) {
                    sender.add_pending_read(std::move(read));
                }
                else {
                    sender.issue_read(traverse_state, std::move(read));
                }
            }
        }
        else {
            sender.list.erase_and_dispose(it, TraverseSender::delete_machine);
        }

        if (sender.within_recursion_count == 1) {
            while (!sender.list.empty()) {
                auto &front = sender.list.front();
                if (front.node == nullptr) {
                    break;
                }
                front.visit(front.branch, *front.node);
                sender.list.pop_front_and_dispose(
                    TraverseSender::delete_machine);
            }
        }
        --sender.within_recursion_count;
    }
}

// Returns whether the traversal ran to completion: false if the version was
// pruned part way through. Drives the aux's AsyncIO on the calling thread.
inline bool preorder_traverse_ondisk_ordered(
    UpdateAux &aux, Node::SharedPtr node, OrderedTraverseMachine &machine,
    uint64_t const version, timeline_id const tid = timeline_id::primary,
    size_t const concurrency_limit = 4096)
{
    MONAD_ASSERT(aux.is_on_disk());
    // At zero no read is ever issued, so flush() would return mid-traversal.
    MONAD_ASSERT(concurrency_limit > 0);

    struct TraverseReceiver
    {
        bool &version_expired_before_traverse_complete_;

        explicit TraverseReceiver(
            bool &version_expired_before_traverse_complete)
            : version_expired_before_traverse_complete_(
                  version_expired_before_traverse_complete)
        {
        }

        void set_value(
            async::erased_connected_operation *const traverse_state,
            async::result<bool> const traverse_completed)
        {
            MONAD_ASSERT(traverse_completed);
            version_expired_before_traverse_complete_ =
                !traverse_completed.assume_value();
            delete traverse_state;
        }
    };

    bool version_expired_before_traverse_complete = false;

    auto *const state = new auto(async::connect(
        ordered_detail::TraverseSender(
            aux,
            std::move(node),
            machine.clone(INVALID_BRANCH),
            version,
            tid,
            concurrency_limit),
        TraverseReceiver{version_expired_before_traverse_complete}));
    state->initiate();

    aux.io->flush();

    return !version_expired_before_traverse_complete;
}

MONAD_MPT_NAMESPACE_END

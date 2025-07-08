#pragma once

#include <monad/async/erased_connected_operation.hpp>
#include <monad/async/io.hpp>
#include <monad/core/assert.h>
#include <monad/core/tl_tid.h>
#include <monad/mpt/config.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/util.hpp>

#include <cstdint>
#include <functional>

#include <boost/container/deque.hpp>
#include <boost/container/small_vector.hpp>
#include <boost/intrusive/list.hpp>
#include <boost/intrusive/set.hpp>

#include "deserialize_node_from_receiver_result.hpp"

MONAD_MPT_NAMESPACE_BEGIN

struct TraverseMachine;

namespace detail
{
    struct TraversePath
    {
        TraversePath()
            : size(0)
            , capacity(33)
            , data(static_cast<unsigned char *>(operator new(capacity)))
        {
            data[0] = 0;
        }

        TraversePath(TraversePath const &other, unsigned char branch)
            : size(other.size)
        {
            if (branch != INVALID_BRANCH) {
                capacity = (size + 1 + 1) / 2 + 32;
                data = static_cast<unsigned char *>(operator new(capacity));
                std::memcpy(data, other.data, (other.size + 1 + 1) / 2);
                if ((size + 1) % 2 == 0) {
                    data[(size + 1) / 2] = (branch << 4);
                }
                else {
                    data[(size + 1) / 2] |= branch;
                }
                ++size;
            }
            else {
                size = other.size;
                capacity = other.capacity;
                data = static_cast<unsigned char *>(operator new(capacity));
                std::memcpy(data, other.data, (other.size + 1 + 1) / 2);
            }
        }

        TraversePath(TraversePath &&other) = delete;

        TraversePath &operator=(TraversePath &&other) = delete;

        TraversePath &operator=(TraversePath const &other)
        {
            if (this != &other) {
                operator delete(data);
                size = other.size;
                capacity = other.capacity;
                data = static_cast<unsigned char *>(operator new(capacity));
                std::memcpy(data, other.data, (other.size + 1 + 1) / 2);
            }
            return *this;
        }

        bool operator<(TraversePath const &other) const
        {
            auto min_size = std::min(size, other.size);
            auto ret = std::memcmp(data, other.data, (min_size + 1 + 1) / 2);
            if (ret != 0) {
                return ret < 0;
            }
            return size < other.size;
        }

        void append(unsigned start, unsigned end, unsigned char const *data)
        {
            if (start >= end) {
                return;
            }

            auto size = this->size;
            auto add_size = end - start;
            auto required_capacity = (size + add_size + 1 + 1) / 2;
            if (required_capacity > capacity) {
                capacity = required_capacity;
                auto data =
                    static_cast<unsigned char *>(operator new(capacity));
                std::memcpy(data, this->data, (size + 1 + 1) / 2);
                this->data = data;
            }
            if ((size + 1) % 2 != 0) {
                this->data[(size + 1) / 2] |= get_nibble(data, start);
                ++start;
                ++size;
            }
            if (start % 2 == 0) {
                auto bytes = (end - start) / 2;
                memcpy(this->data + (size + 1) / 2, data + start / 2, bytes);
                size += bytes * 2;
                start += bytes * 2;
            }
            else {
                for (; start + 1 < end; start += 2, size += 2) {
                    this->data[(size + 1) / 2] =
                        ((data[start / 2] & 0xF) << 4) |
                        ((data[start / 2 + 1] & 0xF0) >> 4);
                }
            }
            if (start < end) {
                if ((size + 1) % 2 == 0) {
                    this->data[(size + 1) / 2] = (get_nibble(data, start) << 4);
                }
                else {
                    this->data[(size + 1) / 2] |= get_nibble(data, start);
                }
                ++size;
            }
            this->size = size;
        }

        ~TraversePath()
        {
            operator delete(data);
        }

        uint32_t size;
        uint32_t capacity;
        unsigned char *data;
    };

    struct TraverseSender;

    void async_parallel_preorder_traverse_init(
        TraverseSender &, async::erased_connected_operation *traverse_state,
        Node const &);

    void async_parallel_preorder_traverse_impl(
        TraverseSender &sender,
        async::erased_connected_operation *traverse_state, Node::UniquePtr node,
        TraverseMachine &machine);

    bool preorder_traverse_blocking_impl(
        UpdateAuxImpl &aux, Node const &node, TraverseMachine &traverse,
        uint64_t const version);
}

struct TraverseMachine
{
    unsigned char branch{INVALID_BRANCH};
    boost::intrusive::list_member_hook<> hook;

    virtual ~TraverseMachine() = default;
    TraverseMachine() = default;

    TraverseMachine(TraverseMachine const &other, unsigned char branch)
        : branch(branch)
        , path_(other.path_, branch)
    {
    }

    TraverseMachine(TraverseMachine const &other) = delete;
    TraverseMachine(TraverseMachine &&other) = delete;

    virtual void visit(unsigned char parent_branch, Node const &node) = 0;

    virtual std::unique_ptr<TraverseMachine>
    clone(unsigned char branch) const = 0;

    virtual bool should_visit_node(
        Node const & /* node */, unsigned char /* parent branch */)
    {
        return true;
    }

    virtual bool should_visit_child(
        Node const & /* parent node */, unsigned char /* child branch */)
    {
        return true;
    }

    NibblesView path() const
    {
        return NibblesView{1, path_.size + 1, path_.data};
    }

    detail::TraversePath const &path_ref() const
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

    friend void detail::async_parallel_preorder_traverse_impl(
        detail::TraverseSender &sender,
        async::erased_connected_operation *traverse_state, Node::UniquePtr node,
        TraverseMachine &machine);
    friend bool detail::preorder_traverse_blocking_impl(
        UpdateAuxImpl &aux, Node const &node, TraverseMachine &traverse,
        uint64_t const version);

    detail::TraversePath path_{};
    Node::UniquePtr node;
};

// TODO: move definitions out of header file
namespace detail
{
    struct TraverseSender;

    void async_parallel_preorder_traverse_init(
        TraverseSender &, async::erased_connected_operation *traverse_state,
        Node const &);

    // current implementation does not contaminate triedb node caching
    inline bool preorder_traverse_blocking_impl(
        UpdateAuxImpl &aux, Node const &node, TraverseMachine &traverse,
        uint64_t const version)
    {
        if (traverse.branch != INVALID_BRANCH) {
            traverse.update_path(node);
        }

        if (!traverse.should_visit_node(node, traverse.branch)) {
            return true;
        }
        traverse.visit(traverse.branch, node);

        for (auto const &[idx, branch] : NodeChildrenRange(node.mask)) {
            if (traverse.should_visit_child(node, branch)) {
                auto const *const next = node.next(idx);
                if (next) {
                    auto child_traverse = traverse.clone(branch);
                    if (!preorder_traverse_blocking_impl(
                            aux, *next, *child_traverse, version)) {
                        return false;
                    }
                    continue;
                }
                MONAD_ASSERT(aux.is_on_disk());
                Node::UniquePtr next_node_ondisk =
                    read_node_blocking(aux, node.fnext(idx), version);
                auto child_traverse = traverse.clone(branch);
                if (!next_node_ondisk ||
                    !preorder_traverse_blocking_impl(
                        aux, *next_node_ondisk, *child_traverse, version)) {
                    return false;
                }
            }
        }
        return true;
    }

    using TraverseList = boost::intrusive::list<
        TraverseMachine,
        boost::intrusive::member_hook<
            TraverseMachine, boost::intrusive::list_member_hook<>,
            &TraverseMachine::hook>>;

    /* We need to be able to stop the parallel traversal in the middle of the
    run, perhaps because of version got invalidated. To handle that particular
    case, current solution is to wait for all outstanding i/o to complete. We
    have a limit on concurrent read i/o, so the wait would take up to a few
    hundred microseconds, which is affordable in my opinion. Another way is to
    have i/o cancellation through `io_uring_prep_cancel`, however `AsyncIO` is
    not designed to handle cancellation, and it is nontrivial amount of work to
    add that correctly for little gain on disk i/o. Cancellation often takes as
    long as waiting for the i/o to complete in any case. If the i/o has been
    sent to the device, it can't be cancelled after that point, all can be done
    is wait until the device delivers. The new i/o executor is designed with
    cancellation, and we can test that feature when plugged in if really need.
  */

    struct TraverseSender
    {
        struct MachineOffset
        {
            /// Offset in the read buffer where the node data starts
            uint32_t buffer_off;

            /// Associated traverse machine owned by the sender list
            TraverseMachine *machine;
        };

        struct NodeRead
        {
            NodeRead(chunk_offset_t const offset, TraverseMachine &machine)
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
                this->rd_offset.offset =
                    new_offset & chunk_offset_t::max_offset;
                auto buffer_off =
                    uint32_t(offset.offset - this->rd_offset.offset);
                machine_offsets.emplace_back(
                    MachineOffset{buffer_off, &machine});
            }

            NodeRead(NodeRead &&other) = default;
            NodeRead(NodeRead const &other) = delete;
            NodeRead &operator=(NodeRead &&other) = default;
            NodeRead &operator=(NodeRead const &other) = delete;

            chunk_offset_t rd_offset;
            unsigned bytes_to_read;
            TraversePath const *path;
            boost::container::small_vector<MachineOffset, 4> machine_offsets;

            struct compare
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
                    return a.rd_offset < b.rd_offset;
                }
            };

            struct compare_offset_key
            {
                bool operator()(file_offset_t const &a, NodeRead const &b) const
                {
                    return a < b.rd_offset.raw() + b.bytes_to_read;
                }

                bool operator()(NodeRead const &a, file_offset_t const &b) const
                {
                    return a.rd_offset.raw() + a.bytes_to_read < b;
                }
            };
        };

        struct NodeReadInSet : public NodeRead
        {
            NodeReadInSet(NodeRead &&read)
                : NodeRead(std::move(read))
            {
            }

            boost::intrusive::set_member_hook<> path_hook;
            boost::intrusive::set_member_hook<> offset_hook;
        };

        using PendingReads = boost::intrusive::set<
            NodeReadInSet,
            boost::intrusive::member_hook<
                NodeReadInSet, boost::intrusive::set_member_hook<>,
                &NodeReadInSet::path_hook>,
            boost::intrusive::compare<NodeReadInSet::compare>>;

        using OffsetReads = boost::intrusive::set<
            NodeReadInSet,
            boost::intrusive::member_hook<
                NodeReadInSet, boost::intrusive::set_member_hook<>,
                &NodeReadInSet::offset_hook>,
            boost::intrusive::compare<NodeReadInSet::compare>>;

        struct receiver_t : public NodeRead
        {
            static constexpr bool lifetime_managed_internally = true;

            TraverseSender *sender;
            async::erased_connected_operation *traverse_state;

            receiver_t(
                TraverseSender *sender,
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
                monad::async::erased_connected_operation *io_state,
                ResultType buffer_)
            {
                MONAD_ASSERT(buffer_);
                --sender->outstanding_reads;
                if (sender->version_expired_before_complete ||
                    !sender->aux.version_is_valid_ondisk(sender->version)) {
                    // async read failure or stopping initiated
                    sender->version_expired_before_complete = true;
                    sender->pending_reads.clear_and_dispose(
                        [](auto *r) { delete r; });
                }
                else { // version is valid after reading the buffer
                    if constexpr (std::is_same_v<
                                      std::decay_t<ResultType>,
                                      typename monad::async::
                                          read_single_buffer_sender::
                                              result_type>) {
                        auto &buffer = std::move(buffer_).assume_value().get();
                        for (auto &mo : machine_offsets) {
                            MONAD_ASSERT(mo.buffer_off < buffer.size());
                            MONAD_ASSERT(buffer.size() > 0);
                            auto node = deserialize_node_from_buffer(
                                (unsigned char *)buffer.data() + mo.buffer_off,
                                buffer.size() - mo.buffer_off);
                            async_parallel_preorder_traverse_impl(
                                *sender,
                                traverse_state,
                                std::move(node),
                                *mo.machine);
                        }

                        buffer.reset();
                    }
                    else if constexpr (std::is_same_v<
                                           std::decay_t<ResultType>,
                                           typename monad::async::
                                               read_multiple_buffer_sender::
                                                   result_type>) {
                        auto &buffer = buffer_.assume_value().front();
                        MONAD_ASSERT(buffer.size() > 0);
                        // Did the Receiver forget to set
                        // lifetime_managed_internally?
                        MONAD_DEBUG_ASSERT(
                            io_state->lifetime_is_managed_internally());
                        for (auto &mo : machine_offsets) {
                            MONAD_ASSERT(mo.buffer_off < buffer.size());
                            MONAD_ASSERT(buffer.size() > 0);
                            auto node = deserialize_node_from_buffer(
                                (unsigned char *)buffer.data() + mo.buffer_off,
                                buffer.size() - mo.buffer_off);
                            async_parallel_preorder_traverse_impl(
                                *sender,
                                traverse_state,
                                std::move(node),
                                *mo.machine);
                        }
                    }
                    else {
                        static_assert(false);
                    }
                }
                // complete async traverse if no outstanding io AND there is no
                // recursive traverse call
                // `async_parallel_preorder_traverse_impl()` in current stack,
                // which means traverse is still in progress
                if (sender->within_recursion_count == 0 &&
                    sender->pending_reads.empty() &&
                    sender->outstanding_reads == 0) {
                    MONAD_ASSERT(
                        sender->version_expired_before_complete ||
                        sender->list.empty());
                    traverse_state->completed(async::success());
                }
            }
        };

        static_assert(sizeof(receiver_t) == 128);
        static_assert(alignof(receiver_t) == 8);

        using result_type = async::result<bool>;

        UpdateAuxImpl &aux;
        Node::UniquePtr traverse_root;
        std::unique_ptr<TraverseMachine> machine;
        uint64_t const version;
        size_t const max_outstanding_reads;
        size_t outstanding_reads{0};
        size_t within_recursion_count{0};
        bool version_expired_before_complete{false};
        TraverseList list;

        // List of pending reads sorted by path.
        PendingReads pending_reads;

        // List of pending reads sorted by read offset to allow merging
        // adjacent or overlapping reads.
        OffsetReads offset_reads;

        TraverseSender(
            UpdateAuxImpl &aux, Node::UniquePtr traverse_root,
            std::unique_ptr<TraverseMachine> machine, uint64_t const version,
            size_t const concurrency_limit)
            : aux(aux)
            , traverse_root(std::move(traverse_root))
            , machine(std::move(machine))
            , version(version)
            , max_outstanding_reads(concurrency_limit)
        {
        }

        TraverseSender(TraverseSender const &) = delete;
        TraverseSender(TraverseSender &&) = default;
        TraverseSender &operator=(TraverseSender const &) = delete;
        TraverseSender &operator=(TraverseSender &&) = default;

        ~TraverseSender()
        {
            // Delete incomplete traverse machines in case of early termination
            list.clear_and_dispose([](auto *n) { delete n; });
        }

        async::result<void>
        operator()(async::erased_connected_operation *traverse_state) noexcept
        {
            MONAD_ASSERT(traverse_root != nullptr);
            async_parallel_preorder_traverse_init(
                *this, traverse_state, *traverse_root);
            return async::success();
        }

        // return whether traverse has completed successfully
        async::result<bool> completed(
            async::erased_connected_operation *,
            async::result<void> res) noexcept
        {
            BOOST_OUTCOME_TRY(std::move(res));
            MONAD_ASSERT(within_recursion_count == 0);
            return async::success(!version_expired_before_complete);
        }

        void initiate_pending_reads(
            async::erased_connected_operation *traverse_state)
        {
            while (outstanding_reads < max_outstanding_reads &&
                   !pending_reads.empty()) {
                auto it = pending_reads.begin();
                auto &read = *it;
                async_read(
                    aux, receiver_t(this, traverse_state, std::move(read)));
                offset_reads.erase(offset_reads.iterator_to(read));
                pending_reads.erase(it);
                delete &read;
                ++outstanding_reads;
            }
        }

        static bool can_merge(
            TraverseSender::NodeRead const &lhs,
            TraverseSender::NodeRead const &rhs)
        {
            auto lhs_offset = lhs.rd_offset.raw();
            auto rhs_offset = rhs.rd_offset.raw();
            // check if ranges lhs_offset..lhs_offset+lhs.bytes_to_read and
            // rhs_offset..rhs_offset+rhs.bytes_to_read are adjacent or
            // intersecting
            return (
                lhs_offset + lhs.bytes_to_read >= rhs_offset &&
                rhs_offset + rhs.bytes_to_read >= lhs_offset);
        }

        static bool
        try_merge(TraverseSender::NodeRead &lhs, TraverseSender::NodeRead &rhs)
        {
            auto lhs_offset = lhs.rd_offset.raw();
            auto rhs_offset = rhs.rd_offset.raw();
            // check if ranges lhs_offset..lhs_offset+lhs.bytes_to_read and
            // rhs_offset..rhs_offset+rhs.bytes_to_read are adjacent or
            // intersecting
            if (lhs_offset + lhs.bytes_to_read >= rhs_offset &&
                rhs_offset + rhs.bytes_to_read >= lhs_offset) {

                // std::cout << "Merging reads: " << std::hex
                //           << "lhs_offset: " << (lhs_offset >> DISK_PAGE_BITS)
                //           << ", lhs.bytes_to_read: "
                //           << (lhs.bytes_to_read >> DISK_PAGE_BITS)
                //           << ", rhs_offset: " << (rhs_offset >>
                //           DISK_PAGE_BITS)
                //           << ", rhs.bytes_to_read: "
                //           << (rhs.bytes_to_read >> DISK_PAGE_BITS) <<
                //           std::dec
                //           << std::endl;

                // merge two reads
                auto start = std::min(lhs_offset, rhs_offset);
                auto end = std::max(
                    lhs_offset + lhs.bytes_to_read,
                    rhs_offset + rhs.bytes_to_read);

                lhs.bytes_to_read = unsigned(end - start);
                lhs.rd_offset.offset = start & chunk_offset_t::max_offset;
                lhs.rd_offset.id = (start >> 28) & chunk_offset_t::max_id;
                lhs.rd_offset.spare = 0; // spare is not used in this context

                // adjust lhs machine offsets
                if (lhs_offset != start) {
                    for (auto &mo : lhs.machine_offsets) {
                        mo.buffer_off += uint32_t(lhs_offset - start);
                    }
                }
                // move machines to lhs adjusting offset
                for (auto &mo : rhs.machine_offsets) {
                    mo.buffer_off += uint32_t(rhs_offset - start);
                    lhs.machine_offsets.emplace_back(std::move(mo));
                }
                rhs.machine_offsets.clear();
                if (*rhs.path < *lhs.path) {
                    // move rhs path to lhs path
                    lhs.path = rhs.path;
                }

                return true;
            }
            return false;
        }

        void add_pending_read(NodeRead &&read)
        {
            auto new_read = new TraverseSender::NodeReadInSet(std::move(read));
            // Check if we can merge with existing read.
            // Find element that ends at or after new element start.
            // This is leftmost mergeable element. Moreover, if this element
            // can't be merged, no other element can be merged either (this
            // element starts after new element ends and previous element
            // ends before new element starts).
            auto it = offset_reads.lower_bound(
                new_read->rd_offset.raw(), NodeRead::compare_offset_key{});
            while (it != offset_reads.end() && can_merge(*it, *new_read)) {
                auto &existing_read = *it;
                // remove existing read from offset_reads and
                // pending_reads
                it = offset_reads.erase(it);
                pending_reads.erase(pending_reads.iterator_to(existing_read));

                // std::cout << "Merging reads: " << std::hex << "lhs_offset: "
                //           << (existing_read.rd_offset.raw() >>
                //           DISK_PAGE_BITS)
                //           << std::dec << ", lhs.bytes_to_read: "
                //           << (existing_read.bytes_to_read >> DISK_PAGE_BITS)
                //           << ", lhs num mos: "
                //           << existing_read.machine_offsets.size() << std::hex
                //           << ", rhs_offset: "
                //           << (new_read->rd_offset.raw() >>
                //           DISK_PAGE_BITS)
                //           << std::dec << ", rhs.bytes_to_read: "
                //           << (new_read->bytes_to_read >> DISK_PAGE_BITS)
                //           << ", rhs num mos: "
                //           << new_read->machine_offsets.size() << std::dec
                //           << std::endl;

                (void)try_merge(existing_read, *new_read);
                delete new_read;
                new_read = &existing_read;
            }

            auto pret = pending_reads.insert(*new_read);
            MONAD_ASSERT(pret.second);
            auto oret = offset_reads.insert(*new_read);
            MONAD_ASSERT(oret.second);
        }
    };

    inline void async_parallel_preorder_traverse_init(
        TraverseSender &sender,
        async::erased_connected_operation *traverse_state, Node const &node)
    {
        if (!sender.aux.version_is_valid_ondisk(sender.version)) {
            sender.version_expired_before_complete = true;
            return;
        }
        sender.list.push_back(*sender.machine);
        sender.within_recursion_count++;
        sender.machine->branch = INVALID_BRANCH;
        async_parallel_preorder_traverse_impl(
            sender,
            traverse_state,
            copy_node(&node),
            *sender.machine.release());
        sender.within_recursion_count--;
        MONAD_ASSERT(sender.within_recursion_count == 0);

        // complete async traverse if no outstanding ios
        if (sender.pending_reads.empty() && sender.outstanding_reads == 0) {
            traverse_state->completed(async::success());
        }
    }

    inline void async_parallel_preorder_traverse_impl(
        TraverseSender &sender,
        async::erased_connected_operation *traverse_state,
        Node::UniquePtr _node, TraverseMachine &machine)
    {
        machine.node = std::move(_node);
        sender.initiate_pending_reads(traverse_state);
        if (machine.branch != INVALID_BRANCH) {
            machine.update_path(*machine.node);
        }
        auto should_visit_node =
            machine.should_visit_node(*machine.node, machine.branch);
        auto it = sender.list.iterator_to(machine);
        if (should_visit_node) {
            boost::container::small_vector<TraverseSender::NodeRead, 16> reads;
            for (auto const [idx, branch] :
                 NodeChildrenRange(machine.node->mask)) {
                if (machine.should_visit_child(*machine.node, branch)) {
                    auto const *const next = machine.node->next(idx);
                    auto child_machine = machine.clone(branch);
                    // Insert the child machine into the list after the current
                    // position of the iterator. All children are sorted after
                    // the parent since child key is parent key + branch.
                    //
                    // The list assumes ownership of the child machine so it is
                    // released below.
                    it = sender.list.insert(std::next(it), *child_machine);
                    if (next == nullptr) {
                        MONAD_ASSERT(sender.aux.is_on_disk());
                        reads.emplace_back(
                            machine.node->fnext(idx), *child_machine.release());
                    }
                    else {
                        async_parallel_preorder_traverse_impl(
                            sender,
                            traverse_state,
                            copy_node(next),
                            *child_machine.release());
                    }
                }
            }
            // for each receiver in receivers, check if we can merge
            std::sort(
                reads.begin(),
                reads.end(),
                [](auto const &lhs, auto const &rhs) {
                    return lhs.rd_offset < rhs.rd_offset;
                });
            for (auto i = 0u, j = 1u; j < reads.size(); ++j) {
                if (!TraverseSender::try_merge(reads[i], reads[j])) {
                    i = j;
                }
            }

            for (auto &read : reads) {
                if (read.machine_offsets.empty()) {
                    // This read was merged
                    continue;
                }
                if (sender.outstanding_reads >= sender.max_outstanding_reads) {
                    sender.add_pending_read(std::move(read));
                }
                else {
                    async_read(
                        sender.aux,
                        TraverseSender::receiver_t(
                            &sender, traverse_state, std::move(read)));
                    ++sender.outstanding_reads;
                }
            }
        }
        else {
            sender.list.erase_and_dispose(it, [](auto *n) { delete n; });
        }

        while (!sender.list.empty()) {
            auto &traverse = sender.list.front();
            if (traverse.node == nullptr) {
                // Next in order node is not ready yet
                break;
            }

            traverse.visit(traverse.branch, *traverse.node);

            sender.list.pop_front_and_dispose([](auto *n) { delete n; });
        }
    }
}

// return value indicates if we have done the full traversal or not
inline bool preorder_traverse_blocking(
    UpdateAuxImpl &aux, Node const &node, TraverseMachine &traverse,
    uint64_t const version)

{
    traverse.branch = INVALID_BRANCH;
    return detail::preorder_traverse_blocking_impl(
        aux, node, traverse, version);
}

inline bool preorder_traverse_ondisk(
    UpdateAuxImpl &aux, Node const &node, TraverseMachine &machine,
    uint64_t const version, size_t const concurrency_limit = 4096)
{
    MONAD_ASSERT(aux.is_on_disk());

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
            async::erased_connected_operation *traverse_state,
            async::result<bool> traverse_completed)
        {
            MONAD_ASSERT(traverse_completed);
            version_expired_before_traverse_complete_ =
                !traverse_completed.assume_value();
            delete traverse_state;
        }
    };

    bool version_expired_before_traverse_complete;
    auto machine_clone = machine.clone(INVALID_BRANCH);

    auto *const state = new auto(async::connect(
        detail::TraverseSender(
            aux,
            copy_node(&node),
            std::move(machine_clone),
            version,
            concurrency_limit),
        TraverseReceiver{version_expired_before_traverse_complete}));
    state->initiate();

    aux.io->wait_until_done();

    // return traversal succeeds or not
    return !version_expired_before_traverse_complete;
}

MONAD_MPT_NAMESPACE_END

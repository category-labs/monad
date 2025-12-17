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

#pragma once

#include <category/async/erased_connected_operation.hpp>
#include <category/async/io.hpp>
#include <category/core/assert.h>
#include <category/core/tl_tid.h>
#include <category/mpt/config.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/util.hpp>

#include <cstdint>
#include <functional>

#include <boost/container/deque.hpp>

#include "deserialize_node_from_receiver_result.hpp"

MONAD_MPT_NAMESPACE_BEGIN

struct TraverseMachine
{
    size_t level{0};

    virtual ~TraverseMachine() = default;
    // Implement the logic to decide when to stop, return true for continue,
    // false for stop
    virtual bool
    down(unsigned char branch, Node const &, NibblesView node_relpath) = 0;
    virtual void
    up(unsigned char branch, Node const &, NibblesView node_relpath) = 0;
    virtual std::unique_ptr<TraverseMachine> clone() const = 0;

    virtual bool should_visit(Node const &, unsigned char)
    {
        return true;
    }
};

// TODO: move definitions out of header file
namespace detail
{
    struct TraverseSender;

    void async_parallel_preorder_traverse_init(
        TraverseSender &, async::erased_connected_operation *traverse_state,
        Node const &);

    void async_parallel_preorder_traverse_impl(
        TraverseSender &sender,
        async::erased_connected_operation *traverse_state, Node const &node,
        NibblesView node_relpath, TraverseMachine &machine,
        unsigned char const branch);

    // current implementation does not contaminate triedb node caching
    inline bool preorder_traverse_blocking_impl(
        UpdateAuxImpl &aux, unsigned char const branch, Node const &node,
        NibblesView const node_relpath, TraverseMachine &traverse,
        uint64_t const version)
    {
        ++traverse.level;
        if (!traverse.down(branch, node, node_relpath)) {
            --traverse.level;
            return true;
        }
        for (auto const [idx, next_branch] : NodeChildrenRange(node.mask)) {
            if (traverse.should_visit(node, next_branch)) {
                if (Node::SharedPtr const &next = node.next(idx);
                    next != nullptr) {
                    if (!preorder_traverse_blocking_impl(
                            aux,
                            next_branch,
                            *next,
                            next->path_nibble_view().substr(
                                node.child_path_start_index()),
                            traverse,
                            version)) {
                        --traverse.level;
                        traverse.up(branch, node, node_relpath);
                        return false;
                    }
                    continue;
                }
                MONAD_ASSERT(aux.is_on_disk());
                auto const next_node_ondisk =
                    read_node_blocking(aux, node.fnext(idx), version);
                if (!next_node_ondisk ||
                    !preorder_traverse_blocking_impl(
                        aux,
                        next_branch,
                        *next_node_ondisk,
                        next_node_ondisk->path_nibble_view().substr(
                            node.child_path_start_index()),
                        traverse,
                        version)) {
                    --traverse.level;
                    traverse.up(branch, node, node_relpath);
                    return false;
                }
            }
        }
        --traverse.level;
        traverse.up(branch, node, node_relpath);
        return true;
    }

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
        struct receiver_t
        {
            static constexpr bool lifetime_managed_internally = true;

            TraverseSender *sender;
            async::erased_connected_operation *const traverse_state;
            std::unique_ptr<TraverseMachine> machine;
            chunk_offset_t rd_offset{0, 0};
            uint16_t buffer_off;
            unsigned char const branch;
            unsigned bytes_to_read;
            unsigned next_relpath_start_index;

            receiver_t(
                TraverseSender *sender,
                async::erased_connected_operation *const traverse_state,
                unsigned char const branch, chunk_offset_t const offset,
                unsigned const next_relpath_start_index,
                std::unique_ptr<TraverseMachine> machine)
                : sender(sender)
                , traverse_state(traverse_state)
                , machine(std::move(machine))
                , branch(branch)
                , next_relpath_start_index(next_relpath_start_index)
            {
                auto const num_pages_to_load_node =
                    node_disk_pages_spare_15{offset}.to_pages();
                bytes_to_read = static_cast<unsigned>(
                    num_pages_to_load_node << DISK_PAGE_BITS);
                rd_offset = offset;
                auto const new_offset =
                    round_down_align<DISK_PAGE_BITS>(offset.offset);
                MONAD_DEBUG_ASSERT(new_offset <= chunk_offset_t::max_offset);
                rd_offset.offset = new_offset & chunk_offset_t::max_offset;
                buffer_off = uint16_t(offset.offset - rd_offset.offset);
            }

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
                    sender->reads_to_initiate.clear();
                    sender->reads_to_initiate_sidx = 0;
                    sender->reads_to_initiate_eidx = 0;
                    sender->reads_to_initiate_count = 0;
                }
                else { // version is valid after reading the buffer
                    auto const next_node_on_disk =
                        deserialize_node_from_receiver_result(
                            std::move(buffer_), buffer_off, io_state);
                    sender->within_recursion_count++;
                    async_parallel_preorder_traverse_impl(
                        *sender,
                        traverse_state,
                        *next_node_on_disk,
                        next_node_on_disk->path_nibble_view().substr(
                            next_relpath_start_index),
                        *machine,
                        branch);
                    sender->within_recursion_count--;
                }
                // complete async traverse if no outstanding io AND there is no
                // recursive traverse call
                // `async_parallel_preorder_traverse_impl()` in current stack,
                // which means traverse is still in progress
                if (sender->within_recursion_count == 0 &&
                    sender->reads_to_initiate_count == 0 &&
                    sender->outstanding_reads == 0) {
                    traverse_state->completed(async::success());
                }
            }
        };

        static_assert(sizeof(receiver_t) == 48);
        static_assert(alignof(receiver_t) == 8);

        using result_type = async::result<bool>;

        UpdateAuxImpl &aux;
        Node::SharedPtr traverse_root;
        std::unique_ptr<TraverseMachine> machine;
        uint64_t const version;
        size_t const max_outstanding_reads;
        size_t outstanding_reads{0};
        size_t within_recursion_count{0};
        std::vector<boost::container::deque<receiver_t>> reads_to_initiate{20};
        size_t reads_to_initiate_sidx{0}; // exclusive
        size_t reads_to_initiate_eidx{0}; // inclusive
        size_t reads_to_initiate_count{0};
        bool version_expired_before_complete{false};

        TraverseSender(
            UpdateAuxImpl &aux, Node::SharedPtr traverse_root,
            std::unique_ptr<TraverseMachine> machine, uint64_t const version,
            size_t const concurrency_limit)
            : aux(aux)
            , traverse_root(std::move(traverse_root))
            , machine(std::move(machine))
            , version(version)
            , max_outstanding_reads(concurrency_limit)
        {
        }

        async::result<void>
        operator()(async::erased_connected_operation *traverse_state)
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

        void initiate_pending_reads()
        {
            auto idx = reads_to_initiate_eidx;
            while (outstanding_reads < max_outstanding_reads &&
                   idx > reads_to_initiate_sidx) {
                while (outstanding_reads < max_outstanding_reads &&
                       !reads_to_initiate[idx].empty()) {
                    async_read(aux, std::move(reads_to_initiate[idx].front()));
                    ++outstanding_reads;
                    reads_to_initiate[idx].pop_front();
                    --reads_to_initiate_count;
                }
                if (reads_to_initiate[idx].empty() &&
                    idx == reads_to_initiate_eidx) {
                    --reads_to_initiate_eidx;
                }
                --idx;
            }
            if (reads_to_initiate_count == 0) {
                reads_to_initiate_sidx = 0;
                reads_to_initiate_eidx = 0;
            }
        }
    };

    inline void async_parallel_preorder_traverse_init(
        TraverseSender &sender,
        async::erased_connected_operation *traverse_state, Node const &node)
    {
        sender.within_recursion_count++;
        async_parallel_preorder_traverse_impl(
            sender, traverse_state, node, {}, *sender.machine, INVALID_BRANCH);
        sender.within_recursion_count--;
        MONAD_ASSERT(sender.within_recursion_count == 0);

        // complete async traverse if no outstanding ios
        if (sender.reads_to_initiate_count == 0 &&
            sender.outstanding_reads == 0) {
            traverse_state->completed(async::success());
        }
    }

    inline void async_parallel_preorder_traverse_impl(
        TraverseSender &sender,
        async::erased_connected_operation *traverse_state, Node const &node,
        NibblesView const node_relpath, TraverseMachine &machine,
        unsigned char const branch)
    {
        // How many children are considered left side for depth first preference
        // Two and four was benchmarked as slightly worse than three, so three
        // appears to be the optimum.
        static constexpr unsigned LEFT_SIDE = 3;
        sender.initiate_pending_reads();
        // Detect if level (which is unsigned) has gone below zero. It never
        // should if this code is correct. The choice of 256 is completely
        // arbitrary and means nothing.
        MONAD_ASSERT(machine.level < 256);
        ++machine.level;
        if (!machine.down(branch, node, node_relpath)) {
            --machine.level;
            return;
        }
        unsigned children_read = 0;
        for (auto const [idx, branch] : NodeChildrenRange(node.mask)) {
            if (machine.should_visit(node, branch)) {
                Node::SharedPtr const &next = node.next(idx);
                if (next == nullptr) {
                    MONAD_ASSERT(sender.aux.is_on_disk());
                    // verify version before read
                    if (!sender.aux.version_is_valid_ondisk(sender.version)) {
                        sender.version_expired_before_complete = true;
                        sender.reads_to_initiate.clear();
                        sender.reads_to_initiate_sidx = 0;
                        sender.reads_to_initiate_eidx = 0;
                        sender.reads_to_initiate_count = 0;
                        return;
                    }
                    TraverseSender::receiver_t receiver(
                        &sender,
                        traverse_state,
                        branch,
                        node.fnext(idx),
                        node.child_path_start_index(),
                        machine.clone());
                    unsigned const this_child_read = children_read++;
                    if (sender.outstanding_reads >=
                        sender.max_outstanding_reads) {
                        // The deepest reads get highest priority
                        size_t priority = machine.level;
                        // Left side reads get a bit more priority
                        if (this_child_read < LEFT_SIDE) {
                            priority += LEFT_SIDE - this_child_read;
                        }
                        MONAD_DEBUG_ASSERT(priority > 0);
                        if (priority >= sender.reads_to_initiate.size()) {
                            sender.reads_to_initiate.resize(priority + 1);
                        }
                        if (priority > sender.reads_to_initiate_eidx) {
                            if (sender.reads_to_initiate_eidx == 0) {
                                sender.reads_to_initiate_sidx = priority - 1;
                            }
                            sender.reads_to_initiate_eidx = priority;
                        }
                        if (priority <= sender.reads_to_initiate_sidx) {
                            sender.reads_to_initiate_sidx = priority - 1;
                        }
                        sender.reads_to_initiate[priority].emplace_back(
                            std::move(receiver));
                        ++sender.reads_to_initiate_count;
                        continue;
                    }
                    async_read(sender.aux, std::move(receiver));
                    ++sender.outstanding_reads;
                }
                else {
                    async_parallel_preorder_traverse_impl(
                        sender,
                        traverse_state,
                        *next,
                        next->path_nibble_view().substr(
                            node.child_path_start_index()),
                        machine,
                        branch);
                    if (sender.version_expired_before_complete) {
                        return;
                    }
                }
            }
        }
        --machine.level;
        machine.up(branch, node, node_relpath);
    }
}

// return value indicates if we have done the full traversal or not
inline bool preorder_traverse_blocking(
    UpdateAuxImpl &aux, Node const &node, TraverseMachine &traverse,
    uint64_t const version)
{
    auto const ret = detail::preorder_traverse_blocking_impl(
        aux, INVALID_BRANCH, node, {}, traverse, version);
    MONAD_ASSERT(traverse.level == 0);
    return ret;
}

inline bool preorder_traverse_ondisk(
    UpdateAuxImpl &aux, Node::SharedPtr node, TraverseMachine &machine,
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

    auto *const state = new auto(async::connect(
        detail::TraverseSender(
            aux, std::move(node), machine.clone(), version, concurrency_limit),
        TraverseReceiver{version_expired_before_traverse_complete}));
    state->initiate();

    aux.io->wait_until_done();

    // return traversal succeeds or not
    return !version_expired_before_traverse_complete;
}

MONAD_MPT_NAMESPACE_END

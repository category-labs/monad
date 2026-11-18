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

#include <category/mpt/traverse.hpp>

#include <category/async/concepts.hpp>
#include <category/async/connected_operation.hpp>
#include <category/async/erased_connected_operation.hpp>
#include <category/async/io.hpp>
#include <category/core/assert.h>
#include <category/mpt/config.hpp>
#include <category/mpt/deserialize_node_from_receiver_result.hpp>
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/util.hpp>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <utility>

MONAD_MPT_NAMESPACE_BEGIN

namespace detail
{
    void async_parallel_preorder_traverse_init(
        TraverseSender &, async::erased_connected_operation *traverse_state,
        Node const &);

    void async_parallel_preorder_traverse_impl(
        TraverseSender &sender,
        async::erased_connected_operation *traverse_state, Node const &node,
        TraverseMachine &machine, unsigned char branch);

    struct TraverseSender::receiver_t
    {
        static constexpr bool lifetime_managed_internally = true;

        TraverseSender *sender;
        async::erased_connected_operation *const traverse_state;
        std::unique_ptr<TraverseMachine> machine;
        chunk_offset_t rd_offset{0, 0};
        unsigned bytes_to_read;
        uint16_t buffer_off;
        unsigned char const branch;

        receiver_t(
            TraverseSender *const sender,
            async::erased_connected_operation *const traverse_state,
            unsigned char const branch, chunk_offset_t const offset,
            std::unique_ptr<TraverseMachine> machine)
            : sender(sender)
            , traverse_state(traverse_state)
            , machine(std::move(machine))
            , branch(branch)
        {
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
        void set_value(
            monad::async::erased_connected_operation *io_state,
            ResultType buffer_)
        {
            MONAD_ASSERT(buffer_);
            --sender->outstanding_reads;
            if (sender->version_expired_before_complete ||
                !sender->aux.metadata_ctx().version_is_valid_ondisk(
                    sender->version, sender->tid)) {
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

    static_assert(sizeof(TraverseSender::receiver_t) == 40);
    static_assert(alignof(TraverseSender::receiver_t) == 8);

    TraverseSender::TraverseSender(
        UpdateAux &aux, Node::SharedPtr traverse_root,
        std::unique_ptr<TraverseMachine> machine, uint64_t const version,
        timeline_id const tid, size_t const concurrency_limit)
        : aux(aux)
        , traverse_root(std::move(traverse_root))
        , machine(std::move(machine))
        , version(version)
        , tid(tid)
        , max_outstanding_reads(concurrency_limit)
        , reads_to_initiate(20)
    {
    }

    TraverseSender::TraverseSender(TraverseSender &&) noexcept = default;

    TraverseSender::~TraverseSender() = default;

    async::result<void> TraverseSender::operator()(
        async::erased_connected_operation *const traverse_state)
    {
        MONAD_ASSERT(traverse_root != nullptr);
        async_parallel_preorder_traverse_init(
            *this, traverse_state, *traverse_root);
        return async::success();
    }

    async::result<bool> TraverseSender::completed(
        async::erased_connected_operation *, async::result<void> res) noexcept
    {
        BOOST_OUTCOME_TRY(std::move(res));
        MONAD_ASSERT(within_recursion_count == 0);
        return async::success(!version_expired_before_complete);
    }

    void TraverseSender::initiate_pending_reads()
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

    void async_parallel_preorder_traverse_init(
        TraverseSender &sender,
        async::erased_connected_operation *const traverse_state,
        Node const &node)
    {
        // False positive: preorder_traverse_ondisk allocates the sender with
        // `new auto(async::connect(...))`, and the analyzer does not model the
        // copy elision into the non-movable operation state, so it treats
        // this counter as never initialized.
        // NOLINTNEXTLINE(clang-analyzer-core.uninitialized.Assign)
        sender.within_recursion_count++;
        async_parallel_preorder_traverse_impl(
            sender, traverse_state, node, *sender.machine, INVALID_BRANCH);
        sender.within_recursion_count--;
        MONAD_ASSERT(sender.within_recursion_count == 0);

        // complete async traverse if no outstanding ios
        if (sender.reads_to_initiate_count == 0 &&
            sender.outstanding_reads == 0) {
            traverse_state->completed(async::success());
        }
    }

    void async_parallel_preorder_traverse_impl(
        TraverseSender &sender,
        async::erased_connected_operation *const traverse_state,
        Node const &node, TraverseMachine &machine, unsigned char const branch)
    {
        // How many children are considered left side for depth first
        // preference. Two and four was benchmarked as slightly worse than
        // three, so three appears to be the optimum.
        static constexpr unsigned LEFT_SIDE = 3;
        sender.initiate_pending_reads();
        // Detect if level (which is unsigned) has gone below zero. It never
        // should if this code is correct. The choice of 256 is completely
        // arbitrary and means nothing.
        MONAD_ASSERT(machine.level < 256);
        ++machine.level;
        if (!machine.down(branch, node)) {
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
                    if (!sender.aux.metadata_ctx().version_is_valid_ondisk(
                            sender.version, sender.tid)) {
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
                        sender, traverse_state, *next, machine, branch);
                    if (sender.version_expired_before_complete) {
                        return;
                    }
                }
            }
        }
        --machine.level;
        machine.up(branch, node);
    }
}

bool preorder_traverse_ondisk(
    UpdateAux &aux, Node::SharedPtr node, TraverseMachine &machine,
    uint64_t const version, timeline_id const tid,
    size_t const concurrency_limit)
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
            async::erased_connected_operation *const traverse_state,
            async::result<bool> const traverse_completed)
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
            aux,
            std::move(node),
            machine.clone(),
            version,
            tid,
            concurrency_limit),
        TraverseReceiver{version_expired_before_traverse_complete}));
    state->initiate();

    aux.io->flush();

    // return traversal succeeds or not
    return !version_expired_before_traverse_complete;
}

MONAD_MPT_NAMESPACE_END

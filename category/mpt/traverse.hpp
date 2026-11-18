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
#include <category/core/assert.h>
#include <category/mpt/config.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/util.hpp>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <vector>

#include <boost/container/deque.hpp>

MONAD_MPT_NAMESPACE_BEGIN

struct TraverseMachine
{
    size_t level{0};

    virtual ~TraverseMachine() = default;
    // Implement the logic to decide when to stop, return true for continue,
    // false for stop
    virtual bool down(unsigned char branch, Node const &) = 0;
    virtual void up(unsigned char branch, Node const &) = 0;
    virtual std::unique_ptr<TraverseMachine> clone() const = 0;

    virtual bool should_visit(Node const &, unsigned char)
    {
        return true;
    }
};

namespace detail
{
    struct DefaultChildrenVisitRange
    {
        auto operator()(uint16_t const mask) const
        {
            return NodeChildrenRange(mask);
        }
    };

    // current implementation does not contaminate triedb node caching
    template <class ChildrenVisitRange>
    inline bool preorder_traverse_blocking_impl(
        UpdateAux &aux, unsigned char const branch, Node const &node,
        TraverseMachine &traverse, uint64_t const version,
        ChildrenVisitRange &children_of, timeline_id const tid)
    {
        ++traverse.level;
        if (!traverse.down(branch, node)) {
            --traverse.level;
            return true;
        }
        auto const range = children_of(node.mask);
        for (auto const &[idx, next_branch] : range) {
            if (traverse.should_visit(node, next_branch)) {
                if (Node::SharedPtr const &next = node.next(idx);
                    next != nullptr) {
                    if (!preorder_traverse_blocking_impl(
                            aux,
                            next_branch,
                            *next,
                            traverse,
                            version,
                            children_of,
                            tid)) {
                        --traverse.level;
                        traverse.up(branch, node);
                        return false;
                    }
                    continue;
                }
                MONAD_ASSERT(aux.is_on_disk());
                auto const next_node_ondisk =
                    read_node_blocking(aux, node.fnext(idx), version, tid);
                if (!next_node_ondisk || !preorder_traverse_blocking_impl(
                                             aux,
                                             next_branch,
                                             *next_node_ondisk,
                                             traverse,
                                             version,
                                             children_of,
                                             tid)) {
                    --traverse.level;
                    traverse.up(branch, node);
                    return false;
                }
            }
        }
        --traverse.level;
        traverse.up(branch, node);
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
        struct receiver_t;

        using result_type = async::result<bool>;

        UpdateAux &aux;
        Node::SharedPtr traverse_root;
        std::unique_ptr<TraverseMachine> machine;
        uint64_t const version;
        timeline_id const tid;
        size_t const max_outstanding_reads;
        size_t outstanding_reads{0};
        size_t within_recursion_count{0};
        std::vector<boost::container::deque<receiver_t>> reads_to_initiate;
        size_t reads_to_initiate_sidx{0}; // exclusive
        size_t reads_to_initiate_eidx{0}; // inclusive
        size_t reads_to_initiate_count{0};
        bool version_expired_before_complete{false};

        TraverseSender(
            UpdateAux &aux, Node::SharedPtr traverse_root,
            std::unique_ptr<TraverseMachine> machine, uint64_t version,
            timeline_id tid, size_t concurrency_limit);
        // receiver_t is incomplete here, so these are defined out of line
        TraverseSender(TraverseSender &&) noexcept;
        ~TraverseSender();

        async::result<void>
        operator()(async::erased_connected_operation *traverse_state);

        // return whether traverse has completed successfully
        async::result<bool> completed(
            async::erased_connected_operation *,
            async::result<void> res) noexcept;

        void initiate_pending_reads();
    };
}

// return value indicates if we have done the full traversal or not
template <class ChildrenVisitRange = detail::DefaultChildrenVisitRange>
inline bool preorder_traverse_blocking(
    UpdateAux &aux, Node const &node, TraverseMachine &traverse,
    uint64_t const version, timeline_id const tid = timeline_id::primary,
    ChildrenVisitRange children_of = {})
{
    auto const ret = detail::preorder_traverse_blocking_impl(
        aux, INVALID_BRANCH, node, traverse, version, children_of, tid);
    MONAD_ASSERT(traverse.level == 0);
    return ret;
}

bool preorder_traverse_ondisk(
    UpdateAux &aux, Node::SharedPtr node, TraverseMachine &machine,
    uint64_t version, timeline_id tid = timeline_id::primary,
    size_t concurrency_limit = 4096);

MONAD_MPT_NAMESPACE_END

#pragma once

#include <monad/async/erased_connected_operation.hpp>
#include <monad/async/io.hpp>
#include <monad/core/tl_tid.h>
#include <monad/mpt/config.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/util.hpp>

#include <cstdint>
#include <functional>

#include <boost/container/deque.hpp>

#include "deserialize_node_from_receiver_result.hpp"

MONAD_MPT_NAMESPACE_BEGIN

struct TraverseMachine
{
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
        TraverseMachine &machine, unsigned char const branch);
}

namespace detail
{
    inline bool verify_version_valid(UpdateAuxImpl &aux, uint64_t const version)
    {
        return aux.is_on_disk() ? aux.version_is_valid_ondisk(version) : true;
    }

    // current implementation does not contaminate triedb node caching
    inline bool preorder_traverse_blocking_impl(
        UpdateAuxImpl &aux, unsigned char const branch, Node const &node,
        TraverseMachine &traverse, uint64_t const version)
    {
        if (!traverse.down(branch, node)) {
            return true;
        }
        for (unsigned char i = 0; i < 16; ++i) {
            if (node.mask & (1u << i)) {
                if (traverse.should_visit(node, (unsigned char)i)) {
                    auto const idx = node.to_child_index(i);
                    auto const *const next = node.next(idx);
                    if (next) {
                        preorder_traverse_blocking_impl(
                            aux, i, *next, traverse, version);
                        continue;
                    }
                    MONAD_ASSERT(aux.is_on_disk());
                    // verify version before read
                    if (!verify_version_valid(aux, version)) {
                        return false;
                    }
                    Node::UniquePtr next_disk{};
                    try {
                        next_disk = read_node_blocking(
                            aux.io->storage_pool(), node.fnext(idx));
                    }
                    catch (std::exception const &e) { // exception implies UB
                        return false;
                    }
                    preorder_traverse_blocking_impl(
                        aux, i, *next_disk, traverse, version);
                }
            }
        }
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
        struct receiver_t
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
                TraverseSender *sender,
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
                    !verify_version_valid(sender->aux, sender->version)) {
                    // async read failure or stopping initiated
                    sender->version_expired_before_complete = true;
                    sender->reads_to_initiate.clear();
                }
                else { // version is valid after reading the buffer
                    auto next_node_on_disk =
                        deserialize_node_from_receiver_result(
                            std::move(buffer_), buffer_off, io_state);
                    async_parallel_preorder_traverse_impl(
                        *sender,
                        traverse_state,
                        *next_node_on_disk,
                        *machine,
                        branch);
                }
                // complete async traverse if no outstanding ios
                if (sender->reads_to_initiate.empty() &&
                    sender->outstanding_reads == 0) {
                    traverse_state->completed(async::success());
                }
            }
        };

        static_assert(sizeof(receiver_t) == 40);
        static_assert(alignof(receiver_t) == 8);

        using result_type = async::result<bool>;

        UpdateAuxImpl &aux;
        Node::UniquePtr traverse_root;
        std::unique_ptr<TraverseMachine> machine;
        uint64_t const version;
        size_t const max_outstanding_reads;
        size_t outstanding_reads{0};
        size_t nreads{0};
        boost::container::deque<receiver_t> reads_to_initiate{};
        bool version_expired_before_complete{false};

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
            return async::success(!version_expired_before_complete);
        }

        void initiate_pending_reads()
        {
            while (outstanding_reads < max_outstanding_reads &&
                   !reads_to_initiate.empty()) {
                async_read(aux, std::move(reads_to_initiate.front()));
                ++outstanding_reads;
                reads_to_initiate.pop_front();
            }
        }
    };

    inline void async_parallel_preorder_traverse_init(
        TraverseSender &sender,
        async::erased_connected_operation *traverse_state, Node const &node)
    {
        async_parallel_preorder_traverse_impl(
            sender, traverse_state, node, *sender.machine, INVALID_BRANCH);

        // complete async traverse if no outstanding ios
        if (sender.reads_to_initiate.empty() && sender.outstanding_reads == 0) {
            traverse_state->completed(async::success());
        }
    }

    inline void async_parallel_preorder_traverse_impl(
        TraverseSender &sender,
        async::erased_connected_operation *traverse_state, Node const &node,
        TraverseMachine &machine, unsigned char const branch)
    {
        sender.initiate_pending_reads();
        if (!machine.down(branch, node)) {
            return;
        }
        for (unsigned i = 0, idx = 0, bit = 1; idx < node.number_of_children();
             ++i, bit <<= 1) {
            if (node.mask & bit) {
                if (machine.should_visit(node, (unsigned char)i)) {
                    auto const *const next = node.next(idx);
                    if (next == nullptr) {
                        MONAD_ASSERT(sender.aux.is_on_disk());
                        // verify version before read
                        if (!verify_version_valid(sender.aux, sender.version)) {
                            sender.version_expired_before_complete = true;
                            return;
                        }
                        TraverseSender::receiver_t receiver(
                            &sender,
                            traverse_state,
                            (unsigned char)i,
                            node.fnext(idx),
                            machine.clone());
                        if (sender.outstanding_reads >=
                            sender.max_outstanding_reads) {
                            sender.reads_to_initiate.emplace_back(
                                std::move(receiver));
                            ++idx;
                            continue;
                        }
                        async_read(sender.aux, std::move(receiver));
                        ++sender.outstanding_reads;
                        ++sender.nreads;
                    }
                    else {
                        async_parallel_preorder_traverse_impl(
                            sender,
                            traverse_state,
                            *next,
                            machine,
                            (unsigned char)i);
                    }
                }
                ++idx;
            }
        }
    }
}

// return value indicates if we have done the full traversal or not
inline bool preorder_traverse_blocking(
    UpdateAuxImpl &aux, Node const &node, TraverseMachine &traverse,
    uint64_t const version)
{
    return detail::preorder_traverse_blocking_impl(
        aux, INVALID_BRANCH, node, traverse, version);
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

    auto *const state = new auto(async::connect(
        detail::TraverseSender(
            aux, copy_node(&node), machine.clone(), version, concurrency_limit),
        TraverseReceiver{version_expired_before_traverse_complete}));
    state->initiate();

    aux.io->wait_until_done();

    // return traversal succeeds or not
    return !version_expired_before_traverse_complete;
}

MONAD_MPT_NAMESPACE_END

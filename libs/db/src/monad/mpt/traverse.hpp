#pragma once

#include <monad/async/erased_connected_operation.hpp>
#include <monad/async/io.hpp>
#include <monad/mpt/config.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/util.hpp>

#include <cstdint>
#include <functional>

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

namespace detail
{
    // current implementation does not contaminate triedb node caching
    template <typename VerifyVersionFunc>
    inline bool preorder_traverse_blocking_impl(
        UpdateAuxImpl &aux, unsigned char const branch, Node const &node,
        TraverseMachine &traverse, VerifyVersionFunc &&verify_func)
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
                            aux, i, *next, traverse, verify_func);
                        continue;
                    }
                    MONAD_ASSERT(aux.is_on_disk());
                    // verify version before read
                    if (!verify_func()) {
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
                        aux, i, *next_disk, traverse, verify_func);
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

    template <typename VerifyVersionFunc>
    struct preorder_traverse_impl
    {
        UpdateAuxImpl &aux;
        VerifyVersionFunc verify_func;
        bool stopping{false};

        struct receiver_t
        {
            static constexpr bool lifetime_managed_internally = true;
            preorder_traverse_impl *impl;
            std::unique_ptr<TraverseMachine> traverse;
            chunk_offset_t rd_offset{0, 0};
            unsigned bytes_to_read;
            uint16_t buffer_off;
            unsigned char const branch;

            receiver_t(
                preorder_traverse_impl *impl, unsigned char const branch,
                chunk_offset_t const offset,
                std::unique_ptr<TraverseMachine> traverse)
                : impl(impl)
                , traverse(std::move(traverse))
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
                if (!buffer_ || impl->stopping ||
                    !impl->verify_func()) { // async read failure or stopping
                                            // initiated
                    impl->stopping = true;
                    return;
                }
                try {
                    auto next_disk =
                        detail::deserialize_node_from_receiver_result(
                            std::move(buffer_), buffer_off, io_state);
                    // verify version after read is done
                    if (!impl->verify_func()) {
                        impl->stopping = true;
                        return;
                    }
                    impl->process(*next_disk, branch, *traverse);
                }
                catch (std::exception const &e) { // exception implies UB
                    impl->stopping = true;
                }
            }
        };

        void process(
            Node const &node, unsigned char const branch,
            TraverseMachine &traverse)
        {
            if (!traverse.down(branch, node)) {
                return;
            }
            for (unsigned i = 0, idx = 0, bit = 1;
                 idx < node.number_of_children();
                 ++i, bit <<= 1) {
                if (node.mask & bit) {
                    if (traverse.should_visit(node, (unsigned char)i)) {
                        auto const *const next = node.next(idx);
                        if (next == nullptr) {
                            MONAD_ASSERT(aux.is_on_disk());
                            // verify version before read
                            if (!verify_func()) {
                                stopping = true;
                            }
                            receiver_t receiver(
                                this,
                                (unsigned char)i,
                                node.fnext(idx),
                                traverse.clone());
                            async_read(aux, std::move(receiver));
                        }
                        else {
                            process(*next, (unsigned char)i, traverse);
                        }
                    }
                    ++idx;
                }
            }
            traverse.up(branch, node);
        }
    };
}

// return value indicates if we have done the full traversal or not
template <typename VerifyVersionFunc>
inline bool preorder_traverse_blocking(
    UpdateAuxImpl &aux, Node const &node, TraverseMachine &traverse,
    VerifyVersionFunc &&verify_func)
{
    return detail::preorder_traverse_blocking_impl(
        aux, INVALID_BRANCH, node, traverse, verify_func);
}

// parallel traversal using async i/o
template <typename VerifyVersionFunc>
inline bool preorder_traverse(
    UpdateAuxImpl &aux, Node const &node, TraverseMachine &traverse,
    VerifyVersionFunc verify_func)
{
    if (aux.io) {
        MONAD_ASSERT(aux.io->owning_thread_id() == gettid());
    }
    detail::preorder_traverse_impl<VerifyVersionFunc> impl(aux, verify_func);
    impl.process(node, INVALID_BRANCH, traverse);
    if (aux.io) {
        aux.io->wait_until_done();
    }
    return !impl.stopping;
}

MONAD_MPT_NAMESPACE_END

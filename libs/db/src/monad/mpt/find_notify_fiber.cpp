#include <monad/async/config.hpp>

#include <monad/async/concepts.hpp>
#include <monad/async/erased_connected_operation.hpp>
#include <monad/async/io.hpp>
#include <monad/core/assert.h>
#include <monad/core/nibble.h>
#include <monad/core/tl_tid.h>
#include <monad/mpt/config.hpp>
#include <monad/mpt/detail/boost_fiber_workarounds.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/util.hpp>

#include <boost/fiber/future.hpp>

#include <cassert>
#include <cstdint>
#include <limits>
#include <utility>

#include <unistd.h>

#include "deserialize_node_from_receiver_result.hpp"

MONAD_MPT_NAMESPACE_BEGIN

using namespace MONAD_ASYNC_NAMESPACE;

void find_recursive(
    UpdateAuxImpl &, inflight_map_t &,
    threadsafe_boost_fibers_promise<find_cursor_result_type> &, NodeCursor root,
    NibblesView key);

namespace
{
    struct find_receiver
    {
        static constexpr bool lifetime_managed_internally = true;

        UpdateAuxImpl *aux;
        inflight_map_t &inflights;
        Node *parent;
        chunk_offset_t rd_offset; // required for sender
        unsigned bytes_to_read; // required for sender too
        uint16_t buffer_off;
        unsigned const branch_index;

        find_receiver(
            UpdateAuxImpl &aux, inflight_map_t &inflights, Node *const parent,
            unsigned char const branch)
            : aux(&aux)
            , inflights(inflights)
            , parent(parent)
            , rd_offset(0, 0)
            , branch_index(parent->to_child_index(branch))
        {
            chunk_offset_t const offset = parent->fnext(branch_index);
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

        //! notify a list of requests pending on this node
        template <class ResultType>
        void set_value(
            MONAD_ASYNC_NAMESPACE::erased_connected_operation *io_state,
            ResultType buffer_)
        {
            MONAD_ASSERT(buffer_);
            auto const offset = parent->fnext(branch_index);
            auto *node = parent->next(branch_index);
            if (node == nullptr) {
                parent->set_next(
                    branch_index,
                    detail::deserialize_node_from_receiver_result(
                        std::move(buffer_), buffer_off, io_state));
                node = parent->next(branch_index);
            }
            auto it = inflights.find(offset);
            if (it != inflights.end()) {
                auto pendings = std::move(it->second);
                inflights.erase(it);
                for (auto &cont : pendings) {
                    MONAD_ASSERT(cont(NodeCursor{*node}));
                }
            }
        }
    };
}

// Use a hashtable for inflight requests, it maps a file offset to a list of
// requests. If a read request exists in the hash table, simply append to an
// existing inflight read, Otherwise, send a read request and put itself on the
// map
void find_recursive(
    UpdateAuxImpl &aux, inflight_map_t &inflights,
    threadsafe_boost_fibers_promise<find_cursor_result_type> &promise,
    NodeCursor root, NibblesView const key)

{
    if (!root.is_valid()) {
        promise.set_value(
            {NodeCursor{}, find_result::root_node_is_null_failure});
        return;
    }
    unsigned prefix_index = 0;
    unsigned node_prefix_index = root.prefix_index;
    Node *node = root.node;
    for (; node_prefix_index < node->path_nibble_index_end;
         ++node_prefix_index, ++prefix_index) {
        if (prefix_index >= key.nibble_size()) {
            promise.set_value(
                {NodeCursor{*node, node_prefix_index},
                 find_result::key_ends_earlier_than_node_failure});
            return;
        }
        if (key.get(prefix_index) !=
            get_nibble(node->path_data(), node_prefix_index)) {
            promise.set_value(
                {NodeCursor{*node, node_prefix_index},
                 find_result::key_mismatch_failure});
            return;
        }
    }
    if (prefix_index == key.nibble_size()) {
        promise.set_value(
            {NodeCursor{*node, node_prefix_index}, find_result::success});
        return;
    }
    MONAD_ASSERT(prefix_index < key.nibble_size());
    if (unsigned char const branch = key.get(prefix_index);
        node->mask & (1u << branch)) {
        MONAD_DEBUG_ASSERT(
            prefix_index < std::numeric_limits<unsigned char>::max());
        auto const next_key =
            key.substr(static_cast<unsigned char>(prefix_index) + 1u);
        auto const child_index = node->to_child_index(branch);
        if (node->next(child_index) != nullptr) {
            find_recursive(
                aux, inflights, promise, *node->next(child_index), next_key);
            return;
        }
        if (aux.io->owning_thread_id() != get_tl_tid()) {
            promise.set_value(
                {NodeCursor{*node, node_prefix_index},
                 find_result::need_to_continue_in_io_thread});
            return;
        }
        chunk_offset_t const offset = node->fnext(child_index);
        auto cont = [&aux, &inflights, &promise, next_key](
                        NodeCursor node_cursor) -> result<void> {
            find_recursive(aux, inflights, promise, node_cursor, next_key);
            return success();
        };
        if (auto lt = inflights.find(offset); lt != inflights.end()) {
            lt->second.emplace_back(cont);
            return;
        }
        inflights[offset].emplace_back(cont);
        find_receiver receiver(aux, inflights, node, branch);
        detail::initiate_async_read_update(
            *aux.io, std::move(receiver), receiver.bytes_to_read);
    }
    else {
        promise.set_value(
            {NodeCursor{*node, node_prefix_index},
             find_result::branch_not_exist_failure});
    }
}

void find_notify_fiber_future(
    UpdateAuxImpl &aux, inflight_map_t &inflights,
    fiber_find_request_t const req)
{
    auto g(aux.shared_lock());
    find_recursive(aux, inflights, *req.promise, req.start, req.key);
}

MONAD_MPT_NAMESPACE_END

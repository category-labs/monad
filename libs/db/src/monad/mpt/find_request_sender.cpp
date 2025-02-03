#include <monad/mpt/find_request_sender.hpp>

#include "deserialize_node_from_receiver_result.hpp"

#include <monad/async/concepts.hpp>
#include <monad/async/config.hpp>
#include <monad/async/erased_connected_operation.hpp>
#include <monad/core/assert.h>
#include <monad/core/nibble.h>
#include <monad/core/tl_tid.h>
#include <monad/mpt/config.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/util.hpp>

#include <cstdint>
#include <limits>

#include <unistd.h>

MONAD_MPT_NAMESPACE_BEGIN

using namespace MONAD_ASYNC_NAMESPACE;

// TODO: fix the version out of history range UB by version validation after
// each io
struct find_request_sender::find_receiver
{
    static constexpr bool lifetime_managed_internally = true;

    find_request_sender *const sender;
    erased_connected_operation *const io_state;

    chunk_offset_t rd_offset{0, 0}; // required for sender
    unsigned bytes_to_read; // required for sender too
    uint16_t buffer_off;
    unsigned const branch_index;

    constexpr find_receiver(
        find_request_sender *sender_, erased_connected_operation *io_state_,
        unsigned char const branch)
        : sender(sender_)
        , io_state(io_state_)
        , branch_index(sender->root_.node->to_child_index(branch))
    {
        chunk_offset_t const offset = sender->root_.node->fnext(branch_index);
        auto const num_pages_to_load_node =
            node_disk_pages_spare_15{offset}.to_pages();
        bytes_to_read =
            static_cast<unsigned>(num_pages_to_load_node << DISK_PAGE_BITS);
        rd_offset = offset;
        auto const new_offset = round_down_align<DISK_PAGE_BITS>(offset.offset);
        MONAD_DEBUG_ASSERT(new_offset <= chunk_offset_t::max_offset);
        rd_offset.offset = new_offset & chunk_offset_t::max_offset;
        buffer_off = uint16_t(offset.offset - rd_offset.offset);
    }

    // notify a list of requests pending on this node
    template <class ResultType>
    void set_value(
        MONAD_ASYNC_NAMESPACE::erased_connected_operation *, ResultType buffer_)
    {
        MONAD_ASSERT(buffer_);
        MONAD_ASSERT(sender->root_.is_valid());
        auto const next_offset = sender->root_.node->fnext(branch_index);
        auto *node = sender->root_.node->next(branch_index);
        if (node == nullptr) {
            auto node_ptr = detail::deserialize_node_from_receiver_result(
                std::move(buffer_), buffer_off, io_state);
            node = node_ptr.get();
            /* Nodes that are within cached level shares the same lifetime as
             the root node of current version.
             Starting from cached_level, the lifetime of the node is refcounted,
             and all nodes that are visited below this level will remain alive
             as long as the pending `find_request_sender`s are */
            if (sender->curr_level_ > sender->cached_levels_ &&
                sender->subtrie_with_sender_lifetime_ == nullptr) {
                sender->subtrie_with_sender_lifetime_ = std::move(node_ptr);
            }
            else {
                sender->root_.node->set_next(branch_index, std::move(node_ptr));
            }
        }
        auto it = sender->inflights_.find(next_offset);
        if (it != sender->inflights_.end()) {
            auto pendings = std::move(it->second);
            sender->inflights_.erase(it);
            auto subtrie_with_sender_lifetime_ =
                sender->subtrie_with_sender_lifetime_;
            for (auto &invoc : pendings) {
                MONAD_ASSERT(
                    invoc(NodeCursor(*node), subtrie_with_sender_lifetime_));
            }
        }
    }
};

result<void>
find_request_sender::operator()(erased_connected_operation *io_state) noexcept
{
    /* This is slightly bold, we basically repeatedly self reenter the Sender's
    initiation function until we complete. It is legal and it is allowed,
    just a bit quirky is all.
    */
    for (;;) {
        unsigned prefix_index = 0;
        unsigned node_prefix_index = root_.prefix_index;
        MONAD_ASSERT(root_.is_valid());
        Node *node = root_.node;
        for (; node_prefix_index < node->path_nibble_index_end;
             ++node_prefix_index, ++prefix_index) {
            if (prefix_index >= key_.nibble_size()) {
                res_ = {
                    byte_string{}, DbError::key_ends_earlier_than_node_failure};
                io_state->completed(success());
                return success();
            }
            if (key_.get(prefix_index) !=
                get_nibble(node->path_data(), node_prefix_index)) {
                res_ = {byte_string{}, DbError::key_mismatch_failure};
                io_state->completed(success());
                return success();
            }
        }
        if (prefix_index == key_.nibble_size()) {
            res_ = {
                byte_string{return_value_ ? node->value() : node->data()},
                DbError::success};
            io_state->completed(success());
            return success();
        }
        MONAD_ASSERT(prefix_index < key_.nibble_size());
        if (unsigned char const branch = key_.get(prefix_index);
            node->mask & (1u << branch)) {
            MONAD_DEBUG_ASSERT(
                prefix_index < std::numeric_limits<unsigned char>::max());
            key_ = key_.substr(static_cast<unsigned char>(prefix_index) + 1u);
            auto const child_index = node->to_child_index(branch);
            ++this->curr_level_;
            if (node->next(child_index) != nullptr) {
                root_ = NodeCursor{*node->next(child_index)};
                continue;
            }
            if (!tid_checked_) {
                MONAD_ASSERT(aux_.io != nullptr);
                if (aux_.io->owning_thread_id() != get_tl_tid()) {
                    res_ = {
                        byte_string{}, DbError::need_to_continue_in_io_thread};
                    return success();
                }
                tid_checked_ = true;
            }
            chunk_offset_t const offset = node->fnext(child_index);
            auto cont = [this, io_state](
                            NodeCursor const root,
                            std::shared_ptr<Node>
                                subtrie_with_sender_lifetime_) -> result<void> {
                this->subtrie_with_sender_lifetime_ =
                    subtrie_with_sender_lifetime_;
                return this->resume_(io_state, root);
            };
            if (auto lt = inflights_.find(offset); lt != inflights_.end()) {
                lt->second.emplace_back(cont);
                return success();
            }
            inflights_[offset].emplace_back(cont);
            find_receiver receiver(this, io_state, branch);
            detail::initiate_async_read_update(
                *aux_.io, std::move(receiver), receiver.bytes_to_read);
            return success();
        }
        else {
            res_ = {byte_string{}, DbError::branch_not_exist_failure};
            io_state->completed(success());
            return success();
        }
    }
}

MONAD_MPT_NAMESPACE_END

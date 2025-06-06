#pragma once

#include <monad/mpt/config.hpp>

#include <monad/async/io_senders.hpp>
#include <monad/mpt/node.hpp>

MONAD_MPT_NAMESPACE_BEGIN

namespace detail
{
    template <receiver Receiver>
        requires(
            MONAD_ASYNC_NAMESPACE::compatible_sender_receiver<
                read_short_update_sender, Receiver> &&
            MONAD_ASYNC_NAMESPACE::compatible_sender_receiver<
                read_long_update_sender, Receiver>)
    inline void initiate_async_read_update(
        MONAD_ASYNC_NAMESPACE::AsyncIO &io, Receiver &&receiver,
        size_t bytes_to_read)
    {
        [[likely]] if (
            bytes_to_read <= MONAD_ASYNC_NAMESPACE::AsyncIO::READ_BUFFER_SIZE) {
            read_short_update_sender sender(receiver);
            auto iostate =
                io.make_connected(std::move(sender), std::move(receiver));
            iostate->initiate();
            iostate.release();
        }
        else {
            read_long_update_sender sender(receiver);
            using connected_type =
                decltype(connect(io, std::move(sender), std::move(receiver)));
            auto *iostate = new connected_type(
                connect(io, std::move(sender), std::move(receiver)));
            iostate->initiate();
            // drop iostate
        }
    }

    template <class ResultType>
    inline Node::UniquePtr deserialize_node_from_receiver_result(
        ResultType buffer_, uint16_t buffer_off,
        MONAD_ASYNC_NAMESPACE::erased_connected_operation *io_state)
    {
        MONAD_ASSERT_PRINTF(
            buffer_,
            "i/o failed with %s",
            buffer_.assume_error().message().c_str());
        Node::UniquePtr node;
        if constexpr (std::is_same_v<
                          std::decay_t<ResultType>,
                          typename monad::async::read_single_buffer_sender::
                              result_type>) {
            auto &buffer = std::move(buffer_).assume_value().get();
            MONAD_ASSERT(buffer.size() > buffer_off);
            node = deserialize_node_from_buffer(
                (unsigned char *)buffer.data() + buffer_off,
                buffer.size() - buffer_off);
            buffer.reset();
        }
        else if constexpr (std::is_same_v<
                               std::decay_t<ResultType>,
                               typename monad::async::
                                   read_multiple_buffer_sender::result_type>) {
            // Comes from read_long_update_sender which always allocates single
            // buffer.
            MONAD_ASSERT(buffer_.assume_value().size() == 1);
            auto &buffer = buffer_.assume_value().front();
            MONAD_ASSERT(buffer.size() > buffer_off);
            // Did the Receiver forget to set lifetime_managed_internally?
            MONAD_DEBUG_ASSERT(io_state->lifetime_is_managed_internally());
            node = deserialize_node_from_buffer(
                (unsigned char *)buffer.data() + buffer_off,
                buffer.size() - buffer_off);
        }
        else {
            static_assert(false);
        }
        return node;
    }
}

MONAD_MPT_NAMESPACE_END

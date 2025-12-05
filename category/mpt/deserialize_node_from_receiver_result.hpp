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

#include <category/mpt/config.hpp>

#include <category/async/io_senders.hpp>
#include <category/mpt/node.hpp>

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
            auto iostate = io.make_connected(
                std::move(sender), std::forward<Receiver>(receiver));
            iostate->initiate();
            iostate.release();
        }
        else {
            read_long_update_sender sender(receiver);
            using connected_type = decltype(connect(
                io, std::move(sender), std::forward<Receiver>(receiver)));
            auto *iostate = new connected_type(connect(
                io, std::move(sender), std::forward<Receiver>(receiver)));
            iostate->initiate();
            // drop iostate
        }
    }

    template <class NodeType, class ResultType>
    inline NodeType::SharedPtr deserialize_node_from_receiver_result(
        ResultType buffer_, uint16_t buffer_off,
        MONAD_ASYNC_NAMESPACE::erased_connected_operation *io_state)
    {
        MONAD_ASSERT(buffer_);
        typename NodeType::SharedPtr node;
        if constexpr (std::is_same_v<
                          std::decay_t<ResultType>,
                          typename monad::async::read_single_buffer_sender::
                              result_type>) {
            auto &buffer = std::move(buffer_).assume_value().get();
            MONAD_ASSERT(buffer.size() > buffer_off);
            node = deserialize_node_from_buffer<NodeType>(
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
            auto const &buffer = buffer_.assume_value().front();
            MONAD_ASSERT(buffer.size() > buffer_off);
            // Did the Receiver forget to set lifetime_managed_internally?
            MONAD_DEBUG_ASSERT(io_state->lifetime_is_managed_internally());
            node = deserialize_node_from_buffer<NodeType>(
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

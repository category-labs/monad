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

#include <category/async/io.hpp>

#include <array>
#include <chrono>
#include <variant>

MONAD_ASYNC_NAMESPACE_BEGIN

/*! \class read_single_buffer_sender
\brief A Sender which (possibly partially) fills a single **registered** buffer
of bytes read from an offset in a file.

To have `AsyncIO` set a suitable registered buffer, you should Connect this to
its Receiver using `AsyncIO::make_connected()`.
*/
class read_single_buffer_sender
{
public:
    using buffer_type = filled_read_buffer;
    using const_buffer_type = filled_read_buffer;
    using result_type = result<std::reference_wrapper<buffer_type>>;

    static constexpr operation_type my_operation_type = operation_type::read;

private:
    chunk_offset_t offset_;
    buffer_type buffer_;
    bool defer_submit_;

public:
    constexpr read_single_buffer_sender(
        chunk_offset_t offset, size_t bytes_to_read, bool defer_submit = false)
        : offset_(offset)
        , buffer_(bytes_to_read)
        , defer_submit_(defer_submit)
    {
    }

    constexpr read_single_buffer_sender(
        chunk_offset_t offset, buffer_type buffer, bool defer_submit = false)
        : offset_(offset)
        , buffer_(std::move(buffer))
        , defer_submit_(defer_submit)
    {
    }

    constexpr chunk_offset_t offset() const noexcept
    {
        return offset_;
    }

    constexpr buffer_type const &buffer() const & noexcept
    {
        return buffer_;
    }

    constexpr buffer_type buffer() && noexcept
    {
        return std::move(buffer_);
    }

    void reset(
        chunk_offset_t offset, size_t bytes_to_read, bool defer_submit = false)
    {
        offset_ = offset;
        buffer_ = buffer_type(bytes_to_read);
        defer_submit_ = defer_submit;
    }

    void
    reset(chunk_offset_t offset, buffer_type buffer, bool defer_submit = false)
    {
        offset_ = offset;
        buffer_ = std::move(buffer);
        defer_submit_ = defer_submit;
    }

    result<void> operator()(erased_connected_operation *io_state)
    {
        if (!buffer_) {
            buffer_.set_read_buffer(
                io_state->executor()->get_read_buffer(buffer_.size()));
        }
        size_t const bytes_transferred =
            io_state->executor()->submit_read_request(
                buffer_.to_mutable_span(), offset_, io_state, defer_submit_);
        if (bytes_transferred != size_t(-1)) {
            // It completed early
            return make_status_code(
                sender_errc::initiation_immediately_completed,
                bytes_transferred);
        }
        return success();
    }

    result_type completed(
        erased_connected_operation *, result<size_t> bytes_transferred) noexcept
    {
        if (bytes_transferred.has_error()) {
            fprintf(
                stderr,
                "ERROR: Read single buffer of %zu bytes from chunk %u offset "
                "%llu failed with error '%s'\n",
                buffer().size(),
                offset().id,
                file_offset_t(offset().offset),
                bytes_transferred.assume_error().message().c_str());
        }

        BOOST_OUTCOME_TRY(auto &&count, std::move(bytes_transferred));
        buffer_.set_bytes_transferred(count);
        return success(std::ref(buffer_));
    }
};

static_assert(sizeof(read_single_buffer_sender) == 48);
static_assert(alignof(read_single_buffer_sender) == 8);
static_assert(sender<read_single_buffer_sender>);

/*! \class read_multiple_buffer_sender
\brief A Sender which (possibly partially) scatter fills one or more
**unregistered** buffers of bytes read from an offset in a file.

Unlike `read_single_buffer_sender`, this scatter reads into unregistered
buffers. You therefore should NOT use `AsyncIO::make_connected()`, in
fact if you try it will be a compile time error.

Instead simply `connect()` it as for a normal Sender-Receiver pair.
*/
class read_multiple_buffer_sender
{
    static constexpr size_t SMALL_BUFFERS_COUNT = 4;

public:
    using buffer_type = std::span<std::byte>;
    using const_buffer_type = std::span<std::byte const>;
    using buffers_type = std::span<buffer_type>;
    using const_buffers_type = std::span<const_buffer_type>;
    using result_type = result<buffers_type>;

    static constexpr operation_type my_operation_type =
        operation_type::read_scatter;

private:
    chunk_offset_t offset_;
    buffers_type buffers_;
    std::variant<
        std::array<struct iovec, SMALL_BUFFERS_COUNT>,
        std::vector<struct iovec>>
        iovecs_;

public:
    constexpr read_multiple_buffer_sender(
        chunk_offset_t offset, buffers_type buffers)
        : offset_(offset)
        , buffers_(buffers)
    {
    }

    constexpr chunk_offset_t offset() const noexcept
    {
        return offset_;
    }

    constexpr buffers_type buffers() const noexcept
    {
        return buffers_;
    }

    void reset(chunk_offset_t offset, buffers_type buffers)
    {
        offset_ = offset;
        buffers_ = buffers;
    }

    result<void> operator()(erased_connected_operation *io_state) noexcept
    {
        try {
            std::span<const struct iovec> iovecs;
            if (buffers_.size() <= SMALL_BUFFERS_COUNT) {
                std::array<struct iovec, SMALL_BUFFERS_COUNT> temp;
                {
                    size_t n = 0;
                    for (; n < buffers_.size(); n++) {
                        temp[n] = {
                            (char *)buffers_[n].data(), buffers_[n].size()};
                    }
                    // Without this, GCC complains in release builds :(
                    for (; n < temp.size(); n++) {
                        temp[n].iov_base = nullptr;
                        temp[n].iov_len = 0;
                    }
                }

                iovecs_ = temp;
                auto &v = std::get<0>(iovecs_);
                iovecs = v;
                iovecs = iovecs.subspan(0, buffers_.size());
            }
            else {
                std::vector<struct iovec> temp;
                temp.reserve(buffers_.size());
                for (auto const buffer : buffers_) {
                    temp.push_back({(char *)buffer.data(), buffer.size()});
                }
                iovecs_ = std::move(temp);
                auto &v = std::get<1>(iovecs_);
                iovecs = v;
            }
            size_t const bytes_transferred =
                io_state->executor()->submit_read_request(
                    iovecs, offset_, io_state);
            if (bytes_transferred != size_t(-1)) {
                // It completed early
                return make_status_code(
                    sender_errc::initiation_immediately_completed,
                    bytes_transferred);
            }
            return success();
        }
        catch (...) {
            return system_code_from_exception();
        }
    }

    result_type completed(
        erased_connected_operation *, result<size_t> bytes_transferred) noexcept
    {
        if (bytes_transferred.has_error()) {
            fprintf(
                stderr,
                "ERROR: Read multiple buffer from chunk %u offset "
                "%llu failed with error '%s'\n",
                offset().id,
                file_offset_t(offset().offset),
                bytes_transferred.assume_error().message().c_str());
        }
        BOOST_OUTCOME_TRY(auto &&count, std::move(bytes_transferred));
        for (size_t n = 0; n < buffers_.size(); n++) {
            if (buffers_[n].size() > count) {
                buffers_[n] = {buffers_[n].data(), count};
                buffers_ = buffers_.subspan(0, n + 1);
                break;
            }
            if (buffers_[n].size() == count) {
                buffers_ = buffers_.subspan(0, n + 1);
                break;
            }
            count -= buffers_[n].size();
        }
        return success(buffers_);
    }
};

static_assert(sizeof(read_multiple_buffer_sender) == 96);
static_assert(alignof(read_multiple_buffer_sender) == 8);
static_assert(sender<read_multiple_buffer_sender>);

/*! \class write_single_buffer_sender
\brief A Sender which (possibly partially) writes a single **registered** buffer
of bytes into an offset in a file.

To have `AsyncIO` set a suitable registered buffer, you should Connect this to
its Receiver using `AsyncIO::make_connected()`.

Writes are treated specially and separately to all other operations by
`AsyncIO`. They get their own, dedicated, io_uring instance exclusively used for
writes. The ring is always the size of the maximum number of write i/o buffers,
so it is never possible that initiating a write will find the submission queue
full. The write io_uring instance is exclusively addressed using
`IOSQE_IO_DRAIN` so every write submitted must complete before the next write
begins. A strict append-only sequential order is enforced so the storage only
ever sees a single append operation to existing content, and writes are never
ever out of order.

All this is done to reduce read-modify-write cycles by the storage thus reducing
flash wear, easing the load on the SSD's CPUs, and causing writes to be paced
to the speed of the SSD rather than flooding it with i/o. This especially
matters when the SSD runs out of SLC cache and write speed drops sixfold, we
need to substantially back off all i/o to let the SSD recover.
*/
class write_single_buffer_sender
{
public:
    using buffer_type = filled_write_buffer;
    using const_buffer_type = filled_write_buffer;
    using result_type = result<std::reference_wrapper<buffer_type>>;

    static constexpr operation_type my_operation_type = operation_type::write;

private:
    chunk_offset_t offset_;
    buffer_type buffer_;
    std::byte *append_;

public:
    constexpr write_single_buffer_sender(
        chunk_offset_t offset, size_t bytes_to_write)
        : offset_(offset)
        , buffer_(bytes_to_write)
        , append_(const_cast<std::byte *>(buffer_.data()))
    {
    }

    constexpr write_single_buffer_sender(
        chunk_offset_t offset, buffer_type buffer)
        : offset_(offset)
        , buffer_(std::move(buffer))
        , append_(const_cast<std::byte *>(buffer_.data()))
    {
    }

    constexpr chunk_offset_t offset() const noexcept
    {
        return offset_;
    }

    constexpr buffer_type const &buffer() const & noexcept
    {
        return buffer_;
    }

    constexpr buffer_type buffer() && noexcept
    {
        return std::move(buffer_);
    }

    void reset(chunk_offset_t offset, size_t bytes_to_write)
    {
        offset_ = offset;
        buffer_ = buffer_type(bytes_to_write);
        append_ = const_cast<std::byte *>(buffer_.data());
    }

    void reset(chunk_offset_t offset, buffer_type buffer)
    {
        offset_ = offset;
        buffer_ = std::move(buffer);
        append_ = const_cast<std::byte *>(buffer_.data());
    }

    result<void> operator()(erased_connected_operation *io_state) noexcept
    {
        MONAD_ASSERT(!!buffer_);
        buffer_.set_bytes_transferred(size_t(append_ - buffer_.data()));
        io_state->executor()->submit_write_request(buffer_, offset_, io_state);
        return success();
    }

    result_type completed(
        erased_connected_operation *, result<size_t> bytes_transferred) noexcept
    {
        if (bytes_transferred.has_error()) {
            fprintf(
                stderr,
                "ERROR: Write of %zu bytes to chunk %u offset %llu failed "
                "with "
                "error "
                "'%s'\n",
                buffer().size(),
                offset().id,
                file_offset_t(offset().offset),
                bytes_transferred.assume_error().message().c_str());
        }
        BOOST_OUTCOME_TRY(auto &&count, std::move(bytes_transferred));
        buffer_.set_bytes_transferred(count);
        return std::ref(buffer_);
    }

    constexpr size_t written_buffer_bytes() const noexcept
    {
        MONAD_ASSERT(buffer_.data() <= append_);
        return static_cast<size_t>(append_ - buffer_.data());
    }

    constexpr size_t remaining_buffer_bytes() const noexcept
    {
        auto const *end = buffer_.data() + buffer_.size();
        MONAD_ASSERT(end >= append_);
        return static_cast<size_t>(end - append_);
    }

    constexpr std::byte *advance_buffer_append(size_t bytes) noexcept
    {
        if (bytes > remaining_buffer_bytes()) {
            return nullptr;
        }
        auto *ret = append_;
        append_ += bytes;
        return ret;
    }
};

static_assert(sizeof(write_single_buffer_sender) == 48);
static_assert(alignof(write_single_buffer_sender) == 8);
static_assert(sender<write_single_buffer_sender>);

MONAD_ASYNC_NAMESPACE_END

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

#include <category/async/concepts.hpp>

#include <category/core/assert.h>

#include <boost/intrusive/rbtree_algorithms.hpp>

#include <chrono>
#include <cstddef>
#include <memory>
#include <span>

MONAD_ASYNC_NAMESPACE_BEGIN

class AsyncIO;

namespace detail
{
    struct AsyncIO_per_thread_state_t;

    class read_buffer_deleter
    {
        AsyncIO *parent_{nullptr};

    public:
        read_buffer_deleter() = default;

        constexpr explicit read_buffer_deleter(AsyncIO *parent)
            : parent_(parent)
        {
            MONAD_ASSERT(parent != nullptr);
        }

        inline void operator()(std::byte *b);
    };

    class write_buffer_deleter
    {
        AsyncIO *parent_{nullptr};

    public:
        write_buffer_deleter() = default;

        constexpr explicit write_buffer_deleter(AsyncIO *parent)
            : parent_(parent)
        {
            MONAD_ASSERT(parent != nullptr);
        }

        inline void operator()(std::byte *b);
    };

    using read_buffer_ptr = std::unique_ptr<std::byte, read_buffer_deleter>;
    using write_buffer_ptr = std::unique_ptr<std::byte, write_buffer_deleter>;
};

enum class operation_type : uint8_t
{
    unknown,
    read,
    write,
    read_scatter
};

/*! \class filled_read_buffer
\brief A span denoting how much of a `AsyncIO::read_buffer_ptr` has been filled,
also holding lifetime to the i/o buffer.
*/
class filled_read_buffer : protected std::span<std::byte const>
{
    using base_ = std::span<std::byte const>;
    detail::read_buffer_ptr buffer_;

public:
    using element_type = typename base_::element_type;
    using value_type = typename base_::value_type;
    using size_type = typename base_::size_type;
    using difference_type = typename base_::difference_type;
    using pointer = typename base_::pointer;
    using const_pointer = typename base_::const_pointer;
    using reference = typename base_::reference;
    using const_reference = typename base_::const_reference;
    using iterator = typename base_::iterator;
    using reverse_iterator = typename base_::reverse_iterator;

    using base_::begin;
    using base_::end;
    using base_::front;
    using base_::rbegin;
    using base_::rend;
    using base_::operator[];
    using base_::data;
    using base_::empty;
    using base_::first;
    using base_::last;
    using base_::size;
    using base_::size_bytes;
    using base_::subspan;

    constexpr filled_read_buffer() = default;

    filled_read_buffer(filled_read_buffer const &) = delete;
    filled_read_buffer(filled_read_buffer &&) = default;
    filled_read_buffer &operator=(filled_read_buffer const &) = delete;
    filled_read_buffer &operator=(filled_read_buffer &&) = default;

    constexpr explicit filled_read_buffer(size_t bytes_to_read)
        : base_((std::byte const *)nullptr, bytes_to_read)
    {
    }

    //! True if read buffer has been allocated
    explicit operator bool() const noexcept
    {
        return !!buffer_;
    }

    //! Allocates the i/o buffer
    void set_read_buffer(detail::read_buffer_ptr b) noexcept
    {
        buffer_ = std::move(b);
        auto *self = static_cast<base_ *>(this);
        *self = {buffer_.get(), self->size()};
    }

    //! Sets the span length
    void set_bytes_transferred(size_t bytes) noexcept
    {
        auto *span = static_cast<base_ *>(this);
        *span = span->subspan(0, bytes);
    }

    //! Reset the filled read buffer, releasing its i/o buffer
    void reset()
    {
        this->~filled_read_buffer();
        new (this) filled_read_buffer;
    }

    //! Return this as a span
    std::span<std::byte const> const &as_span() const noexcept
    {
        return *this;
    }

    //! Return a mutable span to this data
    std::span<std::byte> to_mutable_span() const noexcept
    {
        return {const_cast<std::byte *>(this->data()), this->size()};
    }
};

static_assert(sizeof(filled_read_buffer) == 32);
static_assert(alignof(filled_read_buffer) == 8);

/*! \class filled_write_buffer
\brief A span denoting how much of a `AsyncIO::write_buffer_ptr` was written,
also holding lifetime to the i/o buffer.
*/
class filled_write_buffer : protected std::span<std::byte const>
{
    using base_ = std::span<std::byte const>;
    detail::write_buffer_ptr buffer_;

public:
    using element_type = typename base_::element_type;
    using value_type = typename base_::value_type;
    using size_type = typename base_::size_type;
    using difference_type = typename base_::difference_type;
    using pointer = typename base_::pointer;
    using const_pointer = typename base_::const_pointer;
    using reference = typename base_::reference;
    using const_reference = typename base_::const_reference;
    using iterator = typename base_::iterator;
    using reverse_iterator = typename base_::reverse_iterator;

    using base_::begin;
    using base_::end;
    using base_::front;
    using base_::rbegin;
    using base_::rend;
    using base_::operator[];
    using base_::data;
    using base_::empty;
    using base_::first;
    using base_::last;
    using base_::size;
    using base_::size_bytes;
    using base_::subspan;

    constexpr filled_write_buffer() = default;

    filled_write_buffer(filled_write_buffer const &) = delete;
    filled_write_buffer(filled_write_buffer &&) = default;
    filled_write_buffer &operator=(filled_write_buffer const &) = delete;
    filled_write_buffer &operator=(filled_write_buffer &&) = default;

    constexpr explicit filled_write_buffer(size_t bytes_to_write)
        : base_((std::byte const *)nullptr, bytes_to_write)
    {
    }

    //! True if write buffer is allocated
    constexpr explicit operator bool() const noexcept
    {
        return !!buffer_;
    }

    //! Allocates the i/o buffer
    void set_write_buffer(detail::write_buffer_ptr b) noexcept
    {
        buffer_ = std::move(b);
        auto *self = static_cast<base_ *>(this);
        *self = {buffer_.get(), self->size()};
    }

    //! Sets the span length
    void set_bytes_transferred(size_t bytes) noexcept
    {
        auto *span = static_cast<base_ *>(this);
        *span = span->subspan(0, bytes);
    }

    //! Reset the filled write buffer
    void reset()
    {
        this->~filled_write_buffer();
        new (this) filled_write_buffer;
    }

    //! Return this as a span
    std::span<std::byte const> const &as_span() const noexcept
    {
        return *this;
    }

    //! Return a mutable span to this data
    std::span<std::byte> to_mutable_span() const noexcept
    {
        return {const_cast<std::byte *>(this->data()), this->size()};
    }
};

static_assert(sizeof(filled_write_buffer) == 32);
static_assert(alignof(filled_write_buffer) == 8);

/* \class erased_connected_operation
\brief A type erased abstract base class of a connected operation. Lets you
work with connection operation states with a type you are unaware of.
*/
class erased_connected_operation
{
public:
    friend struct detail::AsyncIO_per_thread_state_t;

    enum class initiation_result
    {
        initiation_success,
        initiation_failed_told_receiver,
        initiation_immediately_completed,
        deferred
    };

    enum class io_priority : uint8_t
    {
        highest,
        normal,
        idle
    };

protected:
    operation_type operation_type_{operation_type::unknown};
    bool being_executed_{false};
    bool lifetime_managed_internally_{
        false}; // some factory classes may deallocate states on their own
    io_priority io_priority_{io_priority::normal};
    std::atomic<AsyncIO *> io_{
        nullptr}; // set at construction if associated with an AsyncIO instance,
                  // which isn't mandatory

    struct rbtree_t_
    {
        /* Users of these fields:

           - `parent` gets used by `AsyncIO_per_thread_state` to keep a forward
           list of operations to be initiated when the thread stack unwinds. It
           stops using it before initiation.

           - `right` gets used by `AsyncIO::submit_request_()` to keep a
           forward list of operations initiated awaiting submission when
           concurrent operations submitted exceeds the runtime concurrency
           limit.

           - i/o read uses `key` between initiation and completion. It says what
           offset to add to bytes transferred returned.

           - i/o write uses `key` between initiation and completion. It says
           what offset the write is being performed at.
        */
        union
        {
            rbtree_t_ *parent{nullptr};
            erased_connected_operation *parent_;
        };

        union
        {
            rbtree_t_ *left{nullptr};
            erased_connected_operation *left_;
        };

        union
        {
            rbtree_t_ *right{nullptr};
            erased_connected_operation *right_;
        };

        file_offset_t key : 63 {0};
        file_offset_t color : 1 {false};
    } rbtree_;

    constexpr erased_connected_operation(
        operation_type operation_type, bool lifetime_managed_internally)
        : operation_type_(operation_type)
        , lifetime_managed_internally_(lifetime_managed_internally)
    {
    }

    constexpr erased_connected_operation(
        operation_type operation_type, AsyncIO &io,
        bool lifetime_managed_internally)
        : operation_type_(operation_type)
        , lifetime_managed_internally_(lifetime_managed_internally)
        , io_(&io)
    {
#ifndef __clang__
        MONAD_ASSERT(&io != nullptr);
#endif
    }

    virtual initiation_result
    do_possibly_deferred_initiate_(bool never_defer, bool is_retry) = 0;

public:
    union
    {
        std::chrono::steady_clock::time_point initiated;
        std::chrono::steady_clock::duration
            elapsed; // set upon completion if capture_io_latencies enabled
    };

    struct rbtree_node_traits
    {
        using node = rbtree_t_;
        using node_ptr = rbtree_t_ *;
        using const_node_ptr = rbtree_t_ const *;
        using color = bool;

        static node_ptr get_parent(const_node_ptr n)
        {
            return n->parent;
        }

        static void set_parent(node_ptr n, node_ptr parent)
        {
            n->parent = parent;
        }

        static node_ptr get_left(const_node_ptr n)
        {
            return n->left;
        }

        static void set_left(node_ptr n, node_ptr left)
        {
            n->left = left;
        }

        static node_ptr get_right(const_node_ptr n)
        {
            return n->right;
        }

        static void set_right(node_ptr n, node_ptr right)
        {
            n->right = right;
        }

        static color get_color(const_node_ptr n)
        {
            return n->color;
        }

        static void set_color(node_ptr n, color c)
        {
            n->color = c;
        }

        static color black()
        {
            return color(false);
        }

        static color red()
        {
            return color(true);
        }

        static file_offset_t get_key(const_node_ptr n)
        {
            return n->key;
        }

        static void set_key(node_ptr n, file_offset_t v)
        {
            static constexpr file_offset_t max_key = (1ULL << 63) - 1;
            MONAD_ASSERT(v <= max_key);
            n->key = v & max_key;
        }

        static erased_connected_operation *
        get_parent(erased_connected_operation const *n)
        {
            return n->rbtree_.parent_;
        }

        static void set_parent(
            erased_connected_operation *n, erased_connected_operation *parent)
        {
            n->rbtree_.parent_ = parent;
        }

        static erased_connected_operation *
        get_left(erased_connected_operation const *n)
        {
            return n->rbtree_.left_;
        }

        static void set_left(
            erased_connected_operation *n, erased_connected_operation *left)
        {
            n->rbtree_.left_ = left;
        }

        static erased_connected_operation *
        get_right(erased_connected_operation const *n)
        {
            return n->rbtree_.right_;
        }

        static void set_right(
            erased_connected_operation *n, erased_connected_operation *right)
        {
            n->rbtree_.right_ = right;
        }

        static file_offset_t get_key(erased_connected_operation const *n)
        {
            return n->rbtree_.key;
        }

        static void set_key(erased_connected_operation *n, file_offset_t v)
        {
            static constexpr file_offset_t max_key = (1ULL << 63) - 1;
            MONAD_ASSERT(v <= max_key);
            n->rbtree_.key = v & max_key;
        }

        static node_ptr to_node_ptr(erased_connected_operation *n)
        {
            return &n->rbtree_;
        }

        static const_node_ptr to_node_ptr(erased_connected_operation const *n)
        {
            return &n->rbtree_;
        }

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored                                                 \
    "-Winvalid-offsetof" // complains about lack of standard layout

        static erased_connected_operation *
        to_erased_connected_operation(node_ptr n)
        {
            return reinterpret_cast<erased_connected_operation *>(
                ((char *)n) - offsetof(erased_connected_operation, rbtree_));
        }

        static erased_connected_operation const *
        to_erased_connected_operation(const_node_ptr n)
        {
            return reinterpret_cast<erased_connected_operation const *>(
                ((char const *)n) -
                offsetof(erased_connected_operation, rbtree_));
        }

#pragma GCC diagnostic pop
    };
    friend struct rbtree_node_traits;

    virtual ~erased_connected_operation()
    {
        MONAD_ASSERT(!being_executed_);
    }

    bool is_unknown_operation_type() const noexcept
    {
        return operation_type_ == operation_type::unknown;
    }

    bool is_read() const noexcept
    {
        return operation_type_ == operation_type::read;
    }

    bool is_read_scatter() const noexcept
    {
        return operation_type_ == operation_type::read_scatter;
    }

    bool is_write() const noexcept
    {
        return operation_type_ == operation_type::write;
    }

    bool is_currently_being_executed() const noexcept
    {
        return being_executed_;
    }

    bool lifetime_is_managed_internally() const noexcept
    {
        return lifetime_managed_internally_;
    }

    enum io_priority io_priority() const noexcept
    {
        return io_priority_;
    }

    void set_io_priority(enum io_priority v) noexcept
    {
        io_priority_ = v;
    }

    //! The executor instance being used, which may be none.
    AsyncIO *executor() noexcept
    {
        return io_.load(std::memory_order_acquire);
    }

    //! Invoke completion. The Sender will send the value to the Receiver. If
    //! the Receiver expects an i/o buffer and the Sender does not transform
    //! this into an i/o buffer, terminates the program.
    virtual void completed(result<void> res) = 0;
    //! Invoke completion specifying the number of bytes
    //! transferred. If the Receiver does not expect bytes transferred, this
    //! will silently decay into the void `completed()` overload.
    virtual void completed(result<size_t> bytes_transferred) = 0;
    //! Invoke completion specifying the read buffer filled by reference. If the
    //! Receiver does not expect the read buffer filled, this will silently
    //! decay into the bytes transferred `completed()` overload.
    virtual void completed(result<std::reference_wrapper<filled_read_buffer>>
                               read_buffer_filled) = 0;
    //! Invoke completion specifying the write buffer written by reference. If
    //! the Receiver does not expect the write buffer written, this will
    //! silently decay into the bytes transferred `completed()` overload.
    virtual void completed(result<std::reference_wrapper<filled_write_buffer>>
                               write_buffer_written) = 0;

    // Overload ambiguity resolver so you can write `completed(success())`
    // without ambiguous overload warnings.
    void completed(BOOST_OUTCOME_V2_NAMESPACE::success_type<void> _)
    {
        completed(result<void>(_));
    }

    //! Invoke initiation, sending any failure to the receiver
    initiation_result initiate() noexcept
    {
        // NOTE Keep this in sync with the one in connected_operation_storage
        // we reimplement this there to aid devirtualisation.
        //
        // It is safe to not defer write op, because no write receivers do
        // recursion in current use cases thus no risk of stack exhaustion.
        return do_possibly_deferred_initiate_(is_write(), false);
    }

    //! Invoke re-initiation after temporary failutre, sending any failure to
    //! the receiver
    initiation_result reinitiate() noexcept
    {
        return do_possibly_deferred_initiate_(false, true);
    }

    void reset()
    {
        io_priority_ = io_priority::normal;
    }
};

static_assert(sizeof(erased_connected_operation) == 64);
static_assert(alignof(erased_connected_operation) == 8);

MONAD_ASYNC_NAMESPACE_END

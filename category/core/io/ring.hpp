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

#include <category/core/io/config.hpp>

#include <liburing.h>

#include <optional>

MONAD_IO_NAMESPACE_BEGIN

struct RingConfig
{
    unsigned entries{128}; //!< Number of submission queue entries
    /*! Enable i/o spin polling throughout the kernel i/o stack. Be aware if set
    all non-i/o operations will fail e.g. timers, posting across threads etc, as
    will all non-O_DIRECT i/o. And, some filesystems will refuse ops even with
    O_DIRECT turned on.
    */
    bool enable_io_polling{false};
    //! If set, turn on kernel polling of submission ring on the specified CPU
    std::optional<unsigned> sq_thread_cpu;

    RingConfig() = default;

    constexpr explicit RingConfig(unsigned const entries_)
        : entries(entries_)
    {
    }

    constexpr RingConfig(
        unsigned const entries_, bool const enable_io_polling_,
        std::optional<unsigned> const sq_thread_cpu_)
        : entries(entries_)
        , enable_io_polling(enable_io_polling_)
        , sq_thread_cpu(sq_thread_cpu_)
    {
    }
};

class Ring final
{
    io_uring ring_;
    io_uring_params const params_;

public:
    explicit Ring(RingConfig const &config = {});
    ~Ring();

    Ring(Ring const &) = delete;
    Ring(Ring &&) = delete;
    Ring &operator=(Ring const &) = delete;
    Ring &operator=(Ring &&) = delete;

    [[gnu::always_inline]] io_uring const &get_ring() const
    {
        return ring_;
    }

    [[gnu::always_inline]] io_uring &get_ring()
    {
        return ring_;
    }

    [[gnu::always_inline]] io_uring_params const &get_params() const
    {
        return params_;
    }

    [[gnu::always_inline]] unsigned get_sq_entries() const
    {
        return params_.sq_entries;
    }

    [[gnu::always_inline]] unsigned get_cq_entries() const
    {
        return params_.cq_entries;
    }

    [[gnu::always_inline]] bool must_call_uring_submit() const
    {
        return !(params_.flags & IORING_SETUP_SQPOLL);
    }
};

static_assert(sizeof(Ring) == 336);
static_assert(alignof(Ring) == 8);

MONAD_IO_NAMESPACE_END

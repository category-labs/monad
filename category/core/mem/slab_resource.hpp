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

#include <category/core/config.hpp>

#include <algorithm>
#include <atomic>
#include <cstddef>
#include <memory_resource>
#include <span>

MONAD_NAMESPACE_BEGIN

class slab_resource final : public std::pmr::memory_resource
{
    std::span<size_t const> slab_sizes_;
    std::pmr::synchronized_pool_resource pool_;
    std::atomic<size_t> *used_bytes_{nullptr};

public:
    slab_resource(
        std::span<size_t const> slab_sizes, std::pmr::pool_options opts = {},
        std::pmr::memory_resource *upstream = std::pmr::get_default_resource())
        : slab_sizes_(slab_sizes)
        , pool_(opts, upstream)
    {
    }

    void set_used_bytes(std::atomic<size_t> *used_bytes) noexcept
    {
        used_bytes_ = used_bytes;
    }

    void release()
    {
        pool_.release();
    }

private:
    void *do_allocate(size_t bytes, size_t alignment) override
    {
        size_t const sz = round_up(bytes);
        if (used_bytes_) {
            used_bytes_->fetch_add(sz, std::memory_order_relaxed);
        }
        return pool_.allocate(sz, alignment);
    }

    void do_deallocate(void *p, size_t bytes, size_t alignment) override
    {
        size_t const sz = round_up(bytes);
        pool_.deallocate(p, sz, alignment);
        if (used_bytes_) {
            used_bytes_->fetch_sub(sz, std::memory_order_relaxed);
        }
    }

    bool
    do_is_equal(std::pmr::memory_resource const &other) const noexcept override
    {
        return this == &other;
    }

    size_t round_up(size_t bytes) const noexcept
    {
        auto it =
            std::lower_bound(slab_sizes_.begin(), slab_sizes_.end(), bytes);
        return it == slab_sizes_.end() ? bytes : *it;
    }
};

MONAD_NAMESPACE_END

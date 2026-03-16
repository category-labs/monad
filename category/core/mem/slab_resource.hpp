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

#include <atomic>
#include <cstddef>
#include <memory_resource>

MONAD_NAMESPACE_BEGIN

class slab_resource final : public std::pmr::memory_resource
{
    std::pmr::synchronized_pool_resource pool_;
    std::atomic<size_t> used_bytes_{0};

public:
    explicit slab_resource(
        std::pmr::pool_options opts = {},
        std::pmr::memory_resource *upstream = std::pmr::get_default_resource())
        : pool_(opts, upstream)
    {
    }

    void release()
    {
        pool_.release();
        used_bytes_.store(0, std::memory_order_relaxed);
    }

    size_t used_bytes() const noexcept
    {
        return used_bytes_.load(std::memory_order_relaxed);
    }

private:
    void *do_allocate(size_t bytes, size_t alignment) override
    {
        used_bytes_.fetch_add(bytes, std::memory_order_relaxed);
        return pool_.allocate(bytes, alignment);
    }

    void do_deallocate(void *p, size_t bytes, size_t alignment) override
    {
        pool_.deallocate(p, bytes, alignment);
        used_bytes_.fetch_sub(bytes, std::memory_order_relaxed);
    }

    bool
    do_is_equal(std::pmr::memory_resource const &other) const noexcept override
    {
        return this == &other;
    }
};

MONAD_NAMESPACE_END

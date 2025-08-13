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

#include <category/core/mem/allocators.hpp>

#include <category/core/config.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdlib>
#include <memory>
#include <utility>

namespace
{
    static size_t constructed{0}, destructed{0}, allocated(0), deallocated(0);

    void reset()
    {
        constructed = destructed = allocated = deallocated = 0;
    }

    struct Foo
    {
        int x;

        Foo()
        {
            constructed++;
        }

        Foo(Foo const &o)
            : x(o.x)
        {
            constructed++;
        }

        explicit Foo(int a)
            : x(a)
        {
            constructed++;
        }

        ~Foo()
        {
            destructed++;
        }
    };

    struct custom_allocator
    {
        using value_type = Foo;
        using size_type = size_t;

        [[nodiscard]] value_type *allocate(size_type n)
        {
            allocated++;
            return std::allocator<value_type>().allocate(n);
        }

        void deallocate(value_type *p, size_type n) noexcept
        {
            deallocated++;
            std::allocator<value_type>().deallocate(p, n);
        }

        static custom_allocator &get()
        {
            static custom_allocator v;
            return v;
        }
    };

    struct raw_allocator
    {
        using value_type = std::byte;
        using size_type = size_t;

        [[nodiscard]] value_type *allocate(size_type n)
        {
            allocated++;
            return (std::byte *)std::malloc(n);
        }

        void deallocate(value_type *p, size_type) noexcept
        {
            deallocated++;
            free(p);
        }
    };

    static MONAD_NAMESPACE::allocators::detail::type_raw_alloc_pair<
        custom_allocator, raw_allocator>
    get_type_raw_alloc_pair()
    {
        static custom_allocator a;
        static raw_allocator b;
        return {a, b};
    }

    TEST(AllocatorsTest, allocate_unique)
    {
        using namespace MONAD_NAMESPACE::allocators;
        reset();
        allocate_unique<custom_allocator, &custom_allocator::get>();
        EXPECT_EQ(allocated, 1);
        EXPECT_EQ(constructed, 1);
        EXPECT_EQ(destructed, 1);
        EXPECT_EQ(deallocated, 1);
    }

    TEST(AllocatorsTest, aliasing_unique_ptr)
    {
        using namespace MONAD_NAMESPACE::allocators;
        reset();
        allocate_aliasing_unique<
            custom_allocator,
            raw_allocator,
            &get_type_raw_alloc_pair>(16);
        EXPECT_EQ(allocated, 1);
        EXPECT_EQ(constructed, 1);
        EXPECT_EQ(destructed, 1);
        EXPECT_EQ(deallocated, 1);
    }
}

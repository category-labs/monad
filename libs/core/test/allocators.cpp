#include <monad/mem/allocators.hpp>

#include <monad/config.hpp>
#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

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
        make_aliasing_unique<Foo>(16);
        EXPECT_EQ(allocated, 1);
        EXPECT_EQ(constructed, 2);
        EXPECT_EQ(destructed, 2);
        EXPECT_EQ(deallocated, 1);
    }
}

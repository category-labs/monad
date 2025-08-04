#include <category/vm/utils/rc_ptr.hpp>
#include <utility>

#include <gtest/gtest.h>

using namespace monad::vm::utils;

namespace
{
    struct TestInt
    {
        int value;
        int *ptr;

        explicit TestInt(int *x)
        {
            value = *x;
            ptr = x;
            ++*ptr;
        }

        ~TestInt()
        {
            --*ptr;
        }
    };

    using TestIntRcPtr = RcPtr<TestInt, RcObject<TestInt>::DefaultDeleter>;

    TestIntRcPtr make_test_int(int *ptr)
    {
        return TestIntRcPtr::make(RcObject<TestInt>::default_allocate, ptr);
    }

    void assign_test_int(TestIntRcPtr &x, TestIntRcPtr const &y)
    {
        x = y;
    }
};

TEST(RcPtr, make)
{
    int int_value = 1;
    {
        auto test_int1 = make_test_int(&int_value);
        ASSERT_EQ(test_int1->value, 1);
        ASSERT_EQ(int_value, 2);
        {
            auto test_int2 = make_test_int(&int_value);
            ASSERT_EQ(test_int2->value, 2);
            ASSERT_EQ(int_value, 3);
        }
        ASSERT_EQ(int_value, 2);
    }
    ASSERT_EQ(int_value, 1);
}

TEST(RcPtr, copy_constructor)
{
    int int_value = 1;
    {
        auto test_int1 = make_test_int(&int_value);
        ASSERT_EQ(test_int1->value, 1);
        ASSERT_EQ(int_value, 2);
        {
            TestIntRcPtr const test_int2(test_int1);
            ASSERT_EQ(test_int2->value, 1);
            ASSERT_EQ(int_value, 2);
        }
        ASSERT_EQ(int_value, 2);
    }
    ASSERT_EQ(int_value, 1);
}

TEST(RcPtr, copy_assignment)
{
    int int_value = 1;
    {
        auto test_int1 = make_test_int(&int_value);
        ASSERT_EQ(test_int1->value, 1);
        ASSERT_EQ(int_value, 2);
        {
            auto test_int2 = make_test_int(&int_value);
            ASSERT_EQ(test_int2->value, 2);
            ASSERT_EQ(int_value, 3);
            test_int2 = test_int1;
            ASSERT_EQ(test_int2->value, 1);
            ASSERT_EQ(int_value, 2);
        }
        ASSERT_EQ(int_value, 2);
    }
    ASSERT_EQ(int_value, 1);
}

TEST(RcPtr, move_constructor)
{
    int int_value = 1;
    {
        auto test_int1 = make_test_int(&int_value);
        ASSERT_EQ(test_int1->value, 1);
        ASSERT_EQ(int_value, 2);
        {
            TestIntRcPtr const test_int2(std::move(test_int1));
            ASSERT_EQ(test_int2->value, 1);
            ASSERT_EQ(int_value, 2);
        }
        ASSERT_EQ(int_value, 1);
    }
    ASSERT_EQ(int_value, 1);
}

TEST(RcPtr, move_assignment)
{
    int int_value = 1;
    {
        auto test_int1 = make_test_int(&int_value);
        ASSERT_EQ(test_int1->value, 1);
        ASSERT_EQ(int_value, 2);
        {
            auto test_int2 = make_test_int(&int_value);
            ASSERT_EQ(test_int2->value, 2);
            ASSERT_EQ(int_value, 3);
            test_int2 = std::move(test_int1);
            ASSERT_EQ(test_int2->value, 1);
            ASSERT_EQ(int_value, 2);
        }
        ASSERT_EQ(int_value, 1);
    }
    ASSERT_EQ(int_value, 1);
}

TEST(RcPtr, self_assignment)
{
    int int_value = 1;
    {
        auto test_int = make_test_int(&int_value);
        assign_test_int(test_int, test_int);
        ASSERT_EQ(test_int->value, 1);
        ASSERT_EQ(int_value, 2);
    }
    ASSERT_EQ(int_value, 1);
}

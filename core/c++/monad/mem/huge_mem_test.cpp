#include <monad/mem/huge_mem.h>

#include <gmock/gmock.h>
#include <gtest/gtest.h>

TEST(huge_mem, one_byte)
{
    huge_mem mem = {.size = 0, .data = nullptr};

    huge_mem_alloc(&mem, 1);

    EXPECT_EQ(mem.size, 1UL << 21);
    EXPECT_THAT(mem.data, testing::NotNull());

    huge_mem_free(&mem);
}

TEST(huge_mem, one_page)
{
    huge_mem mem = {.size = 0, .data = nullptr};

    huge_mem_alloc(&mem, 1UL << 21);

    EXPECT_EQ(mem.size, 1UL << 21);
    EXPECT_THAT(mem.data, testing::NotNull());

    huge_mem_free(&mem);
}

TEST(huge_mem, more_one_page)
{
    huge_mem mem = {.size = 0, .data = nullptr};

    huge_mem_alloc(&mem, (1UL << 21) + 1);

    EXPECT_EQ(mem.size, 1UL << 22);
    EXPECT_THAT(mem.data, testing::NotNull());

    huge_mem_free(&mem);
}

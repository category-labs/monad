#include <monad/mpt/config.hpp>

#include <monad/mpt/node.hpp>

#include <gtest/gtest.h>

#include <cstddef>

using namespace MONAD_MPT_NAMESPACE;

TEST(SpareBitsTest, construct_spare)
{
    {
        size_t const pages = 1023;
        node_disk_pages_spare_15 const spare{pages};
        EXPECT_TRUE(spare.to_pages() >= pages);
        EXPECT_EQ(spare.value.spare.count, 1023);
        EXPECT_EQ(spare.value.spare.shift, 0);
        EXPECT_EQ(spare.to_pages(), 1023);
    }

    {
        size_t const pages = 1024;
        node_disk_pages_spare_15 const spare{pages};
        EXPECT_TRUE(spare.to_pages() >= pages);
        EXPECT_EQ(spare.value.spare.count, 512);
        EXPECT_EQ(spare.value.spare.shift, 1);
        EXPECT_EQ(spare.to_pages(), 1024);
    }

    {
        size_t const pages = 1024 * 11;
        node_disk_pages_spare_15 const spare{pages};
        EXPECT_TRUE(spare.to_pages() >= pages);
        EXPECT_EQ(spare.value.spare.count, 704);
        EXPECT_EQ(spare.value.spare.shift, 4);
        EXPECT_EQ(spare.to_pages(), pages);
    }

    {
        size_t const pages = 1024 * 16; // 16384
        node_disk_pages_spare_15 const spare{pages};
        EXPECT_TRUE(spare.to_pages() >= pages);
        EXPECT_EQ(spare.value.spare.count, 512);
        EXPECT_EQ(spare.value.spare.shift, 5);
        EXPECT_EQ(spare.to_pages(), pages);
    }

    {
        size_t const pages = 1024 * 16 + 1; // 16384
        node_disk_pages_spare_15 const spare{pages};
        EXPECT_TRUE(spare.to_pages() >= pages);
        EXPECT_EQ(spare.value.spare.count, 513);
        EXPECT_EQ(spare.value.spare.shift, 5);
        EXPECT_EQ(spare.to_pages(), 16416);
    }

    {
        size_t const pages = 256745; // random
        node_disk_pages_spare_15 const spare{pages};
        EXPECT_EQ(spare.value.spare.count, 1003);
        EXPECT_EQ(spare.value.spare.shift, 8);
        EXPECT_EQ(spare.to_pages(), 256768);
    }
}

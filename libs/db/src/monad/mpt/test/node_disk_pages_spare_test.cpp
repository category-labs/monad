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
        size_t const pages = 1025;
        node_disk_pages_spare_15 const spare{pages};
        EXPECT_TRUE(spare.to_pages() >= pages);
        EXPECT_EQ(spare.value.spare.count, 513);
        EXPECT_EQ(spare.value.spare.shift, 1);
        EXPECT_EQ(spare.to_pages(), 1026);
    }

    {
        size_t const pages = 2046;
        node_disk_pages_spare_15 const spare{pages};
        EXPECT_TRUE(spare.to_pages() >= pages);
        EXPECT_EQ(spare.value.spare.count, 1023);
        EXPECT_EQ(spare.value.spare.shift, 1);
        EXPECT_EQ(spare.to_pages(), 2046);
    }

    {
        size_t const pages = 2047;
        node_disk_pages_spare_15 const spare{pages};
        EXPECT_TRUE(spare.to_pages() >= pages);
        EXPECT_EQ(spare.value.spare.count, 512);
        EXPECT_EQ(spare.value.spare.shift, 2);
        EXPECT_EQ(spare.to_pages(), 2048);
    }

    {
        size_t const pages = 2048;
        node_disk_pages_spare_15 const spare{pages};
        EXPECT_TRUE(spare.to_pages() >= pages);
        EXPECT_EQ(spare.value.spare.count, 512);
        EXPECT_EQ(spare.value.spare.shift, 2);
        EXPECT_EQ(spare.to_pages(), 2048);
    }

    {
        size_t const pages = 2049;
        node_disk_pages_spare_15 const spare{pages};
        EXPECT_TRUE(spare.to_pages() >= pages);
        EXPECT_EQ(spare.value.spare.count, 513);
        EXPECT_EQ(spare.value.spare.shift, 2);
        EXPECT_EQ(spare.to_pages(), 2052);
    }

    {
        size_t const pages = 4092;
        node_disk_pages_spare_15 const spare{pages};
        EXPECT_TRUE(spare.to_pages() >= pages);
        EXPECT_EQ(spare.value.spare.count, 1023);
        EXPECT_EQ(spare.value.spare.shift, 2);
        EXPECT_EQ(spare.to_pages(), 4092);
    }

    {
        size_t const pages = 4093;
        node_disk_pages_spare_15 const spare{pages};
        EXPECT_TRUE(spare.to_pages() >= pages);
        EXPECT_EQ(spare.value.spare.count, 512);
        EXPECT_EQ(spare.value.spare.shift, 3);
        EXPECT_EQ(spare.to_pages(), 4096);
    }

    {
        size_t const pages = 4094;
        node_disk_pages_spare_15 const spare{pages};
        EXPECT_TRUE(spare.to_pages() >= pages);
        EXPECT_EQ(spare.value.spare.count, 512);
        EXPECT_EQ(spare.value.spare.shift, 3);
        EXPECT_EQ(spare.to_pages(), 4096);
    }

    {
        size_t const pages = 4095;
        node_disk_pages_spare_15 const spare{pages};
        EXPECT_TRUE(spare.to_pages() >= pages);
        EXPECT_EQ(spare.value.spare.count, 512);
        EXPECT_EQ(spare.value.spare.shift, 3);
        EXPECT_EQ(spare.to_pages(), 4096);
    }

    {
        size_t const pages = 4096;
        node_disk_pages_spare_15 const spare{pages};
        EXPECT_TRUE(spare.to_pages() >= pages);
        EXPECT_EQ(spare.value.spare.count, 512);
        EXPECT_EQ(spare.value.spare.shift, 3);
        EXPECT_EQ(spare.to_pages(), 4096);
    }

    {
        size_t const pages = 4097;
        node_disk_pages_spare_15 const spare{pages};
        EXPECT_TRUE(spare.to_pages() >= pages);
        EXPECT_EQ(spare.value.spare.count, 513);
        EXPECT_EQ(spare.value.spare.shift, 3);
        EXPECT_EQ(spare.to_pages(), 4104);
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

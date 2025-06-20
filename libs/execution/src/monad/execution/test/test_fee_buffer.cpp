#include <monad/execution/fee_buffer.hpp>

#include <gtest/gtest.h>

using namespace monad;

TEST(FeeBuffer, basic)
{
    FeeBuffer buffer;
    for (unsigned block = 1; block <= 10; ++block) {
        buffer.set(block, block, block - 1);
        for (unsigned addr = 1; addr <= 10; ++addr) {
            buffer.note(addr, Address{addr}, addr * block);
        }
        buffer.propose();

        for (unsigned addr = 1; addr <= 10; ++addr) {
            EXPECT_EQ(
                buffer.sum(addr, Address{addr}),
                uint512_t{
                    (block * addr) + ((block > 1 ? block - 1 : 0) * addr) +
                    ((block > 2 ? block - 2 : 0) * addr)});
        }
    }
}

TEST(FeeBuffer, finalize)
{
    FeeBuffer buffer;
    buffer.set(0, 0, 0);
    buffer.note(0, Address{1}, 1);
    buffer.propose();

    buffer.set(1, 1, 0);
    buffer.note(0, Address{1}, 2);
    buffer.propose();

    buffer.set(2, 2, 1);
    buffer.note(0, Address{1}, 3);
    buffer.propose();

    EXPECT_EQ(buffer.sum(0, Address{1}), 6);

    buffer.finalize(2);

    EXPECT_EQ(buffer.sum(0, Address{1}), 6);

    buffer.set(3, 3, 2);
    buffer.note(0, Address{1}, 3);
    buffer.propose();
    EXPECT_EQ(buffer.sum(0, Address{1}), 8);
}

TEST(FeeBuffer, branch)
{
    FeeBuffer buffer;
    buffer.set(10, 10, 0);
    buffer.note(0, Address{1}, 1);
    buffer.propose();

    buffer.set(11, 11, 10);
    buffer.note(0, Address{1}, 2);
    buffer.propose();

    buffer.set(11, 12, 10);
    buffer.note(0, Address{1}, 3);
    buffer.propose();

    EXPECT_EQ(buffer.sum(0, Address{1}), 4);

    buffer.set(12, 13, 11);
    buffer.note(0, Address{1}, 2);
    buffer.propose();

    EXPECT_EQ(buffer.sum(0, Address{1}), 5);
}

TEST(FeeBuffer, cumulative)
{
    FeeBuffer buffer;
    buffer.set(10, 10, 0);
    buffer.note(0, Address{1}, 1);
    buffer.note(1, Address{1}, 3);
    buffer.propose();

    buffer.set(11, 11, 10);
    buffer.note(0, Address{1}, 2);
    buffer.note(1, Address{1}, 1);
    buffer.note(2, Address{1}, 10);
    buffer.propose();

    EXPECT_EQ(buffer.sum(0, Address{1}), 6);
    EXPECT_EQ(buffer.sum(1, Address{1}), 7);
    EXPECT_EQ(buffer.sum(2, Address{1}), 17);
}

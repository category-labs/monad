#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/state3/transient_storage.hpp>

#include <gtest/gtest.h>

using namespace monad;

namespace
{
    constexpr auto addr_0 = 0x01010101010101010101_address;
    constexpr auto addr_1 = 0xabababababababababab_address;

    constexpr auto zero_word = 0x00000000000000000000000000000000_bytes32;

    constexpr auto key_0 = 0x12341234123412341234123412341234_bytes32;
    constexpr auto key_1 = 0xabcdabcdabcdabcdabcdabcdabcdabcd_bytes32;

    constexpr auto val_0 = 0x00001111222233334444555566667777_bytes32;
    constexpr auto val_1 = 0xcafebeefcafebeefcafebeefcafebeef_bytes32;
}

TEST(TransientStorageTest, GetZero)
{
    TransientStorage ts;
    ASSERT_EQ(ts.get(addr_0, key_0), zero_word);
}

TEST(TransientStorageTest, SetGet)
{
    TransientStorage ts;

    ts.put(addr_0, key_0, val_0);
    ts.put(addr_1, key_1, val_1);

    ASSERT_EQ(ts.get(addr_0, key_0), val_0);
    ASSERT_EQ(ts.get(addr_1, key_1), val_1);

    ts.put(addr_1, key_1, val_0);
    ASSERT_EQ(ts.get(addr_1, key_1), val_0);
}

TEST(TransientStorageTest, SingleCommit)
{
    TransientStorage ts;

    ts.put(addr_0, key_0, val_0);
    ts.commit();
    ASSERT_EQ(ts.get(addr_0, key_0), val_0);
}

TEST(TransientStorageTest, SingleRevert)
{
    TransientStorage ts;

    ts.put(addr_0, key_0, val_0);
    ts.revert();
    ASSERT_EQ(ts.get(addr_0, key_0), zero_word);
}

TEST(TransientStorageTest, CheckpointRevert)
{
    TransientStorage ts;

    ts.put(addr_0, key_0, val_0);
    ts.checkpoint();

    ts.put(addr_0, key_1, val_1);
    ts.revert();

    ASSERT_EQ(ts.get(addr_0, key_0), val_0);
    ASSERT_EQ(ts.get(addr_1, key_1), zero_word);

    ts.revert();
    ASSERT_EQ(ts.get(addr_0, key_0), zero_word);
    ASSERT_EQ(ts.get(addr_1, key_1), zero_word);
}

TEST(TransientStorageTest, NestedCheckpoint)
{
    TransientStorage ts;

    ts.put(addr_0, key_0, val_0);
    ts.checkpoint();

    ts.put(addr_0, key_1, val_1);
    ts.checkpoint();

    ts.put(addr_1, key_0, val_1);
    ts.put(addr_1, key_1, val_0);

    ts.commit();
    ts.revert();

    ASSERT_EQ(ts.get(addr_1, key_0), zero_word);
    ASSERT_EQ(ts.get(addr_1, key_1), zero_word);
    ASSERT_EQ(ts.get(addr_0, key_1), zero_word);
    ASSERT_EQ(ts.get(addr_0, key_0), val_0);
}

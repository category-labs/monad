#include "fixture.hpp"

#include <monad/vm/runtime/keccak.hpp>
#include <monad/vm/runtime/memory.hpp>
#include <monad/vm/runtime/uint256.hpp>

using namespace monad::vm::runtime;
using namespace monad::vm::compiler::test;

TEST_F(RuntimeTest, KeccakEmpty)
{
    ASSERT_EQ(
        call(sha3, 0, 0),
        0xC5D2460186F7233C927E7DB2DCC703C0E500B653CA82273B7BFAD8045D85A470_u256);
}

TEST_F(RuntimeTest, KeccakNoExpand)
{
    ctx_.gas_remaining = 9;
    call(
        mstore,
        0,
        0xFFFFFFFF00000000000000000000000000000000000000000000000000000000_u256);
    ASSERT_EQ(ctx_.gas_remaining, 6);

    ASSERT_EQ(
        call(sha3, 0, 4),
        0x29045A592007D0C246EF02C2223570DA9522D0CF0F73282C79A1BC8F0BB2C238_u256);
    ASSERT_EQ(ctx_.gas_remaining, 0);
}

TEST_F(RuntimeTest, KeccakExpand)
{
    ctx_.gas_remaining = 27;
    ASSERT_EQ(
        call(sha3, 0, 65),
        0xAE61B77B3E4CBAC1353BFA4C59274E3AE531285C24E3CF57C11771ECBF72D9BF_u256);
    ASSERT_EQ(ctx_.memory.cost, 9);
    ASSERT_EQ(ctx_.gas_remaining, 0);
}

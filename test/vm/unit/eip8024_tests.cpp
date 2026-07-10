// Copyright (C) 2025-26 Category Labs, Inc.
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

// Tests for EIP-8024 (backward-compatible DUPN/SWAPN/EXCHANGE). The opcodes are
// gated on eip_8024_active(), which is true for EvmTraits from the AMSTERDAM
// revision onward -- so the execution tests run there and compare the
// interpreter against the compiler (evmone does not implement EIP-8024, so it
// cannot be the differential oracle).

#include <category/vm/evm/opcodes.hpp>
#include <category/vm/evm/revision.h>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/utils/evm-as.hpp>
#include <category/vm/utils/evm-as/compiler.hpp>

#include <test/vm/unit/evm_fixture.hpp>

#include <evmc/evmc.h>
#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <span>
#include <type_traits>
#include <vector>

using namespace monad::vm;
using enum monad::vm::compiler::EvmOpCode;

using monad::vm::compiler::eip8024_decode_pair;
using monad::vm::compiler::eip8024_decode_single;
using monad::vm::compiler::eip8024_encode_pair;
using monad::vm::compiler::eip8024_encode_single;
using monad::vm::compiler::eip8024_pair_disallowed;
using monad::vm::compiler::eip8024_single_disallowed;

namespace evm_as = monad::vm::utils::evm_as;

namespace
{
    // ----------------------------- codec ---------------------------------

    TEST(Eip8024Codec, SingleRoundTrip)
    {
        for (uint32_t n = 17; n <= 235; ++n) {
            auto const x = eip8024_encode_single(n);
            EXPECT_FALSE(eip8024_single_disallowed(x)) << "n=" << n;
            EXPECT_EQ(eip8024_decode_single(x), n) << "n=" << n;
        }
    }

    TEST(Eip8024Codec, SingleDisallowedRangeIsExactly91To127)
    {
        for (uint32_t x = 0; x <= 255; ++x) {
            bool const expect = x > 90 && x < 128;
            EXPECT_EQ(
                eip8024_single_disallowed(static_cast<uint8_t>(x)), expect)
                << "x=" << x;
        }
    }

    TEST(Eip8024Codec, PairRoundTrip)
    {
        // Enumerate the whole (n, m) domain: 1 <= n < m, n + m <= 30.
        size_t count = 0;
        for (uint8_t n = 1; n < 30; ++n) {
            for (uint8_t m = n + 1; n + m <= 30; ++m) {
                auto const x = eip8024_encode_pair(n, m);
                EXPECT_FALSE(eip8024_pair_disallowed(x))
                    << "n=" << +n << " m=" << +m;
                auto const [dn, dm] = eip8024_decode_pair(x);
                EXPECT_EQ(dn, n) << "n=" << +n << " m=" << +m;
                EXPECT_EQ(dm, m) << "n=" << +n << " m=" << +m;
                ++count;
            }
        }
        EXPECT_GT(count, 0u);
    }

    TEST(Eip8024Codec, PairDisallowedRangeIsExactly82To127)
    {
        for (uint32_t x = 0; x <= 255; ++x) {
            bool const expect = x > 81 && x < 128;
            EXPECT_EQ(eip8024_pair_disallowed(static_cast<uint8_t>(x)), expect)
                << "x=" << x;
        }
    }

    TEST(Eip8024Codec, KnownVectors)
    {
        // EIP-8024 test vectors.
        EXPECT_EQ(eip8024_encode_single(17), 0x80);
        EXPECT_EQ(eip8024_decode_single(0x80), 17u); // e680: DUPN 17
        EXPECT_EQ(eip8024_decode_single(0xdb), 108u); // e7db: SWAPN 108
        auto const [n, m] = eip8024_decode_pair(0x9d); // e89d: EXCHANGE 2,3
        EXPECT_EQ(n, 2);
        EXPECT_EQ(m, 3);

        // Extended EXCHANGE vectors: m > 16 exercises decode_pair's `else`
        // branch, and m == 16 is the upper edge of the `q < r` branch.
        auto const [n2, m2] = eip8024_decode_pair(0x2f); // e82f: EXCHANGE 1,19
        EXPECT_EQ(n2, 1);
        EXPECT_EQ(m2, 19);
        auto const [n3, m3] = eip8024_decode_pair(0x50); // e850: EXCHANGE 14,16
        EXPECT_EQ(n3, 14);
        EXPECT_EQ(m3, 16);
    }

    TEST(Eip8024Codec, SingleDecodeDomainAlwaysInRange)
    {
        // Every allowed single immediate must decode to n in [17, 235] so that
        // DUPN/SWAPN's run-time depth stays within the 1024 stack bound.
        for (uint32_t x = 0; x <= 255; ++x) {
            if (eip8024_single_disallowed(static_cast<uint8_t>(x))) {
                continue;
            }
            auto const n = eip8024_decode_single(static_cast<uint8_t>(x));
            EXPECT_GE(n, 17u) << "x=" << x;
            EXPECT_LE(n, 235u) << "x=" << x;
        }
    }

    TEST(Eip8024Codec, PairDecodeDomainAlwaysValid)
    {
        // Security-critical: the interpreter's EXCHANGE bounds check uses only
        // m (stack_size < m + 1), so decode_pair must yield 1 <= n < m for
        // EVERY allowed immediate -- not just encode()'s image -- or the
        // *(stack_top - n) access could read out of bounds. Sweep the whole
        // allowed domain to prove the disallowed-range check is sufficient.
        for (uint32_t x = 0; x <= 255; ++x) {
            if (eip8024_pair_disallowed(static_cast<uint8_t>(x))) {
                continue;
            }
            auto const [n, m] = eip8024_decode_pair(static_cast<uint8_t>(x));
            EXPECT_GE(n, 1) << "x=" << x;
            EXPECT_LT(n, m) << "x=" << x;
            EXPECT_LE(m, 29) << "x=" << x;
        }
    }

    // ------------------ jumpdest analysis (interpreter) ------------------

    using monad::vm::interpreter::Intercode;

    TEST(Eip8024Jumpdest, DisallowedImmediateByteRemainsAJumpdest)
    {
        // e75b: SWAPN with disallowed immediate 0x5B behaves as INVALID, and
        // the 0x5B is still a reachable JUMPDEST (the scan is not taught about
        // 0xE7's immediate). 0x5B == JUMPDEST.
        Intercode const ic(std::array<uint8_t, 2>{SWAPN, JUMPDEST});
        EXPECT_TRUE(ic.is_jumpdest(1));
    }

    TEST(Eip8024Jumpdest, ValidImmediateIsNotAJumpdest)
    {
        // A valid DUPN immediate is never 0x5B, so it is never a jump target.
        Intercode const ic(
            std::array<uint8_t, 2>{DUPN, eip8024_encode_single(17)});
        EXPECT_FALSE(ic.is_jumpdest(0));
        EXPECT_FALSE(ic.is_jumpdest(1));
    }

    TEST(Eip8024Jumpdest, RealJumpdestAfterValidInstructionIsFound)
    {
        // DUPN <imm> JUMPDEST : the JUMPDEST at offset 2 must be recognised.
        Intercode const ic(
            std::array<uint8_t, 3>{DUPN, eip8024_encode_single(17), JUMPDEST});
        EXPECT_FALSE(ic.is_jumpdest(1));
        EXPECT_TRUE(ic.is_jumpdest(2));
    }

    // --------------------- execution: interp vs compiler -----------------

    class Eip8024Test
        : public compiler::test::VMTraitsTestBase<
              std::integral_constant<monad_eth_revision, MONAD_ETH_AMSTERDAM>>
        , public ::testing::Test
    {
    protected:
        static constexpr int64_t kGas = 10'000'000;

        struct Outcome
        {
            evmc_status_code status;
            int64_t gas_left;
            std::vector<uint8_t> output;
        };

        Outcome
        run(std::span<uint8_t const> code, Implementation impl, int64_t gas)
        {
            host_ = {};
            execute(gas, code, {}, impl);
            return Outcome{
                result_.status_code,
                result_.gas_left,
                std::vector<uint8_t>(
                    result_.output_data,
                    result_.output_data + result_.output_size)};
        }

        // Runs both engines and asserts identical observable behaviour.
        Outcome expect_equal(std::span<uint8_t const> code, int64_t gas = kGas)
        {
            auto const i = run(code, Interpreter, gas);
            auto const c = run(code, Compiler, gas);
            EXPECT_EQ(c.status, i.status);
            EXPECT_EQ(c.gas_left, i.gas_left);
            EXPECT_EQ(c.output, i.output);
            return i;
        }

        void expect_both_fail(std::span<uint8_t const> code, int64_t gas = kGas)
        {
            auto const i = run(code, Interpreter, gas);
            auto const c = run(code, Compiler, gas);
            EXPECT_NE(i.status, EVMC_SUCCESS);
            EXPECT_NE(i.status, EVMC_REVERT);
            EXPECT_NE(c.status, EVMC_SUCCESS);
            EXPECT_NE(c.status, EVMC_REVERT);
        }

        // Assemble an EIP-8024-aware builder to bytecode.
        static std::vector<uint8_t> assemble(auto const &eb)
        {
            std::vector<uint8_t> code;
            evm_as::compile(eb, code);
            return code;
        }

        // Append: store top-of-stack at mem[0] then RETURN those 32 bytes.
        static void append_return_top(auto &eb)
        {
            eb.push0().mstore().return_(0, 32);
        }
    };

    TEST_F(Eip8024Test, DupnCopiesDeepElement)
    {
        // Stack (bottom..top) = 1..20; DUPN 17 duplicates the depth-17 item.
        // Depth 1 is 20, so depth 17 is value 4.
        auto eb = evm_as::amsterdam();
        for (uint8_t v = 1; v <= 20; ++v) {
            eb.push(v);
        }
        eb.dupn(17);
        append_return_top(eb);

        auto const out = expect_equal(assemble(eb));
        ASSERT_EQ(out.status, EVMC_SUCCESS);
        ASSERT_EQ(out.output.size(), 32u);
        EXPECT_EQ(out.output[31], 4);
    }

    TEST_F(Eip8024Test, DupnDeepestReachableElement)
    {
        // 235 items (1..235); DUPN 235 copies the bottom element (value 1).
        auto eb = evm_as::amsterdam();
        for (uint32_t v = 1; v <= 235; ++v) {
            eb.push(v);
        }
        eb.dupn(235);
        append_return_top(eb);

        auto const out = expect_equal(assemble(eb));
        ASSERT_EQ(out.status, EVMC_SUCCESS);
        ASSERT_EQ(out.output.size(), 32u);
        EXPECT_EQ(out.output[31], 1);
    }

    TEST_F(Eip8024Test, SwapnSwapsWithTop)
    {
        // Stack 1..20 (top=20). SWAPN 17 swaps top with the (17+1)=18th item.
        // Depth 18 is value 3, so after the swap the top is 3.
        auto eb = evm_as::amsterdam();
        for (uint8_t v = 1; v <= 20; ++v) {
            eb.push(v);
        }
        eb.swapn(17);
        append_return_top(eb);

        auto const out = expect_equal(assemble(eb));
        ASSERT_EQ(out.status, EVMC_SUCCESS);
        ASSERT_EQ(out.output.size(), 32u);
        EXPECT_EQ(out.output[31], 3);
    }

    TEST_F(Eip8024Test, ExchangeSwapsTwoNonTopItems)
    {
        // Stack (bottom..top) = 1..5. EXCHANGE (n=1,m=2) swaps the (n+1)=2nd
        // item (value 4) with the (m+1)=3rd item (value 3). Afterwards DUP2
        // duplicates the new 2nd item (value 3) to the top.
        auto eb = evm_as::amsterdam();
        for (uint8_t v = 1; v <= 5; ++v) {
            eb.push(v);
        }
        eb.exchange(1, 2);
        eb.dup(2); // duplicate the new 2nd item to the top
        append_return_top(eb);

        auto const out = expect_equal(assemble(eb));
        ASSERT_EQ(out.status, EVMC_SUCCESS);
        ASSERT_EQ(out.output.size(), 32u);
        EXPECT_EQ(out.output[31], 3);
    }

    TEST_F(Eip8024Test, ExchangeAliasedDuplicatedValue)
    {
        // Exercise Stack::exchange when a position aliases a duplicated value:
        // push 1..4, DUP1 (top now 4 again), EXCHANGE the two shallow items.
        auto eb = evm_as::amsterdam();
        for (uint8_t v = 1; v <= 4; ++v) {
            eb.push(v);
        }
        eb.dup(1);
        eb.exchange(1, 2);
        append_return_top(eb);

        // The strong signal here is interpreter == compiler.
        expect_equal(assemble(eb));
    }

    TEST_F(Eip8024Test, SwapnDeepReachesBottom)
    {
        // SWAPN 235 is the deepest single-operand reach (depth n+1 = 236) and
        // forces the compiler to address a spilled stack slot far below the
        // register file. Stack 1..236 (top=236); depth 236 is the bottom
        // (value 1), so after the swap the top is 1.
        auto eb = evm_as::amsterdam();
        for (uint32_t v = 1; v <= 236; ++v) {
            eb.push(v);
        }
        eb.swapn(235);
        append_return_top(eb);

        auto const out = expect_equal(assemble(eb));
        ASSERT_EQ(out.status, EVMC_SUCCESS);
        ASSERT_EQ(out.output.size(), 32u);
        EXPECT_EQ(out.output[31], 1);
    }

    TEST_F(Eip8024Test, ExchangeExtendedRange)
    {
        // EXCHANGE 1,19 uses decode_pair's `else` branch (m = 19 > 16) and
        // reaches depth m+1 = 20. Stack 1..20 (top=20): depth-2 is value 19 and
        // depth-20 is value 1, so the swap puts value 1 at depth-2; DUP2 brings
        // it to the top.
        auto eb = evm_as::amsterdam();
        for (uint8_t v = 1; v <= 20; ++v) {
            eb.push(v);
        }
        eb.exchange(1, 19);
        eb.dup(2); // bring the new depth-2 item to the top
        append_return_top(eb);

        auto const out = expect_equal(assemble(eb));
        ASSERT_EQ(out.status, EVMC_SUCCESS);
        ASSERT_EQ(out.output.size(), 32u);
        EXPECT_EQ(out.output[31], 1);
    }

    TEST_F(Eip8024Test, ExchangeDeepFirstOperand)
    {
        // EXCHANGE 14,16 has a deep first operand (n = 14, so depth-15 <->
        // depth-17) that none of the shallow cases cover. Stack 1..17 (top=17):
        // depth-15 is value 3 and depth-17 is value 1, so the swap puts value 1
        // at depth-15; DUP15 brings it to the top.
        auto eb = evm_as::amsterdam();
        for (uint8_t v = 1; v <= 17; ++v) {
            eb.push(v);
        }
        eb.exchange(14, 16);
        eb.dup(15); // bring the new depth-15 item to the top
        append_return_top(eb);

        auto const out = expect_equal(assemble(eb));
        ASSERT_EQ(out.status, EVMC_SUCCESS);
        ASSERT_EQ(out.output.size(), 32u);
        EXPECT_EQ(out.output[31], 1);
    }

    TEST_F(Eip8024Test, DisallowedSingleImmediateHaltsAsInvalid)
    {
        // 0xE6 0x5B : DUPN with disallowed immediate.
        std::vector<uint8_t> const c{DUPN, JUMPDEST};
        expect_both_fail(c);
    }

    TEST_F(Eip8024Test, DisallowedPairImmediateHaltsAsInvalid)
    {
        // e852: EXCHANGE 0x52 (0x52 == MSTORE, in the disallowed pair range).
        std::vector<uint8_t> const c{EXCHANGE, MSTORE};
        expect_both_fail(c);
    }

    TEST_F(Eip8024Test, DisallowedImmediateByteIsAReachableJumpdestInCompiler)
    {
        // Backward-compatibility guarantee, exercised on the compiler path (the
        // Eip8024Jumpdest cases above only cover the interpreter's Intercode
        // scan). A disallowed immediate makes the EIP-8024 opcode INVALID, but
        // its would-be immediate byte is NOT consumed by basic-block scanning,
        // so a 0x5B sitting there is still discovered as a JUMPDEST and stays a
        // legal jump target. Jump over a DUPN whose immediate is that JUMPDEST
        // and land on it:
        //
        //   0000  PUSH1 0x04  ; jump target = offset of the JUMPDEST
        //   0002  JUMP
        //   0003  DUPN        ; 0xE6; its would-be immediate is the next
        //   byte... 0004  JUMPDEST    ; 0x5B: disallowed DUPN immediate AND the
        //   target 0005  STOP
        //
        // If basic-block scanning wrongly swallowed the 0x5B as DUPN's
        // immediate, offset 4 would not be a valid destination and the JUMP
        // would fault. Must succeed (and agree) in both engines.
        std::vector<uint8_t> const c{PUSH1, 0x04, JUMP, DUPN, JUMPDEST, STOP};
        auto const out = expect_equal(c);
        EXPECT_EQ(out.status, EVMC_SUCCESS);
    }

    TEST_F(Eip8024Test, UnderflowHaltsInBothEngines)
    {
        // DUPN 17 needs 17 items but only two are present.
        auto eb = evm_as::amsterdam();
        eb.push(1).push(2).dupn(17);
        expect_both_fail(assemble(eb));
    }

    TEST_F(Eip8024Test, TruncatedImmediateHaltsWithoutOob)
    {
        // DUPN as the final byte: the missing immediate reads as 0, which
        // decodes to n=145 -> underflow. Must fail, not read out of bounds.
        std::vector<uint8_t> const c{PUSH1, 0x01, DUPN};
        expect_both_fail(c);
    }

    TEST_F(Eip8024Test, OutOfGasBoundary)
    {
        // Enough gas for the pushes but not the DUPN: both must run out.
        auto eb = evm_as::amsterdam();
        for (uint8_t v = 1; v <= 20; ++v) {
            eb.push(v);
        }
        eb.dupn(17);
        append_return_top(eb);
        // 20 * PUSH1 (3 each) = 60 gas; give exactly that so DUPN OOGs.
        expect_both_fail(assemble(eb), 60);
    }

    // ------------------- exhaustive operand sweeps -----------------------

    // Sweep every valid DUPN operand (not just the shallow/deepest cases
    // above) and assert the interpreter and compiler agree, exercising the
    // full register-file-to-spilled-slot addressing range in codegen.
    TEST_F(Eip8024Test, DupnFullOperandSweep)
    {
        for (uint32_t n = 17; n <= 235; ++n) {
            auto eb = evm_as::amsterdam();
            for (uint32_t v = 1; v <= n + 1; ++v) {
                eb.push(v);
            }
            eb.dupn(n);
            append_return_top(eb);
            auto const out = expect_equal(assemble(eb));
            ASSERT_EQ(out.status, EVMC_SUCCESS) << "n=" << n;
            ASSERT_EQ(out.output.size(), 32u) << "n=" << n;
            // Stack (bottom..top) = 1..(n+1); depth n holds value 2.
            EXPECT_EQ(out.output[31], 2) << "n=" << n;
        }
    }

    TEST_F(Eip8024Test, SwapnFullOperandSweep)
    {
        for (uint32_t n = 17; n <= 235; ++n) {
            auto eb = evm_as::amsterdam();
            for (uint32_t v = 1; v <= n + 1; ++v) {
                eb.push(v);
            }
            eb.swapn(n);
            append_return_top(eb);
            auto const out = expect_equal(assemble(eb));
            ASSERT_EQ(out.status, EVMC_SUCCESS) << "n=" << n;
            ASSERT_EQ(out.output.size(), 32u) << "n=" << n;
            // SWAPN n swaps depth-1 with depth-(n+1); with stack 1..(n+1) the
            // latter is the bottom (value 1), so the top becomes 1.
            EXPECT_EQ(out.output[31], 1) << "n=" << n;
        }
    }

    TEST_F(Eip8024Test, ExchangeFullOperandSweep)
    {
        size_t count = 0;
        for (uint8_t n = 1; n < 30; ++n) {
            for (uint8_t m = n + 1; n + m <= 30; ++m) {
                auto eb = evm_as::amsterdam();
                for (uint32_t v = 1; v <= static_cast<uint32_t>(m) + 1; ++v) {
                    eb.push(v);
                }
                eb.exchange(n, m);
                eb.dup(n + 1); // bring the new depth-(n+1) item to the top
                append_return_top(eb);
                auto const out = expect_equal(assemble(eb));
                ASSERT_EQ(out.status, EVMC_SUCCESS)
                    << "n=" << +n << " m=" << +m;
                ASSERT_EQ(out.output.size(), 32u) << "n=" << +n << " m=" << +m;
                // EXCHANGE swaps depth-(n+1) with depth-(m+1); with stack
                // 1..(m+1) the latter is the bottom (value 1), so depth-(n+1)
                // becomes 1.
                EXPECT_EQ(out.output[31], 1) << "n=" << +n << " m=" << +m;
                ++count;
            }
        }
        EXPECT_GT(count, 0u);
    }

    TEST_F(Eip8024Test, DupnStackOverflowBoundary)
    {
        // DUPN is the only EIP-8024 opcode that grows the stack (+1), so it is
        // the only one that can overflow. 1023 items + DUPN reaches exactly the
        // 1024 limit and must succeed in both engines...
        {
            auto eb = evm_as::amsterdam();
            for (uint32_t v = 1; v <= 1023; ++v) {
                eb.push(v);
            }
            eb.dupn(17).stop();
            auto const out = expect_equal(assemble(eb));
            EXPECT_EQ(out.status, EVMC_SUCCESS);
        }
        // ...whereas 1024 items + DUPN would exceed 1024 and must halt in both.
        {
            auto eb = evm_as::amsterdam();
            for (uint32_t v = 1; v <= 1024; ++v) {
                eb.push(v);
            }
            eb.dupn(17).stop();
            expect_both_fail(assemble(eb));
        }
    }

    // ----------------------------- dormancy ------------------------------

    class Eip8024DormantTest
        : public compiler::test::VMTraitsTestBase<
              std::integral_constant<monad_eth_revision, MONAD_ETH_OSAKA>>
        , public ::testing::Test
    {
    protected:
        evmc_status_code run(std::span<uint8_t const> code, Implementation impl)
        {
            host_ = {};
            execute(1'000'000, code, {}, impl);
            return result_.status_code;
        }
    };

    TEST_F(Eip8024DormantTest, OpcodesUndefinedWhenFlagOff)
    {
        // At OSAKA eip_8024_active() is false: 0xE6/E7/E8 are undefined and
        // both engines treat them as INVALID.
        for (uint8_t op : {DUPN, SWAPN, EXCHANGE}) {
            std::vector<uint8_t> const c{PUSH1, 0x01, op, 0x00};
            EXPECT_NE(run(c, Interpreter), EVMC_SUCCESS) << "op=" << +op;
            EXPECT_NE(run(c, Compiler), EVMC_SUCCESS) << "op=" << +op;
        }
        EXPECT_TRUE(
            compiler::is_unknown_opcode_info<monad::EvmTraits<MONAD_ETH_OSAKA>>(
                DUPN));
    }
}

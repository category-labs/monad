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

#include <category/vm/compiler/ir/basic_blocks.hpp>
#include <category/vm/compiler/ir/instruction.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/evm/revision.h>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/utils/evm-as.hpp>
#include <category/vm/utils/evm-as/compiler.hpp>
#include <category/vm/utils/parser.hpp>

#include <test/vm/unit/evm_fixture.hpp>

#include <evmc/evmc.h>
#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <format>
#include <span>
#include <type_traits>
#include <utility>
#include <vector>

using namespace monad::vm;
using enum monad::vm::compiler::EvmOpCode;

using monad::EvmTraits;
using monad::vm::compiler::eip8024_decode_pair;
using monad::vm::compiler::eip8024_decode_single;
using monad::vm::compiler::eip8024_encode_pair;
using monad::vm::compiler::eip8024_encode_single;
using monad::vm::compiler::eip8024_pair_disallowed;
using monad::vm::compiler::eip8024_single_disallowed;

namespace evm_as = monad::vm::utils::evm_as;

namespace
{
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

        // Extended vectors covering both branches of decode_pair: m > 16 and
        // the m == 16 edge.
        auto const [n2, m2] = eip8024_decode_pair(0x2f); // e82f: EXCHANGE 1,19
        EXPECT_EQ(n2, 1);
        EXPECT_EQ(m2, 19);
        auto const [n3, m3] = eip8024_decode_pair(0x50); // e850: EXCHANGE 14,16
        EXPECT_EQ(n3, 14);
        EXPECT_EQ(m3, 16);
    }

    TEST(Eip8024Codec, SingleDecodeDomainAlwaysInRange)
    {
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
        // check_requirements_eip8024 bounds only m, so n < m must hold for
        // every allowed immediate.
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

    using monad::vm::interpreter::Intercode;

    TEST(Eip8024Jumpdest, DisallowedImmediateByteRemainsAJumpdest)
    {
        Intercode const ic(std::array<uint8_t, 2>{SWAPN, JUMPDEST});
        EXPECT_TRUE(ic.is_jumpdest(1));
    }

    TEST(Eip8024Jumpdest, ValidImmediateIsNotAJumpdest)
    {
        Intercode const ic(
            std::array<uint8_t, 2>{DUPN, eip8024_encode_single(17)});
        EXPECT_FALSE(ic.is_jumpdest(0));
        EXPECT_FALSE(ic.is_jumpdest(1));
    }

    TEST(Eip8024Jumpdest, RealJumpdestAfterValidInstructionIsFound)
    {
        Intercode const ic(
            std::array<uint8_t, 3>{DUPN, eip8024_encode_single(17), JUMPDEST});
        EXPECT_FALSE(ic.is_jumpdest(1));
        EXPECT_TRUE(ic.is_jumpdest(2));
    }

    TEST(Eip8024Ir, IrCarriesDecodedOperands)
    {
        using monad::vm::compiler::OpCode;
        using monad::vm::compiler::basic_blocks::unsafe_make_ir;

        std::vector<uint8_t> const code{
            DUPN,
            eip8024_encode_single(17),
            SWAPN,
            eip8024_encode_single(108),
            EXCHANGE,
            eip8024_encode_pair(2, 3),
        };
        auto const ir = unsafe_make_ir<EvmTraits<MONAD_ETH_AMSTERDAM>>(
            std::span<uint8_t const>{code});
        ASSERT_EQ(ir.blocks().size(), 1u);
        auto const &instrs = ir.blocks()[0].instrs;
        ASSERT_EQ(instrs.size(), 3u);

        EXPECT_EQ(instrs[0].opcode(), OpCode::DupN);
        EXPECT_EQ(instrs[0].index(), 17u);
        EXPECT_EQ(instrs[1].opcode(), OpCode::SwapN);
        EXPECT_EQ(instrs[1].index(), 108u);
        EXPECT_EQ(instrs[2].opcode(), OpCode::Exchange);
        EXPECT_EQ(
            instrs[2].exchange_indices(), (std::pair<uint8_t, uint8_t>{2, 3}));

        EXPECT_EQ(std::format("{}", instrs[0]), "DUPN 17");
        EXPECT_EQ(std::format("{}", instrs[1]), "SWAPN 108");
        EXPECT_EQ(std::format("{}", instrs[2]), "EXCHANGE 2, 3");
    }

    TEST(Eip8024Ir, DisallowedImmediateIsInvalid)
    {
        using monad::vm::compiler::basic_blocks::Terminator;
        using monad::vm::compiler::basic_blocks::unsafe_make_ir;

        std::vector<uint8_t> const code{DUPN, JUMPDEST};
        auto const ir = unsafe_make_ir<EvmTraits<MONAD_ETH_AMSTERDAM>>(
            std::span<uint8_t const>{code});
        ASSERT_FALSE(ir.blocks().empty());
        EXPECT_TRUE(ir.blocks()[0].instrs.empty());
        EXPECT_EQ(ir.blocks()[0].terminator, Terminator::InvalidInstruction);
        EXPECT_TRUE(ir.jump_dests().contains(1));
    }

    class Eip8024Test
        : public test::VMTraitsTestBase<
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
            EXPECT_EQ(c.status, i.status);
            EXPECT_NE(i.status, EVMC_SUCCESS);
            EXPECT_NE(i.status, EVMC_REVERT);
            EXPECT_NE(c.status, EVMC_SUCCESS);
            EXPECT_NE(c.status, EVMC_REVERT);
        }

        static std::vector<uint8_t> assemble(auto const &eb)
        {
            std::vector<uint8_t> code;
            evm_as::compile(eb, code);
            return code;
        }

        static void append_return_top(auto &eb)
        {
            eb.push0().mstore().return_(0, 32);
        }
    };

    TEST_F(Eip8024Test, DupnCopiesDeepElement)
    {
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
        auto eb = evm_as::amsterdam();
        for (uint8_t v = 1; v <= 5; ++v) {
            eb.push(v);
        }
        eb.exchange(1, 2);
        eb.dup(2);
        append_return_top(eb);

        auto const out = expect_equal(assemble(eb));
        ASSERT_EQ(out.status, EVMC_SUCCESS);
        ASSERT_EQ(out.output.size(), 32u);
        EXPECT_EQ(out.output[31], 3);
    }

    TEST_F(Eip8024Test, ExchangeAliasedDuplicatedValue)
    {
        auto eb = evm_as::amsterdam();
        for (uint8_t v = 1; v <= 4; ++v) {
            eb.push(v);
        }
        eb.dup(1);
        eb.exchange(1, 2);
        append_return_top(eb);

        expect_equal(assemble(eb));
    }

    TEST_F(Eip8024Test, SwapnDeepReachesBottom)
    {
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
        auto eb = evm_as::amsterdam();
        for (uint8_t v = 1; v <= 20; ++v) {
            eb.push(v);
        }
        eb.exchange(1, 19);
        eb.dup(2);
        append_return_top(eb);

        auto const out = expect_equal(assemble(eb));
        ASSERT_EQ(out.status, EVMC_SUCCESS);
        ASSERT_EQ(out.output.size(), 32u);
        EXPECT_EQ(out.output[31], 1);
    }

    TEST_F(Eip8024Test, ExchangeDeepFirstOperand)
    {
        auto eb = evm_as::amsterdam();
        for (uint8_t v = 1; v <= 17; ++v) {
            eb.push(v);
        }
        eb.exchange(14, 16);
        eb.dup(15);
        append_return_top(eb);

        auto const out = expect_equal(assemble(eb));
        ASSERT_EQ(out.status, EVMC_SUCCESS);
        ASSERT_EQ(out.output.size(), 32u);
        EXPECT_EQ(out.output[31], 1);
    }

    TEST_F(Eip8024Test, DisallowedSingleImmediateHaltsAsInvalid)
    {
        std::vector<uint8_t> const c{DUPN, JUMPDEST};
        auto const out = expect_equal(c);
        EXPECT_EQ(out.status, EVMC_FAILURE);
    }

    TEST_F(Eip8024Test, DisallowedPairImmediateHaltsAsInvalid)
    {
        // 0x52 (MSTORE) is disallowed for EXCHANGE but not for DUPN/SWAPN.
        std::vector<uint8_t> const c{EXCHANGE, MSTORE};
        auto const out = expect_equal(c);
        EXPECT_EQ(out.status, EVMC_FAILURE);
    }

    TEST(Eip8024Disasm, DisallowedImmediateIsLabelledAndNotConsumed)
    {
        auto const shown = utils::show_opcodes({DUPN, JUMPDEST});
        EXPECT_NE(
            shown.find("// invalid DUPN immediate (0x5b)"), std::string::npos)
            << shown;
        EXPECT_NE(shown.find("JUMPDEST"), std::string::npos) << shown;

        auto const consumed =
            utils::show_opcodes({DUPN, eip8024_encode_single(17)});
        EXPECT_EQ(consumed.find("invalid DUPN immediate"), std::string::npos)
            << consumed;
        EXPECT_EQ(consumed.find("JUMPDEST"), std::string::npos) << consumed;
    }

    TEST(Eip8024Annot, StackEffectIsSimulated)
    {
        evm_as::mnemonic_config cfg{};
        cfg.annotate = true;

        {
            auto eb = evm_as::amsterdam();
            for (uint32_t v = 1; v <= 20; ++v) {
                eb.push(v);
            }
            eb.dupn(17).push(99).add();
            auto const out = evm_as::mcompile(eb, cfg);
            EXPECT_NE(out.find("(99 + 4)"), std::string::npos) << out;
            EXPECT_EQ(out.find("(99 + 20)"), std::string::npos) << out;
        }

        {
            auto eb = evm_as::amsterdam();
            for (uint32_t v = 1; v <= 20; ++v) {
                eb.push(v);
            }
            eb.swapn(17).push(99).add();
            auto const out = evm_as::mcompile(eb, cfg);
            EXPECT_NE(out.find("(99 + 3)"), std::string::npos) << out;
            EXPECT_EQ(out.find("(99 + 20)"), std::string::npos) << out;
        }

        {
            auto eb = evm_as::amsterdam();
            for (uint32_t v = 1; v <= 4; ++v) {
                eb.push(v);
            }
            eb.exchange(1, 2);
            auto const out = evm_as::mcompile(eb, cfg);
            EXPECT_NE(out.find("[4, 2, 3, 1]"), std::string::npos) << out;
        }
    }

    TEST_F(Eip8024Test, DisallowedImmediateOutranksInsufficientGas)
    {
        std::vector<uint8_t> const c{DUPN, JUMPDEST};
        auto const out = expect_equal(c, 2); // DUPN costs 3
        EXPECT_EQ(out.status, EVMC_FAILURE);
    }

    TEST_F(Eip8024Test, DisallowedImmediateByteIsAReachableJumpdestInCompiler)
    {
        std::vector<uint8_t> const c{PUSH1, 0x04, JUMP, DUPN, JUMPDEST, STOP};
        auto const out = expect_equal(c);
        EXPECT_EQ(out.status, EVMC_SUCCESS);
    }

    TEST_F(Eip8024Test, UnderflowHaltsInBothEngines)
    {
        auto eb = evm_as::amsterdam();
        eb.push(1).push(2).dupn(17);
        auto const out = expect_equal(assemble(eb));
        EXPECT_EQ(out.status, EVMC_FAILURE);
    }

    TEST_F(Eip8024Test, TruncatedImmediateHaltsWithoutOob)
    {
        // The missing immediate reads as 0, which decodes to n = 145.
        std::vector<uint8_t> const c{PUSH1, 0x01, DUPN};
        expect_both_fail(c);
    }

    TEST_F(Eip8024Test, OutOfGasBoundary)
    {
        auto eb = evm_as::amsterdam();
        for (uint8_t v = 1; v <= 20; ++v) {
            eb.push(v);
        }
        eb.dupn(17);
        append_return_top(eb);
        // 20 * PUSH1 (3 each) = 60 gas; give exactly that so DUPN OOGs.
        expect_both_fail(assemble(eb), 60);
    }

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
                eb.dup(n + 1);
                append_return_top(eb);
                auto const out = expect_equal(assemble(eb));
                ASSERT_EQ(out.status, EVMC_SUCCESS)
                    << "n=" << +n << " m=" << +m;
                ASSERT_EQ(out.output.size(), 32u) << "n=" << +n << " m=" << +m;
                EXPECT_EQ(out.output[31], 1) << "n=" << +n << " m=" << +m;
                ++count;
            }
        }
        EXPECT_GT(count, 0u);
    }

    TEST_F(Eip8024Test, DupnStackOverflowBoundary)
    {
        {
            auto eb = evm_as::amsterdam();
            for (uint32_t v = 1; v <= 1023; ++v) {
                eb.push(v);
            }
            eb.dupn(17).stop();
            auto const out = expect_equal(assemble(eb));
            EXPECT_EQ(out.status, EVMC_SUCCESS);
        }
        {
            auto eb = evm_as::amsterdam();
            for (uint32_t v = 1; v <= 1024; ++v) {
                eb.push(v);
            }
            eb.dupn(17).stop();
            auto const out = expect_equal(assemble(eb));
            EXPECT_EQ(out.status, EVMC_FAILURE);
        }
    }

    // The jump starts a new block, so the compiler must check and read the
    // operands from the runtime stack, unlike a straight-line test.
    std::vector<uint8_t> jumped_block(
        uint32_t const items, uint8_t const op, uint8_t const imm,
        std::vector<uint8_t> const &after = {})
    {
        std::vector<uint8_t> c;
        for (uint32_t v = 1; v <= items; ++v) {
            c.push_back(PUSH1);
            c.push_back(static_cast<uint8_t>(v));
        }
        auto const dest = static_cast<uint32_t>(c.size()) + 4;
        c.insert(
            c.end(),
            {PUSH2,
             static_cast<uint8_t>(dest >> 8),
             static_cast<uint8_t>(dest & 0xFF),
             JUMP,
             JUMPDEST,
             op,
             imm});
        c.insert(c.end(), after.begin(), after.end());
        c.insert(c.end(), {PUSH0, MSTORE, PUSH1, 32, PUSH0, RETURN});
        return c;
    }

    TEST_F(Eip8024Test, DeepDupnInJumpedToBlock)
    {
        auto const out =
            expect_equal(jumped_block(236, DUPN, eip8024_encode_single(235)));
        ASSERT_EQ(out.status, EVMC_SUCCESS);
        ASSERT_EQ(out.output.size(), 32u);
        EXPECT_EQ(out.output[31], 2);
    }

    TEST_F(Eip8024Test, DeepSwapnInJumpedToBlock)
    {
        auto const out =
            expect_equal(jumped_block(236, SWAPN, eip8024_encode_single(235)));
        ASSERT_EQ(out.status, EVMC_SUCCESS);
        ASSERT_EQ(out.output.size(), 32u);
        EXPECT_EQ(out.output[31], 1);
    }

    TEST_F(Eip8024Test, DeepExchangeInJumpedToBlock)
    {
        auto const out = expect_equal(
            jumped_block(30, EXCHANGE, eip8024_encode_pair(1, 29), {DUP2}));
        ASSERT_EQ(out.status, EVMC_SUCCESS);
        ASSERT_EQ(out.output.size(), 32u);
        EXPECT_EQ(out.output[31], 1);
    }

    TEST_F(Eip8024Test, DeepDupnInJumpedToBlockUnderflows)
    {
        expect_both_fail(jumped_block(100, DUPN, eip8024_encode_single(235)));
    }

    class Eip8024DormantTest
        : public test::VMTraitsTestBase<
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
        for (uint8_t op : {DUPN, SWAPN, EXCHANGE}) {
            std::vector<uint8_t> const c{PUSH1, 0x01, op, 0x00};
            EXPECT_NE(run(c, Interpreter), EVMC_SUCCESS) << "op=" << +op;
            EXPECT_NE(run(c, Compiler), EVMC_SUCCESS) << "op=" << +op;
        }
        EXPECT_TRUE(
            compiler::is_unknown_opcode_info<EvmTraits<MONAD_ETH_OSAKA>>(DUPN));
    }
}

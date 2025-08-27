// Copyright (C) 2025 Category Labs, Inc.
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

#include "asmjit/core/jitruntime.h"
#include "category/vm/compiler/ir/x86/types.hpp"
#include "category/vm/runtime//types.hpp"
#include "category/vm/runtime//uint256.hpp"
#include "category/vm/utils/evm-as/compiler.hpp"
#include "evmc/evmc.hpp"
#include <category/vm/compiler/ir/basic_blocks.hpp>
#include <category/vm/compiler/ir/x86.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/utils/evm-as.hpp>
#include <category/vm/utils/evm-as/builder.hpp>
#include <category/vm/utils/evm-as/instruction.hpp>
#include <category/vm/utils/evm-as/resolver.hpp>
#include <category/vm/utils/evm-as/validator.hpp>
#include <cstdlib>
#include <cstring>
#include <format>

#include <evmc/evmc.h>
#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <limits>
#include <memory>
#include <sstream>
#include <string>
#include <vector>

using namespace monad::vm;
using namespace monad::vm::runtime;
using namespace monad::vm::utils;

namespace
{
    std::shared_ptr<monad::vm::compiler::native::Nativecode>
    compile(asmjit::JitRuntime &rt, std::vector<uint8_t> const &bytecode)
    {
        using traits = EvmChain<EVMC_LATEST_STABLE_REVISION>;

        monad::vm::compiler::native::CompilerConfig const config{};
        auto const ir = monad::vm::compiler::basic_blocks::BasicBlocksIR(
            monad::vm::compiler::basic_blocks::unsafe_make_ir<traits>(
                bytecode));
        return monad::vm::compiler::native::compile_basic_blocks(
            traits::evm_rev(), rt, ir, config);
    }

    // NOTE/TODO: Copied verbatim from emitter_tests.cpp. Might be
    // useful to factor this code out into a common shared module.
    evmc::address max_address()
    {
        evmc::address ret;
        std::memset(ret.bytes, -1, sizeof(ret.bytes) / sizeof(*ret.bytes));
        return ret;
    }

    evmc::bytes32 max_bytes32()
    {
        evmc::bytes32 ret;
        std::memset(ret.bytes, -1, sizeof(ret.bytes) / sizeof(*ret.bytes));
        return ret;
    }

    runtime::Result test_result()
    {
        runtime::Result ret;
        ret.status = static_cast<runtime::StatusCode>(
            std::numeric_limits<uint64_t>::max());
        memcpy(ret.offset, max_bytes32().bytes, 32);
        memcpy(ret.size, max_bytes32().bytes, 32);
        return ret;
    }

    runtime::Context test_context(int64_t gas_remaining = 1'000'000)
    {
        return runtime::Context{
            .chain_params = {.max_initcode_size = 0xC000},
            .host = nullptr,
            .context = nullptr,
            .gas_remaining = gas_remaining,
            .gas_refund = 0,
            .env =
                {
                    .evmc_flags = 0,
                    .depth = 0,
                    .recipient = max_address(),
                    .sender = max_address(),
                    .value = max_bytes32(),
                    .create2_salt = max_bytes32(),
                    .input_data = {},
                    .code = {},
                    .return_data = {},
                    .input_data_size = 0,
                    .code_size = 0,
                    .return_data_size = 0,
                    .tx_context = {},
                },
            .result = test_result(),
            .memory = monad::vm::runtime::Memory(runtime::EvmMemoryAllocator{}),
            .exit_stack_ptr = nullptr};
    }

    struct TestStackMemoryDeleter
    {
        void operator()(uint8_t *p) const
        {
            std::free(p);
        }
    } test_stack_memory_deleter;

    std::unique_ptr<uint8_t, TestStackMemoryDeleter> test_stack_memory()
    {
        return {
            reinterpret_cast<uint8_t *>(std::aligned_alloc(32, 32 * 1024)),
            test_stack_memory_deleter};
    }

    struct jit
    {
        static runtime::uint256_t
        run(evm_as::EvmBuilder<EvmChain<EVMC_LATEST_STABLE_REVISION>> const &eb)
        {
            std::vector<uint8_t> bytecode{};
            evm_as::compile(eb, bytecode);

            asmjit::JitRuntime rt{};
            auto native = compile(rt, bytecode);

            [&]() { ASSERT_TRUE(native != nullptr); }();

            auto entry = native->entrypoint();

            [&]() { ASSERT_TRUE(entry != nullptr); }();

            auto ctx = test_context();
            auto const &ret = ctx.result;

            auto stack_memory = test_stack_memory();
            entry(&ctx, stack_memory.get());
            [&]() { ASSERT_EQ(ret.status, runtime::StatusCode::Success); }();

            // TODO: artificial restriction on result offset and size.
            return runtime::uint256_t::load_be_unsafe(ctx.memory.data);
        }
    };
}

TEST(EvmAs, PushExpansion)
{
    using namespace monad::vm::utils::evm_as;
    auto eb = evm_as::latest();
    // Unsigned push expansion
    auto const check = [](auto const &eb) -> void {
        std::vector<compiler::EvmOpCode> matchers = {
            compiler::EvmOpCode::PUSH0,  compiler::EvmOpCode::PUSH1,
            compiler::EvmOpCode::PUSH2,  compiler::EvmOpCode::PUSH3,
            compiler::EvmOpCode::PUSH4,  compiler::EvmOpCode::PUSH5,
            compiler::EvmOpCode::PUSH6,  compiler::EvmOpCode::PUSH7,
            compiler::EvmOpCode::PUSH8,  compiler::EvmOpCode::PUSH9,
            compiler::EvmOpCode::PUSH10, compiler::EvmOpCode::PUSH11,
            compiler::EvmOpCode::PUSH12, compiler::EvmOpCode::PUSH13,
            compiler::EvmOpCode::PUSH14, compiler::EvmOpCode::PUSH15,
            compiler::EvmOpCode::PUSH16, compiler::EvmOpCode::PUSH17,
            compiler::EvmOpCode::PUSH18, compiler::EvmOpCode::PUSH19,
            compiler::EvmOpCode::PUSH20, compiler::EvmOpCode::PUSH21,
            compiler::EvmOpCode::PUSH22, compiler::EvmOpCode::PUSH23,
            compiler::EvmOpCode::PUSH24, compiler::EvmOpCode::PUSH25,
            compiler::EvmOpCode::PUSH26, compiler::EvmOpCode::PUSH27,
            compiler::EvmOpCode::PUSH28, compiler::EvmOpCode::PUSH29,
            compiler::EvmOpCode::PUSH30, compiler::EvmOpCode::PUSH31,
            compiler::EvmOpCode::PUSH32,
        };
        ASSERT_EQ(eb.size(), matchers.size());

        ASSERT_TRUE(Instruction::is_plain(eb[0]));
        ASSERT_EQ(Instruction::as_plain(eb[0]).opcode, matchers[0]);
        for (size_t i = 1; i < eb.size(); i++) {
            ASSERT_TRUE(Instruction::is_push(eb[i]));
            ASSERT_EQ(Instruction::as_push(eb[i]).opcode, matchers[i]);
        }
    };

    eb.push(0);
    for (int nbytes = 1; nbytes < 8; nbytes++) {
        uint64_t const value = (1ULL << (8 * nbytes)) - 1;
        eb.push(value);
    }
    eb.push(std::numeric_limits<uint64_t>::max());
    for (int nbytes = 9; nbytes < 32; nbytes++) {
        runtime::uint256_t const value = (uint256_t{1} << (8 * nbytes)) - 1;
        eb.push(value);
    }
    eb.push(std::numeric_limits<uint256_t>::max());
    ASSERT_TRUE(evm_as::validate(eb));
    check(eb);

    // Signed push expansion
    eb = evm_as::latest();
    eb.spush(-1).spush(-1'000'000);
    ASSERT_EQ(eb.size(), 2);
    ASSERT_TRUE(Instruction::is_push(eb[0]));
    ASSERT_TRUE(Instruction::is_push(eb[1]));
    auto const push1 = Instruction::as_push(eb[0]);
    ASSERT_EQ(push1.imm, std::numeric_limits<uint256_t>::max());

    auto i = push1.imm;
    int j = 0;
    while (i != 0) {
        i = i + 1;
        j++;
    }
    ASSERT_EQ(j, 1);

    auto const push2 = Instruction::as_push(eb[1]);
    ASSERT_EQ(push2.imm, monad::vm::runtime::signextend(7, -1'000'000));

    i = push2.imm;
    j = 0;
    while (i != 0) {
        i = i + 1;
        j++;
    }
    ASSERT_EQ(j, 1'000'000);
    ASSERT_TRUE(evm_as::validate(eb));
}

TEST(EvmAs, SwapExpansion)
{
    auto eb = evm_as::latest();

    eb.push(1).push(2).push(3).swap(2);
    ASSERT_TRUE(evm_as::validate(eb));
    ASSERT_TRUE(evm_as::Instruction::is_plain(eb[3]));
    ASSERT_EQ(
        evm_as::Instruction::as_plain(eb[3]).opcode,
        compiler::EvmOpCode::SWAP2);

    eb = evm_as::latest();
    std::vector<compiler::EvmOpCode> swaps = {
        compiler::EvmOpCode::SWAP1,
        compiler::EvmOpCode::SWAP2,
        compiler::EvmOpCode::SWAP3,
        compiler::EvmOpCode::SWAP4,
        compiler::EvmOpCode::SWAP5,
        compiler::EvmOpCode::SWAP6,
        compiler::EvmOpCode::SWAP7,
        compiler::EvmOpCode::SWAP8,
        compiler::EvmOpCode::SWAP9,
        compiler::EvmOpCode::SWAP10,
        compiler::EvmOpCode::SWAP11,
        compiler::EvmOpCode::SWAP12,
        compiler::EvmOpCode::SWAP13,
        compiler::EvmOpCode::SWAP14,
        compiler::EvmOpCode::SWAP15,
        compiler::EvmOpCode::SWAP16};
    for (size_t i = 1; i <= 16; i++) {
        eb.swap(i);
    }
    ASSERT_EQ(eb.size(), swaps.size());
    for (size_t i = 0; i < eb.size(); i++) {
        ASSERT_TRUE(evm_as::Instruction::is_plain(eb[i]));
        ASSERT_EQ(evm_as::Instruction::as_plain(eb[i]).opcode, swaps[i]);
    }
    ASSERT_FALSE(evm_as::validate(eb));

    eb = evm_as::latest();
    eb.swap(100);
    ASSERT_EQ(eb.size(), 1);
    ASSERT_TRUE(evm_as::Instruction::is_invalid(eb[0]));
    ASSERT_TRUE(evm_as::Instruction::as_invalid(eb[0]).has_name());
    ASSERT_EQ(evm_as::Instruction::as_invalid(eb[0]).name, "SWAP100");
}

TEST(EvmAs, DupExpansion)
{
    auto eb = evm_as::latest();

    eb.push(1).push(2).push(3).dup(2);
    ASSERT_TRUE(evm_as::validate(eb));
    ASSERT_TRUE(evm_as::Instruction::is_plain(eb[3]));
    ASSERT_EQ(
        evm_as::Instruction::as_plain(eb[3]).opcode, compiler::EvmOpCode::DUP2);

    eb = evm_as::latest();
    std::vector<compiler::EvmOpCode> dups = {
        compiler::EvmOpCode::DUP1,
        compiler::EvmOpCode::DUP2,
        compiler::EvmOpCode::DUP3,
        compiler::EvmOpCode::DUP4,
        compiler::EvmOpCode::DUP5,
        compiler::EvmOpCode::DUP6,
        compiler::EvmOpCode::DUP7,
        compiler::EvmOpCode::DUP8,
        compiler::EvmOpCode::DUP9,
        compiler::EvmOpCode::DUP10,
        compiler::EvmOpCode::DUP11,
        compiler::EvmOpCode::DUP12,
        compiler::EvmOpCode::DUP13,
        compiler::EvmOpCode::DUP14,
        compiler::EvmOpCode::DUP15,
        compiler::EvmOpCode::DUP16};
    for (size_t i = 1; i <= 16; i++) {
        eb.dup(i);
    }
    ASSERT_EQ(eb.size(), dups.size());
    for (size_t i = 0; i < eb.size(); i++) {
        ASSERT_TRUE(evm_as::Instruction::is_plain(eb[i]));
        ASSERT_EQ(evm_as::Instruction::as_plain(eb[i]).opcode, dups[i]);
    }

    eb = evm_as::latest();
    eb.dup(17);
    ASSERT_EQ(eb.size(), 1);
    ASSERT_TRUE(evm_as::Instruction::is_invalid(eb[0]));
    ASSERT_TRUE(evm_as::Instruction::as_invalid(eb[0]).has_name());
    ASSERT_EQ(evm_as::Instruction::as_invalid(eb[0]).name, "DUP17");
}

TEST(EvmAs, InvalidPush)
{
    auto eb = evm_as::latest();

    uint8_t i = 32;
    do {
        eb.push(++i, 123);
    }
    while (i < std::numeric_limits<uint8_t>::max());

    std::vector<evm_as::ValidationError> errors{};
    ASSERT_FALSE(evm_as::validate(eb, errors));
    ASSERT_EQ(errors.size(), 223);

    ASSERT_EQ(eb.size(), 223);
    for (auto const &ins : eb) {
        ASSERT_TRUE(evm_as::Instruction::is_invalid(ins));
    }
}

TEST(EvmAs, PushLabels)
{
    using namespace monad::vm::utils::evm_as;
    auto eb = evm_as::latest();

    eb.push(".FOO").push("bar").push("");
    ASSERT_EQ(eb.size(), 3);

    ASSERT_TRUE(Instruction::is_push_label(eb[0]));
    ASSERT_EQ(Instruction::as_push_label(eb[0]).label, ".FOO");

    ASSERT_TRUE(Instruction::is_push_label(eb[1]));
    ASSERT_EQ(Instruction::as_push_label(eb[1]).label, "bar");

    ASSERT_TRUE(Instruction::is_push_label(eb[2]));
    ASSERT_EQ(Instruction::as_push_label(eb[2]).label, "");

    std::vector<evm_as::ValidationError> errors{};
    ASSERT_FALSE(evm_as::validate(eb, errors));
    ASSERT_EQ(errors.size(), 4);
    ASSERT_EQ(errors[0].offset, 2);
    ASSERT_EQ(errors[0].msg, "Empty label");
    for (size_t i = 1; i < errors.size(); i++) {
        ASSERT_TRUE(errors[i].msg.rfind("Undefined label", 0) == 0);
    }
}

TEST(EvmAs, DuplicatedLabels)
{
    auto eb = evm_as::latest();

    eb.jumpdest(".FOO").jumpdest(".BAR").jumpdest(".FOO");
    std::vector<evm_as::ValidationError> errors{};
    ASSERT_FALSE(evm_as::validate(eb, errors));
    ASSERT_EQ(errors.size(), 1);

    ASSERT_EQ(errors[0].offset, 2);
    ASSERT_TRUE(errors[0].msg.rfind("Multiply defined label", 0) == 0);
}

TEST(EvmAs, LabelResolution)
{
    using namespace monad::vm::utils::evm_as;
    auto eb = evm_as::latest();

    eb.jumpdest(".FOO").jump(".FOO");
    ASSERT_EQ(eb.size(), 3);
    ASSERT_TRUE(Instruction::is_jumpdest(eb[0]));
    ASSERT_TRUE(Instruction::is_push_label(eb[1]));
    ASSERT_TRUE(Instruction::is_plain(eb[2]));
    ASSERT_EQ(Instruction::as_plain(eb[2]).opcode, compiler::EvmOpCode::JUMP);
    ASSERT_TRUE(evm_as::validate(eb));
    auto const label_offsets = resolve_labels(eb);
    auto const &it = label_offsets.find(".FOO");
    ASSERT_TRUE(it != label_offsets.end());
    ASSERT_EQ(it->second, 0);
}

TEST(EvmAs, LabelResolution2)
{
    using namespace monad::vm::utils::evm_as;
    auto eb = evm_as::latest();

    eb.jump(".END");
    for (size_t i = 0; i < 256; i++) {
        eb.push0();
    }
    eb.jumpdest(".END");
    ASSERT_EQ(eb.size(), 259);
    ASSERT_TRUE(Instruction::is_push_label(eb[0]));
    auto const label_offsets = resolve_labels(eb);
    auto const &it = label_offsets.find(".END");
    ASSERT_TRUE(it != label_offsets.end());
    ASSERT_EQ(it->second, 260);
    ASSERT_TRUE(evm_as::validate(eb));
}

TEST(EvmAs, UndefinedLabels)
{
    auto eb = evm_as::latest();

    eb.jump("END");
    std::vector<evm_as::ValidationError> errors{};
    ASSERT_FALSE(evm_as::validate(eb, errors));
    ASSERT_EQ(errors.size(), 1);
    ASSERT_EQ(errors[0].msg, "Undefined label 'END'");
}

TEST(EvmAs, ComposeIdentity)
{
    auto eb1 = evm_as::latest();
    auto empty = evm_as::latest();

    eb1.push0();

    auto eb2 = eb1.compose(empty);
    ASSERT_EQ(empty.size(), 0);
    ASSERT_EQ(eb1.size(), eb2.size());
    eb2.push0();
    ASSERT_EQ(eb1.size() + 1, eb2.size());

    eb2 = empty.compose(eb1);
    ASSERT_EQ(empty.size(), 0);
    ASSERT_EQ(eb1.size(), eb2.size());
    eb2.push0();
    ASSERT_EQ(eb1.size() + 1, eb2.size());
}

TEST(EvmAs, Compose1)
{
    auto const check = [](size_t offset, size_t expected_size) -> auto {
        return [=](auto const &eb) -> void {
            using namespace monad::vm::utils::evm_as;
            ASSERT_EQ(eb.size(), expected_size);
            for (size_t i = 0; i < eb.size(); i++) {
                ASSERT_TRUE(Instruction::is_push(eb[i]));
                ASSERT_EQ(
                    Instruction::as_push(eb[i]).imm, uint256_t{i + 1 + offset});
            }
        };
    };

    auto eb1 = evm_as::latest();
    auto eb2 = evm_as::latest();

    eb1.push(1).push(2);
    ASSERT_TRUE(evm_as::validate(eb1));

    eb2.push(3).push(4);
    ASSERT_TRUE(evm_as::validate(eb2));

    auto eb3 = eb1.compose(eb2);
    ASSERT_TRUE(evm_as::validate(eb3));

    check(0, 2)(eb1);
    check(2, 2)(eb2);
    check(0, 4)(eb3);

    ASSERT_TRUE(evm_as::validate(eb1));
    ASSERT_TRUE(evm_as::validate(eb2));
    ASSERT_TRUE(evm_as::validate(eb3));
}

TEST(EvmAs, Compose2)
{

    auto eb1 = evm_as::latest();
    auto eb2 = evm_as::latest();

    eb1.jump(".END");
    ASSERT_FALSE(evm_as::validate(eb1));

    eb2.jumpdest(".END");
    ASSERT_TRUE(evm_as::validate(eb2));

    auto eb3 = eb1.compose(eb2);
    ASSERT_FALSE(evm_as::validate(eb1));
    ASSERT_TRUE(evm_as::validate(eb2));
    ASSERT_TRUE(evm_as::validate(eb3));
}

TEST(EvmAs, Append1)
{

    auto eb1 = evm_as::latest();
    auto eb2 = evm_as::latest();

    eb1.jump(".END");
    ASSERT_FALSE(evm_as::validate(eb1));

    eb2.jumpdest(".END");
    ASSERT_TRUE(evm_as::validate(eb2));

    eb1.append(eb2);
    ASSERT_TRUE(evm_as::validate(eb1));
    ASSERT_TRUE(evm_as::validate(eb2));
}

TEST(EvmAs, BytecodeCompile1)
{
    auto eb = evm_as::latest();

    std::vector<uint8_t> expected{
        compiler::EvmOpCode::PUSH32,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF,
        0xFF};
    ASSERT_TRUE(evm_as::validate(eb.spush(-1)));
    std::vector<uint8_t> bytecode{};
    evm_as::compile(eb, bytecode);
    ASSERT_EQ(bytecode.size(), expected.size());
    for (size_t i = 0; i < bytecode.size(); i++) {
        ASSERT_EQ(bytecode[i], expected[i]);
    }

    expected = {
        compiler::EvmOpCode::PUSH32,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x02,
        0x4C,
        0xB0,
        0x16,
        0xEA};

    eb = evm_as::latest();
    ASSERT_TRUE(evm_as::validate(eb.push(32, 9876543210)));
    bytecode.clear();
    evm_as::compile(eb, bytecode);
    ASSERT_EQ(bytecode.size(), expected.size());
    for (size_t i = 0; i < bytecode.size(); i++) {
        ASSERT_EQ(bytecode[i], expected[i]);
    }

    expected = {compiler::EvmOpCode::PUSH5, 0x02, 0x4C, 0xB0, 0x16, 0xEA};

    eb = evm_as::latest();
    ASSERT_TRUE(evm_as::validate(eb.push(9876543210)));
    bytecode.clear();
    evm_as::compile(eb, bytecode);
    ASSERT_EQ(bytecode.size(), expected.size());
    for (size_t i = 0; i < bytecode.size(); i++) {
        ASSERT_EQ(bytecode[i], expected[i]);
    }
}

TEST(EvmAs, BytecodeCompile2)
{
    auto eb = evm_as::latest();

    std::vector<uint8_t> expected = {
        compiler::EvmOpCode::PUSH2, 0x01, 0x04, compiler::EvmOpCode::JUMP};
    for (size_t i = 0; i < 256; i++) {
        expected.push_back(compiler::EvmOpCode::PUSH0);
    }
    expected.push_back(compiler::EvmOpCode::JUMPDEST);
    ASSERT_EQ(expected.size(), 261);

    eb.jump(".END");
    for (size_t i = 0; i < 256; i++) {
        eb.push0();
    }
    eb.jumpdest(".END");
    ASSERT_EQ(eb.size(), 259);
    ASSERT_TRUE(evm_as::validate(eb));
    std::vector<uint8_t> bytecode{};
    evm_as::compile(eb, bytecode);
    ASSERT_EQ(bytecode.size(), expected.size());
    for (size_t i = 0; i < bytecode.size(); i++) {
        ASSERT_EQ(bytecode[i], expected[i]);
    }
}

TEST(EvmAs, BytecodeCompile3)
{
    auto eb = evm_as::latest();

    std::vector<uint8_t> expected = {compiler::EvmOpCode::JUMPDEST};
    for (size_t i = 0; i < 300; i++) {
        expected.push_back(compiler::EvmOpCode::PUSH0);
    }
    expected.push_back(compiler::EvmOpCode::PUSH0);
    expected.push_back(compiler::EvmOpCode::JUMP);
    ASSERT_EQ(expected.size(), 303);

    eb.jumpdest(".END");
    for (size_t i = 0; i < 300; i++) {
        eb.push0();
    }
    eb.jump(".END");
    ASSERT_EQ(eb.size(), 303);
    ASSERT_TRUE(evm_as::validate(eb));
    std::vector<uint8_t> bytecode{};
    evm_as::compile(eb, bytecode);
    ASSERT_EQ(bytecode.size(), expected.size());
    for (size_t i = 0; i < bytecode.size(); i++) {
        ASSERT_EQ(bytecode[i], expected[i]);
    }
}

TEST(EvmAs, BytecodeCompile4)
{
    auto eb = evm_as::latest();

    std::string expected = "\x5F\x5F\x01";
    ASSERT_EQ(expected.size(), 3);

    eb.push0().push0().add();
    ASSERT_EQ(eb.size(), 3);
    ASSERT_TRUE(evm_as::validate(eb));

    std::string bytecode = evm_as::compile(eb);
    ASSERT_EQ(bytecode.size(), expected.size());
    for (size_t i = 0; i < bytecode.size(); i++) {
        ASSERT_EQ(bytecode[i], expected[i]);
    }
}

TEST(EvmAs, Execution1)
{
    auto eb = evm_as::latest();
    uint256_t const expected = 0x42;

    // The default program on evm.codes/playground (as of May 2025).
    eb.push(1, 0x42).push(1, 0).mstore().push(1, 0x20).push(1, 0).return_();

    ASSERT_TRUE(evm_as::validate(eb));

    uint256_t const result = jit::run(eb);
    ASSERT_EQ(result, expected);
}

TEST(EvmAs, Execution2)
{
    auto eb = evm_as::latest();
    uint256_t const expected = 0x0A;

    eb.spush(-10) // [-10]
        .push0() // [0 -10]
        .jumpdest(".r") // [0 -10]
        .push(1) // [1 0 -10]
        .add() // [(1 + 0) -10]
        .swap1() // [-10 (1 + 0)]
        .push(1) // [1 -10 (1 + 0)]
        .add() // [9 (1 + 0)]
        .dup1() // [9 9 (1 + 0)]
        .swap2() // [(1 + 0) 9 9]
        .swap1() // [9 (1 + 0) 9]
        .jumpi(".r") // [.r 9 (1 + 0) 9]
        .push0() // [0 (1 + 0) 0]
        .mstore() // [0]
        .push(32) // [32 0]
        .push0() // [0 32 0]
        .return_(); // [0]

    ASSERT_TRUE(evm_as::validate(eb));

    uint256_t const result = jit::run(eb);
    ASSERT_EQ(result, expected);
}

TEST(EvmAs, Execution3)
{
    auto eb = evm_as::latest();
    uint256_t const expected = 0xC0FFEEC0FFEE;

    eb.jump("END").push(0xBADBADBADBAD).push0().mstore();

    for (uint32_t i = 0; i < std::numeric_limits<uint16_t>::max(); i++) {
        eb.push0().pop();
    }

    eb.push(32)
        .push0()
        .return_()
        .jumpdest("END")
        .push(expected)
        .push0()
        .mstore()
        .push(32)
        .push0()
        .return_();

    ASSERT_TRUE(evm_as::validate(eb));

    uint256_t const result = jit::run(eb);
    ASSERT_EQ(result, expected);
}

TEST(EvmAs, Execution4)
{
    auto eb = evm_as::latest();
    uint256_t const expected = 0xABBA;

    eb.push0() // dummy value
        .jump("START")
        .jumpdest("END")
        .push(1)
        .add()
        .push0()
        .mstore()
        .push(32)
        .push(0)
        .return_();

    for (uint32_t i = 0; i < std::numeric_limits<uint16_t>::max(); i++) {
        eb.push0().pop();
    }

    eb.jumpdest("START").push(0xABB9).jump("END").stop();

    ASSERT_TRUE(evm_as::validate(eb));

    uint256_t const result = jit::run(eb);
    ASSERT_EQ(result, expected);
}

TEST(EvmAs, MnemonicCompile1)
{
    auto eb = evm_as::latest();

    std::string const expected =
        "// Add 1 + 511.\nPUSH1 0x1\nPUSH2 0x1FF\nADD\n";

    eb.comment("Add 1 + 511.").push(1).push(511).add();
    ASSERT_TRUE(evm_as::validate(eb));
    ASSERT_EQ(evm_as::mcompile(eb), expected);
}

TEST(EvmAs, MnemonicCompile2)
{
    auto eb = evm_as::latest();

    std::string const expected =
        "// Add 1 + 511.\n// Another comment.\n// Yet "
        "another comment.\nPUSH1 0x1\nPUSH2 0x1FF\nADD\n";

    eb.comment("Add 1 + 511.\nAnother comment.\nYet another comment.")
        .push(1)
        .push(511)
        .add();
    ASSERT_TRUE(evm_as::validate(eb));
    ASSERT_EQ(evm_as::mcompile(eb), expected);
}

TEST(EvmAs, MnemonicCompile3)
{
    auto eb = evm_as::latest();

    std::string expected =
        "// Infinite loop\nJUMPDEST .LOOP\nPUSH .LOOP\nJUMP\n";

    eb.comment("Infinite loop").jumpdest(".LOOP").jump(".LOOP");
    ASSERT_TRUE(evm_as::validate(eb));
    ASSERT_EQ(evm_as::mcompile(eb), expected);

    expected = "// Infinite loop (unlabelled)\nJUMPDEST\nPUSH0\nJUMP\n";

    eb = evm_as::latest();
    eb.comment("Infinite loop (unlabelled)").jumpdest().push0().jump();
    ASSERT_TRUE(evm_as::validate(eb));
    ASSERT_EQ(evm_as::mcompile(eb), expected);
}

TEST(EvmAs, EmptyComment)
{
    auto eb = evm_as::latest();

    ASSERT_TRUE(evm_as::validate(eb));
    ASSERT_EQ(evm_as::mcompile(eb), "");

    eb.comment("");
    ASSERT_TRUE(evm_as::validate(eb));
    ASSERT_EQ(evm_as::mcompile(eb), "//\n");
}

TEST(EvmAs, StackUnderflow)
{
    auto eb = evm_as::latest();

    std::vector<evm_as::ValidationError> errors{};
    ASSERT_FALSE(evm_as::validate(eb.add(), errors));
    ASSERT_EQ(errors.size(), 1);
    ASSERT_EQ(errors[0].msg, "Stack underflow");
}

TEST(EvmAs, StackOverflow)
{
    auto eb = evm_as::latest();

    for (size_t i = 0; i < 1025; i++) {
        eb.push0();
    }

    std::vector<evm_as::ValidationError> errors{};
    ASSERT_FALSE(evm_as::validate(eb, errors));
    ASSERT_EQ(errors.size(), 1);
    ASSERT_EQ(errors[0].msg, "Stack overflow");
}

TEST(EvmAs, StackOk)
{
    auto eb = evm_as::latest();

    for (size_t i = 0; i < 1025; i++) {
        eb.push0().pop();
    }

    ASSERT_TRUE(evm_as::validate(eb));
}

TEST(EvmAs, lookup)
{
    auto eb = evm_as::latest();
    auto const info = evm_as::latest().lookup(compiler::EvmOpCode::ADD);
    ASSERT_EQ(info.name, "ADD");
}

TEST(EvmAs, Legacy)
{
    auto eb = evm_as::frontier();
    std::vector<evm_as::ValidationError> errors{};
    eb.push0();
    ASSERT_FALSE(evm_as::validate(eb, errors));
    ASSERT_EQ(errors.size(), 1);
    ASSERT_EQ(errors[0].msg, "Invalid instruction '0x5F'");

    eb = evm_as::frontier();
    eb.push(0);
    ASSERT_TRUE(evm_as::validate(eb));

    auto eb2 = evm_as::shanghai();
    eb2.push0();
    ASSERT_TRUE(evm_as::validate(eb2));

    eb2 = evm_as::shanghai();
    eb2.push(0);
    ASSERT_TRUE(evm_as::validate(eb2));
    ASSERT_EQ(eb2.size(), 1);
    ASSERT_TRUE(evm_as::Instruction::is_plain(eb2[0]));
    ASSERT_EQ(
        evm_as::Instruction::as_plain(eb2[0]).opcode,
        compiler::EvmOpCode::PUSH0);
}

TEST(EvmAs, ValidationSlack)
{
    // This test illustrates some of the slack of the simple validator.
    auto eb = evm_as::latest();

    eb.jump("setup")
        .jumpdest("main")
        .pop()
        .stop()
        .jumpdest("setup")
        .push0()
        .jump("main");

    std::vector<evm_as::ValidationError> errors{};
    ASSERT_FALSE(evm_as::validate(eb, errors));
    ASSERT_EQ(errors.size(), 1);
    ASSERT_EQ(errors[0].msg, "Stack underflow");
    ASSERT_EQ(errors[0].offset, 3);
}

static evm_as::mnemonic_config mconfig{false, true, 12};

TEST(EvmAs, Annotation1)
{
    auto eb = evm_as::latest();

    std::string const expected = "PUSH1 0x1   // [1]\n"
                                 "PUSH1 0x3F  // [63, 1]\n"
                                 "ADD         // [(63 + 1)]\n";

    eb.push(1).push(63).add();
    ASSERT_EQ(evm_as::mcompile(eb, mconfig), expected);
}

TEST(EvmAs, Annotation2)
{
    auto eb = evm_as::latest();

    uint32_t u32max = std::numeric_limits<uint32_t>::max();

    std::string expected = std::format(
        "PUSH4 0x{:X} // [{}]\n"
        "PUSH1 0x1   // [1, {}]\n"
        "ADD         // [(1 + 4294967295)]\n",
        u32max,
        u32max,
        u32max);

    eb.push(u32max).push(1).add();
    ASSERT_EQ(evm_as::mcompile(eb, mconfig), expected);

    // "Large" inputs get named.
    expected = std::format(
        "PUSH5 0x{:X} // [X0]\n"
        "PUSH1 0x1   // [1, X0]\n"
        "ADD         // [(1 + X0)]\n",
        static_cast<uint64_t>(u32max) + 1);

    eb = evm_as::latest();
    eb.push(static_cast<uint64_t>(u32max) + 1).push(1).add();
    ASSERT_EQ(evm_as::mcompile(eb, mconfig), expected);
}

TEST(EvmAs, Annotation3)
{
    auto eb = evm_as::latest();

    std::string const expected = "PUSH0       // [0]\n"
                                 "PUSH1 0x1   // [1, 0]\n"
                                 "PUSH1 0x2   // [2, 1, 0]\n"
                                 "PUSH1 0x3   // [3, 2, 1, 0]\n"
                                 "PUSH1 0x4   // [4, 3, 2, 1, 0]\n"
                                 "PUSH1 0x5   // [5, 4, 3, 2, 1, 0]\n"
                                 "PUSH1 0x6   // [6, 5, 4, 3, 2, 1, 0]\n"
                                 "PUSH1 0x7   // [7, 6, 5, 4, 3, 2, 1, 0]\n"
                                 "PUSH1 0x8   // [8, 7, 6, 5, 4, 3, ..., 0]\n";

    eb.push0().push(1).push(2).push(3).push(4).push(5).push(6).push(7).push(8);
    ASSERT_EQ(evm_as::mcompile(eb, mconfig), expected);
}

TEST(EvmAs, Annotation4)
{
    auto eb = evm_as::latest();

    size_t large =
        static_cast<size_t>(std::numeric_limits<uint32_t>::max()) + 1;

    std::string const expected = std::format(
        "PUSH5 0x{:X} // [X0]\n"
        "PUSH5 0x{:X} // [Y0, X0]\n"
        "PUSH5 0x{:X} // [Z0, Y0, X0]\n"
        "PUSH5 0x{:X} // [A0, Z0, Y0, X0]\n"
        "PUSH5 0x{:X} // [B0, A0, Z0, Y0, X0]\n"
        "PUSH5 0x{:X} // [C0, B0, A0, Z0, Y0, X0]\n"
        "PUSH5 0x{:X} // [X1, C0, B0, A0, Z0, Y0, X0]\n",
        large,
        large,
        large,
        large,
        large,
        large,
        large);

    for (size_t i = 0; i < 7; i++) {
        eb.push(large);
    }
    ASSERT_EQ(evm_as::mcompile(eb, mconfig), expected);
}

TEST(EvmAs, Annotation5)
{
    auto eb = evm_as::latest();

    size_t large =
        static_cast<size_t>(std::numeric_limits<uint32_t>::max()) + 1;

    std::string const expected_last_line = std::format(
        "PUSH5 0x{:X} // [X100, C99, B99, A99, Z99, Y99, ..., X0]", large);

    for (size_t i = 0; i < 601; i++) {
        eb.push(large);
    }

    std::stringstream output(evm_as::mcompile(eb, mconfig));
    std::string line;
    std::vector<std::string> lines;

    while (std::getline(output, line, '\n')) {
        lines.push_back(line);
    }
    ASSERT_TRUE(lines.size() > 0);
    ASSERT_EQ(lines[lines.size() - 1], expected_last_line);
}

TEST(EvmAs, Annotation6)
{
    auto eb = evm_as::latest();

    std::string expected = std::format(
        "PUSH1 0x{:X}  // [123]\n"
        "DUP1        // [123, 123]\n",
        123);

    eb.push(123).dup1();
    ASSERT_EQ(evm_as::mcompile(eb, mconfig), expected);

    expected = std::format(
        "PUSH1 0x{:X}   // [1]\n"
        "PUSH1 0x{:X}   // [2, 1]\n"
        "PUSH1 0x{:X}   // [3, 2, 1]\n"
        "DUP3        // [1, 3, 2, 1]\n",
        1,
        2,
        3);
    eb = evm_as::latest();
    eb.push(1).push(2).push(3).dup3();
    ASSERT_EQ(evm_as::mcompile(eb, mconfig), expected);
}

TEST(EvmAs, Annotation7)
{
    auto eb = evm_as::latest();

    std::string expected = std::format(
        "PUSH1 0x{:X}   // [1]\n"
        "PUSH1 0x{:X}   // [2, 1]\n"
        "SWAP1       // [1, 2]\n",
        1,
        2);

    eb.push(1).push(2).swap1();
    ASSERT_EQ(evm_as::mcompile(eb, mconfig), expected);

    expected = std::format(
        "PUSH1 0x{:X}   // [1]\n"
        "PUSH1 0x{:X}   // [2, 1]\n"
        "PUSH1 0x{:X}   // [3, 2, 1]\n"
        "SWAP2       // [1, 2, 3]\n",
        1,
        2,
        3);
    eb = evm_as::latest();
    eb.push(1).push(2).push(3).swap2();
    ASSERT_EQ(evm_as::mcompile(eb, mconfig), expected);
}

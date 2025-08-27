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

#include <category/vm/compiler/ir/basic_blocks.hpp>
#include <category/vm/compiler/ir/x86/emitter.hpp>
#include <category/vm/compiler/ir/x86/types.hpp>
#include <category/vm/compiler/ir/x86/virtual_stack.hpp>
#include <category/vm/compiler/types.hpp>
#include <category/vm/evm/chain.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/runtime/allocator.hpp>
#include <category/vm/runtime/math.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/runtime/uint256.hpp>

#include "test_params.hpp"

#include <asmjit/core/globals.h>
#include <asmjit/core/jitruntime.h>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <limits>
#include <memory>
#include <tuple>
#include <utility>
#include <vector>

namespace runtime = monad::vm::runtime;
using namespace monad::vm;
using namespace monad::vm::compiler;
using namespace monad::vm::compiler::native;
using namespace monad::vm::interpreter;
using namespace monad::vm::runtime;

namespace
{
    static int test_emitter_ix = 0;

    std::string new_emitter_asm_log_path()
    {
        test_emitter_ix++;
        return std::string(std::format(
            "/tmp/monad_vm_test_logs/emitter_test_{}.s", test_emitter_ix));
    }

    struct TestEmitter : Emitter
    {

        std::string log_path_storage_;

        CompilerConfig add_asm_log_path(CompilerConfig c, std::string log_path)
        {
            if (!c.asm_log_path &&
                monad::vm::compiler::test::params.dump_asm_on_failure) {
                c.asm_log_path = log_path.c_str();
            }
            return c;
        }

        // Default log path, used if c.asm_log_path is not set. The only reason
        // to have this constructor is so that the lifetime of the
        // new_emitter_asm_log_path extends to after the Emitter constructor.
        TestEmitter(
            asmjit::JitRuntime const &rt, code_size_t bytecode_size,
            CompilerConfig const &c = {},
            std::string const &log_path = new_emitter_asm_log_path())
            : Emitter(rt, bytecode_size, add_asm_log_path(c, log_path))
            , log_path_storage_(log_path)
        {
        }

        // Override finish_contract to flush debug_logger_'s file handle
        entrypoint_t finish_contract(asmjit::JitRuntime &rt)
        {
            auto entrypoint = Emitter::finish_contract(rt);

            // Flush the debug logger in case the code segfaults before the
            // Emitter destructor is called.
            flush_debug_logger();
            if (monad::vm::compiler::test::params.dump_asm_on_failure) {
                std::cout << "See disassembly at:\n  " << log_path_storage_
                          << std::endl;
            }

            return entrypoint;
        }
    };

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

    runtime::Context
    test_context(int64_t gas_remaining = (uint64_t{1} << 63) - 1)
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

    std::vector<Emitter::LocationType> const all_locations = {
        Emitter::LocationType::Literal,
        Emitter::LocationType::AvxReg,
        Emitter::LocationType::GeneralReg,
        Emitter::LocationType::StackOffset};

    void mov_literal_to_location_type(
        Emitter &emit, int32_t stack_index, Emitter::LocationType loc)
    {
        StackElem *spill;
        Stack &stack = emit.get_stack();
        auto elem = stack.get(stack_index);
        ASSERT_TRUE(
            elem->literal() && !elem->stack_offset() && !elem->avx_reg() &&
            !elem->general_reg());
        switch (loc) {
        case Emitter::LocationType::AvxReg:
            emit.mov_stack_index_to_avx_reg(stack_index);
            stack.spill_literal(elem);
            ASSERT_TRUE(
                elem->avx_reg() && !elem->stack_offset() && !elem->literal() &&
                !elem->general_reg());
            break;
        case Emitter::LocationType::GeneralReg:
            emit.mov_stack_index_to_general_reg(stack_index);
            stack.spill_literal(elem);
            ASSERT_TRUE(
                elem->general_reg() && !elem->stack_offset() &&
                !elem->literal() && !elem->avx_reg());
            break;
        case Emitter::LocationType::StackOffset:
            emit.mov_stack_index_to_stack_offset(stack_index);
            stack.spill_literal(elem);
            ASSERT_TRUE(elem->avx_reg().has_value());
            spill = stack.spill_avx_reg(elem);
            ASSERT_EQ(spill, nullptr);
            ASSERT_TRUE(
                elem->stack_offset() && !elem->general_reg() &&
                !elem->literal() && !elem->avx_reg());
            break;
        case Emitter::LocationType::Literal:
            break;
        }
    }

    void copy_stack_offset_to_location_type(
        Emitter &emit, int32_t stack_index, Emitter::LocationType loc)
    {
        Stack &stack = emit.get_stack();
        auto elem = stack.get(stack_index);
        ASSERT_TRUE(
            elem->stack_offset() && !elem->general_reg() && !elem->avx_reg() &&
            !elem->literal());
        switch (loc) {
        case Emitter::LocationType::AvxReg:
            emit.mov_stack_index_to_avx_reg(stack_index);
            ASSERT_TRUE(
                elem->avx_reg() && elem->stack_offset() && !elem->literal() &&
                !elem->general_reg());
            break;
        case Emitter::LocationType::GeneralReg:
            emit.mov_stack_index_to_general_reg(stack_index);
            ASSERT_TRUE(
                elem->general_reg() && elem->stack_offset() &&
                !elem->literal() && !elem->avx_reg());
            break;
        case Emitter::LocationType::StackOffset:
            break;
        case Emitter::LocationType::Literal:
            ASSERT_TRUE(false);
            break;
        }
    }

    using PureEmitterInstr = std::function<void(Emitter &)>;
    using PureEmitterInstrPtr = void (Emitter::*)();

    void pure_bin_instr_test_instance(
        asmjit::JitRuntime &rt, PureEmitterInstr instr, uint256_t const &left,
        Emitter::LocationType left_loc, uint256_t const &right,
        Emitter::LocationType right_loc, uint256_t const &result,
        basic_blocks::BasicBlocksIR const &ir, bool dup)
    {
#if 0
        if (left_loc != Emitter::LocationType::Literal || right_loc != Emitter::LocationType::AvxReg || dup) {
            return;
        }
#endif
#if 0
        std::cout <<
            std::format("LEFT {} : {}  and  RIGHT {} : {}",
                    left, Emitter::location_type_to_string(left_loc),
                    right, Emitter::location_type_to_string(right_loc)) << std::endl;
#endif

        TestEmitter emit{rt, ir.codesize};
        (void)emit.begin_new_block(ir.blocks()[0]);
        emit.push(right);
        if (dup) {
            emit.dup(1);
        }
        emit.push(left);
        if (dup) {
            emit.dup(1);
            emit.swap(2);
            emit.swap(1);
        }

        mov_literal_to_location_type(emit, 1 + 2 * dup, left_loc);
        mov_literal_to_location_type(emit, 2 * dup, right_loc);

        instr(emit);

        if (dup) {
            emit.swap(2);
            emit.swap(1);
            instr(emit);
        }
        else {
            emit.push(0);
        }
        emit.return_();

        entrypoint_t entry = emit.finish_contract(rt);
        auto ctx = test_context();
        auto const &ret = ctx.result;

        auto stack_memory = test_stack_memory();
        entry(&ctx, stack_memory.get());

        ASSERT_EQ(ret.status, runtime::StatusCode::Success);
        if (dup) {
            ASSERT_EQ(uint256_t::load_le(ret.offset), result);
        }
        else {
            ASSERT_EQ(uint256_t::load_le(ret.offset), 0);
        }
        ASSERT_EQ(uint256_t::load_le(ret.size), result);
    }

    void pure_una_instr_test_instance(
        asmjit::JitRuntime &rt, PureEmitterInstr instr, uint256_t const &input,
        Emitter::LocationType loc, uint256_t const &result,
        basic_blocks::BasicBlocksIR const &ir, bool dup)
    {
#if 0
        if (loc != Emitter::LocationType::GeneralReg || dup) {
            return;
        }
#endif
#if 0
        std::cout <<
            std::format("INPUT {} : {} with dup = {}",
                    input, Emitter::location_type_to_string(loc), dup)
            << std::endl;
#endif

        TestEmitter emit{rt, ir.codesize};
        (void)emit.begin_new_block(ir.blocks()[0]);
        emit.push(input);
        if (dup) {
            emit.dup(1);
        }

        mov_literal_to_location_type(emit, dup, loc);

        instr(emit);

        if (dup) {
            emit.swap(1);
            instr(emit);
        }
        else {
            emit.push(0);
        }
        emit.return_();

        entrypoint_t entry = emit.finish_contract(rt);
        auto ctx = test_context();
        auto const &ret = ctx.result;

        auto stack_memory = test_stack_memory();
        entry(&ctx, stack_memory.get());

        ASSERT_EQ(ret.status, runtime::StatusCode::Success);
        if (dup) {
            ASSERT_EQ(uint256_t::load_le(ret.offset), result);
        }
        else {
            ASSERT_EQ(uint256_t::load_le(ret.offset), 0);
        }
        ASSERT_EQ(uint256_t::load_le(ret.size), result);
    }

    void pure_bin_instr_test(
        asmjit::JitRuntime &rt, EvmOpCode opcode, PureEmitterInstr instr,
        uint256_t const &left, uint256_t const &right, uint256_t const &result)
    {
        std::vector<uint8_t> bytecode1{PUSH0, PUSH0, opcode, PUSH0, RETURN};
        auto ir1 =
            basic_blocks::BasicBlocksIR::unsafe_from(std::move(bytecode1));
        for (auto left_loc : all_locations) {
            for (auto right_loc : all_locations) {
                pure_bin_instr_test_instance(
                    rt,
                    instr,
                    left,
                    left_loc,
                    right,
                    right_loc,
                    result,
                    ir1,
                    false);
            }
        }

        std::vector<uint8_t> bytecode2{
            PUSH0,
            PUSH0,
            DUP1,
            PUSH0,
            DUP1,
            SWAP2,
            SWAP1,
            opcode,
            POP,
            opcode,
            RETURN};
        auto ir2 =
            basic_blocks::BasicBlocksIR::unsafe_from(std::move(bytecode2));
        for (auto left_loc : all_locations) {
            for (auto right_loc : all_locations) {
                pure_bin_instr_test_instance(
                    rt,
                    instr,
                    left,
                    left_loc,
                    right,
                    right_loc,
                    result,
                    ir2,
                    true);
            }
        }
    }

    void pure_bin_instr_test(
        asmjit::JitRuntime &rt, EvmOpCode opcode, PureEmitterInstrPtr instr,
        uint256_t const &left, uint256_t const &right, uint256_t const &result)
    {
        pure_bin_instr_test(
            rt, opcode, [&](Emitter &e) { (e.*instr)(); }, left, right, result);
    }

    void pure_una_instr_test(
        asmjit::JitRuntime &rt, EvmOpCode opcode, PureEmitterInstr instr,
        uint256_t const &input, uint256_t const &result)
    {
        std::vector<uint8_t> bytecode1{PUSH0, opcode, PUSH0, RETURN};
        auto ir1 =
            basic_blocks::BasicBlocksIR::unsafe_from(std::move(bytecode1));
        for (auto loc : all_locations) {
            pure_una_instr_test_instance(
                rt, instr, input, loc, result, ir1, false);
        }

        std::vector<uint8_t> bytecode2{
            PUSH0, DUP1, opcode, SWAP1, opcode, RETURN};
        auto ir2 =
            basic_blocks::BasicBlocksIR::unsafe_from(std::move(bytecode2));
        for (auto loc : all_locations) {
            pure_una_instr_test_instance(
                rt, instr, input, loc, result, ir1, true);
        }
    }

    void pure_una_instr_test(
        asmjit::JitRuntime &rt, EvmOpCode opcode, PureEmitterInstrPtr instr,
        uint256_t const &input, uint256_t const &result)
    {
        pure_una_instr_test(
            rt, opcode, [&](Emitter &e) { (e.*instr)(); }, input, result);
    }

    void jump_test(
        Emitter::LocationType loc1, Emitter::LocationType loc2,
        Emitter::LocationType loc_dest, bool swap)
    {
#if 0
        if (swap || loc1 != Emitter::LocationType::Literal || loc2 != Emitter::LocationType::AvxReg || loc_dest != Emitter::LocationType::Literal) {
            return;
        }
#endif
#if 0
        std::cout <<
            std::format("LOC1 {}  and  LOC2 {}  and  LOC_DEST {}",
                    Emitter::location_type_to_string(loc1),
                    Emitter::location_type_to_string(loc2),
                    Emitter::location_type_to_string(loc_dest)) << std::endl;
#endif

        auto ir =
            swap ? basic_blocks::BasicBlocksIR::unsafe_from(
                       {PUSH0, PUSH0, PUSH0, SWAP1, JUMP, JUMPDEST, RETURN})
                 : basic_blocks::BasicBlocksIR::unsafe_from(
                       {PUSH0, PUSH0, PUSH0, JUMP, JUMPDEST, RETURN});

        asmjit::JitRuntime rt;
        TestEmitter emit{rt, ir.codesize};

        for (auto const &[k, _] : ir.jump_dests()) {
            emit.add_jump_dest(k);
        }

        (void)emit.begin_new_block(ir.blocks()[0]);
        emit.push(1);
        mov_literal_to_location_type(emit, 0, loc1);
        if (swap) {
            emit.push(5);
            mov_literal_to_location_type(emit, 1, loc_dest);
            emit.push(2);
            mov_literal_to_location_type(emit, 2, loc2);
            emit.swap(1);
        }
        else {
            emit.push(2);
            mov_literal_to_location_type(emit, 1, loc2);
            emit.push(4);
            mov_literal_to_location_type(emit, 2, loc_dest);
        }
        emit.jump();
        (void)emit.begin_new_block(ir.blocks()[1]);
        emit.return_();

        entrypoint_t entry = emit.finish_contract(rt);
        auto ctx = test_context();
        auto const &ret = ctx.result;

        auto stack_memory = test_stack_memory();
        entry(&ctx, stack_memory.get());

        ASSERT_EQ(uint256_t::load_le(ret.offset), 2);
        ASSERT_EQ(uint256_t::load_le(ret.size), 1);
    }

    basic_blocks::BasicBlocksIR get_jumpi_ir(
        bool deferred_comparison, bool swap, bool dup,
        bool jumpdest_fallthrough)
    {
        std::vector<uint8_t> bytecode;
        if (deferred_comparison && swap) {
            if (dup) {
                bytecode = {PUSH0, PUSH0, DUP2, ISZERO, DUP2, SWAP2, JUMPI};
            }
            else {
                bytecode = {PUSH0, PUSH0, PUSH0, ISZERO, PUSH0, SWAP2, JUMPI};
            }
        }
        else if (deferred_comparison) {
            if (dup) {
                bytecode = {PUSH0, PUSH0, DUP2, ISZERO, DUP2, JUMPI};
            }
            else {
                bytecode = {PUSH0, PUSH0, PUSH0, ISZERO, PUSH0, JUMPI};
            }
        }
        else if (swap) {
            if (dup) {
                bytecode = {PUSH0, PUSH0, DUP2, DUP2, SWAP2, JUMPI};
            }
            else {
                bytecode = {PUSH0, PUSH0, PUSH0, PUSH0, SWAP2, JUMPI};
            }
        }
        else if (dup) {
            bytecode = {PUSH0, PUSH0, DUP2, DUP2, JUMPI};
        }
        else {
            bytecode = {PUSH0, PUSH0, PUSH0, PUSH0, JUMPI};
        }

        if (jumpdest_fallthrough) {
            bytecode.push_back(JUMPDEST);
        }

        bytecode.push_back(RETURN);
        bytecode.push_back(JUMPDEST);
        bytecode.push_back(REVERT);

        return basic_blocks::BasicBlocksIR::unsafe_from(std::move(bytecode));
    }

    void jumpi_test(
        asmjit::JitRuntime &rt, Emitter::LocationType loc1,
        Emitter::LocationType loc2, Emitter::LocationType loc_cond,
        Emitter::LocationType loc_dest, bool take_jump,
        bool deferred_comparison, bool swap, bool dup,
        bool jumpdest_fallthrough)
    {
#if 0
        if (!take_jump || deferred_comparison || swap || dup || !jumpdest_fallthrough || loc1 != Emitter::LocationType::GeneralReg || loc2 != Emitter::LocationType::GeneralReg || loc_cond != Emitter::LocationType::GeneralReg || loc_dest != Emitter::LocationType::StackOffset) {
            return;
        }
        std::cout <<
            std::format("LOC1 {}  and  LOC2 {}  and  LOC_COND {}  and  LOC_DEST {} and take_jump {} and deferred_comparison {} and swap {} and dup {}",
                    Emitter::location_type_to_string(loc1),
                    Emitter::location_type_to_string(loc2),
                    Emitter::location_type_to_string(loc_cond),
                    Emitter::location_type_to_string(loc_dest),
                    take_jump,
                    deferred_comparison,
                    swap,
                    dup) << std::endl;
#endif

        auto ir =
            get_jumpi_ir(deferred_comparison, swap, dup, jumpdest_fallthrough);

        TestEmitter emit{rt, ir.codesize};

        for (auto const &[k, _] : ir.jump_dests()) {
            emit.add_jump_dest(k);
        }

        uint256_t const cond = (take_jump + deferred_comparison) & 1;
        uint256_t const dest =
            6 + swap + deferred_comparison + jumpdest_fallthrough;

        (void)emit.begin_new_block(ir.blocks()[0]);

        emit.push(cond);
        if (dup) {
            mov_literal_to_location_type(emit, 0, loc_cond);
        }
        else {
            mov_literal_to_location_type(emit, 0, loc1);
        }
        emit.push(dest);
        if (swap || dup) {
            mov_literal_to_location_type(emit, 1, loc_dest);
        }
        else {
            mov_literal_to_location_type(emit, 1, loc2);
        }
        if (dup) {
            emit.dup(2);
        }
        else {
            emit.push(cond);
            mov_literal_to_location_type(emit, 2, loc_cond);
        }
        if (deferred_comparison) {
            emit.iszero();
        }
        if (dup) {
            emit.dup(2);
        }
        else {
            emit.push(dest);
            if (swap) {
                mov_literal_to_location_type(emit, 3, loc2);
            }
            else {
                mov_literal_to_location_type(emit, 3, loc_dest);
            }
        }
        if (swap) {
            emit.swap(2);
        }
        emit.jumpi(ir.blocks()[1]);

        (void)emit.begin_new_block(ir.blocks()[1]);
        emit.return_();

        (void)emit.begin_new_block(ir.blocks()[2]);
        emit.revert();

        entrypoint_t entry = emit.finish_contract(rt);
        auto ctx = test_context();
        auto const &ret = ctx.result;

        auto stack_memory = test_stack_memory();
        entry(&ctx, stack_memory.get());

        if (take_jump) {
            ASSERT_EQ(ret.status, runtime::StatusCode::Revert);
        }
        else {
            ASSERT_EQ(ret.status, runtime::StatusCode::Success);
        }
        ASSERT_EQ(uint256_t::load_le(ret.offset), dest);
        ASSERT_EQ(uint256_t::load_le(ret.size), cond);
    }

    void block_epilogue_test(
        Emitter::LocationType loc1, Emitter::LocationType loc2,
        Emitter::LocationType loc3, Emitter::LocationType loc4,
        Emitter::LocationType loc5)
    {
#if 0
        if (loc1 != Emitter::LocationType::StackOffset || loc2 != Emitter::LocationType::StackOffset || loc3 != Emitter::LocationType::StackOffset || loc4 != Emitter::LocationType::StackOffset || loc5 != Emitter::LocationType::StackOffset) {
            return;
        }
#endif
#if 0
        std::cout <<
            std::format("LOC1 {}  and  LOC2 {}  and  LOC3 {}  and  LOC4 {}  and  LOC5 {}",
                    Emitter::location_type_to_string(loc1),
                    Emitter::location_type_to_string(loc2),
                    Emitter::location_type_to_string(loc3),
                    Emitter::location_type_to_string(loc4),
                    Emitter::location_type_to_string(loc5)) << std::endl;
#endif

        auto ir = basic_blocks::BasicBlocksIR::unsafe_from(
            {PUSH0,
             PUSH0,
             JUMPDEST,
             PUSH0,
             SWAP2,
             SWAP1,
             DUP1,
             DUP1,
             PUSH0,
             PUSH0,
             SWAP1,
             JUMPDEST,
             SUB,
             SUB,
             SUB,
             SUB,
             SUB,
             RETURN});

        asmjit::JitRuntime rt;
        TestEmitter emit{rt, ir.codesize};

        (void)emit.begin_new_block(ir.blocks()[0]);
        emit.push(1);
        emit.push(10);
        emit.fallthrough();

        (void)emit.begin_new_block(ir.blocks()[1]);
        copy_stack_offset_to_location_type(emit, -2, loc1);
        copy_stack_offset_to_location_type(emit, -1, loc2);

        emit.push(2); // [2, 10, 1]
        mov_literal_to_location_type(emit, 0, loc3);
        emit.swap(2); // [1, 10, 2]
        emit.swap(1); // [10, 1, 2]
        emit.dup(1); // [10, 10, 1, 2]
        emit.dup(1); // [10, 10 10, 1, 2]
        emit.push(1000); // [1000, 10, 10 10, 1, 2]
        mov_literal_to_location_type(emit, 3, loc4);
        emit.push(100); // [100, 1000, 10, 10 10, 1, 2]
        mov_literal_to_location_type(emit, 4, loc5);
        emit.swap(1); // [1000, 100, 10, 10 10, 1, 2]
        emit.fallthrough();

        (void)emit.begin_new_block(ir.blocks()[2]);
        emit.sub(); // [900, 10, 10 10, 1, 2]
        emit.sub(); // [890, 10 10, 1, 2]
        emit.sub(); // [880, 10, 1, 2]
        emit.sub(); // [870, 1, 2]
        emit.sub(); // [869, 2]
        emit.return_();

        entrypoint_t entry = emit.finish_contract(rt);
        auto ctx = test_context();
        auto const &ret = ctx.result;

        auto stack_memory = test_stack_memory();
        entry(&ctx, stack_memory.get());

        ASSERT_EQ(ret.status, runtime::StatusCode::Success);
        ASSERT_EQ(uint256_t::load_le(ret.offset), 869);
        ASSERT_EQ(uint256_t::load_le(ret.size), 2);
    }

    void runtime_test_12_arg_fun(
        runtime::Context *ctx, uint256_t *result, uint256_t const *a,
        uint256_t const *b, uint256_t const *c, uint256_t const *d,
        uint256_t const *e, uint256_t const *f, uint256_t const *g,
        uint256_t const *h, uint256_t const *i, int64_t remaining_base_gas)
    {
        *result = uint256_t{ctx->gas_remaining} -
                  (uint256_t{remaining_base_gas} -
                   (*a - (*b - (*c - (*d - (*e - (*f - (*g - (*h - *i)))))))));
    }

    void runtime_test_11_arg_fun(
        runtime::Context *ctx, uint256_t *result, uint256_t const *a,
        uint256_t const *b, uint256_t const *c, uint256_t const *d,
        uint256_t const *e, uint256_t const *f, uint256_t const *g,
        uint256_t const *h, int64_t remaining_base_gas)
    {
        *result = uint256_t{ctx->gas_remaining} -
                  (uint256_t{remaining_base_gas} -
                   (*a - (*b - (*c - (*d - (*e - (*f - (*g - *h))))))));
    }
}

TEST(Emitter, empty)
{
    asmjit::JitRuntime rt;
    TestEmitter emit{rt, code_size_t{}};

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    entry(&ctx, nullptr);

    ASSERT_EQ(
        static_cast<uint64_t>(ret.status),
        std::numeric_limits<uint64_t>::max());
}

TEST(Emitter, stop)
{
    asmjit::JitRuntime rt;
    TestEmitter emit{rt, bin<1>};
    emit.stop();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    entry(&ctx, nullptr);

    ASSERT_EQ(ret.status, runtime::StatusCode::Success);
}

TEST(Emitter, fail_with_error)
{
    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, bin<1>};
    // Test that asmjit error handler is in place:
    EXPECT_THROW(emit.fail_with_error(asmjit::kErrorOk), Emitter::Error);
}

TEST(Emitter, invalid_instruction)
{
    asmjit::JitRuntime rt;
    TestEmitter emit{rt, bin<1>};
    emit.invalid_instruction();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    entry(&ctx, nullptr);

    ASSERT_EQ(ret.status, runtime::StatusCode::Error);
}

TEST(Emitter, gas_decrement_no_check_1)
{
    asmjit::JitRuntime rt;
    TestEmitter emit{rt, code_size_t{}};
    emit.gas_decrement_no_check(2);

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context(5);

    entry(&ctx, nullptr);

    ASSERT_EQ(ctx.gas_remaining, 3);
}

TEST(Emitter, gas_decrement_no_check_2)
{
    asmjit::JitRuntime rt;
    TestEmitter emit{rt, code_size_t{}};
    emit.gas_decrement_no_check(7);

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context(5);

    entry(&ctx, nullptr);

    ASSERT_EQ(ctx.gas_remaining, -2);
}

TEST(Emitter, gas_decrement_check_non_negative_1)
{
    asmjit::JitRuntime rt;
    TestEmitter emit{rt, code_size_t{}};
    emit.gas_decrement_check_non_negative(6);
    emit.stop();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context(5);
    auto const &ret = ctx.result;

    entry(&ctx, nullptr);

    ASSERT_EQ(ctx.gas_remaining, -1);
    ASSERT_EQ(ret.status, runtime::StatusCode::Error);
}

TEST(Emitter, gas_decrement_check_non_negative_2)
{
    asmjit::JitRuntime rt;
    TestEmitter emit{rt, code_size_t{}};
    emit.gas_decrement_check_non_negative(5);
    emit.stop();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context(5);
    auto const &ret = ctx.result;

    entry(&ctx, nullptr);

    ASSERT_EQ(ctx.gas_remaining, 0);
    ASSERT_EQ(ret.status, runtime::StatusCode::Success);
}

TEST(Emitter, gas_decrement_check_non_negative_3)
{
    asmjit::JitRuntime rt;
    TestEmitter emit{rt, code_size_t{}};
    emit.gas_decrement_check_non_negative(4);
    emit.stop();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context(5);
    auto const &ret = ctx.result;

    entry(&ctx, nullptr);

    ASSERT_EQ(ctx.gas_remaining, 1);
    ASSERT_EQ(ret.status, runtime::StatusCode::Success);
}

TEST(Emitter, return_)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH1, 1, PUSH1, 2});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    uint256_t const size_value = uint256_t{1} << 255;
    uint256_t const offset_value =
        std::numeric_limits<uint256_t>::max() - (uint256_t{1} << 31) + 1;
    emit.push(size_value);
    emit.push(offset_value);
    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    entry(&ctx, nullptr);

    ASSERT_EQ(ret.status, runtime::StatusCode::Success);
    ASSERT_EQ(uint256_t::load_le(ret.offset), offset_value);
    ASSERT_EQ(uint256_t::load_le(ret.size), size_value);
}

TEST(Emitter, revert)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH1, 1, PUSH1, 2});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    uint256_t const size_value = uint256_t{1} << 31;
    uint256_t const offset_value = (uint256_t{1} << 31) - 1;
    emit.push(size_value);
    emit.push(offset_value);
    emit.revert();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    entry(&ctx, nullptr);

    ASSERT_EQ(ret.status, runtime::StatusCode::Revert);
    ASSERT_EQ(uint256_t::load_le(ret.offset), offset_value);
    ASSERT_EQ(uint256_t::load_le(ret.size), size_value);
}

TEST(Emitter, mov_stack_index_to_avx_reg)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH1, 1, PUSH1, 2});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    Stack &stack = emit.get_stack();
    emit.push(1);
    emit.push(2);

    auto e0 = stack.get(0);

    emit.mov_stack_index_to_avx_reg(0); // literal -> avx reg
    stack.spill_literal(e0);
    ASSERT_TRUE(
        e0->avx_reg() && !e0->stack_offset() && !e0->literal() &&
        !e0->general_reg());

    emit.mov_stack_index_to_avx_reg(0); // avx reg -> avx reg
    ASSERT_TRUE(
        e0->avx_reg() && !e0->stack_offset() && !e0->literal() &&
        !e0->general_reg());

    emit.mov_stack_index_to_general_reg(0);
    stack.spill_stack_offset(e0);
    (void)stack.spill_avx_reg(e0);
    ASSERT_TRUE(
        e0->general_reg() && !e0->stack_offset() && !e0->literal() &&
        !e0->avx_reg());

    emit.mov_stack_index_to_avx_reg(0); // general reg -> stack offset & avx reg
    (void)stack.spill_general_reg(e0);
    (void)stack.spill_avx_reg(e0);
    ASSERT_TRUE(
        e0->stack_offset() && !e0->general_reg() && !e0->literal() &&
        !e0->avx_reg());

    emit.mov_stack_index_to_avx_reg(0); // stack offset -> avx reg
    stack.spill_stack_offset(e0);
    ASSERT_TRUE(
        e0->avx_reg() && !e0->general_reg() && !e0->literal() &&
        !e0->stack_offset());

    e0.reset();

    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    auto stack_memory = test_stack_memory();
    entry(&ctx, stack_memory.get());

    ASSERT_EQ(ret.status, runtime::StatusCode::Success);
    ASSERT_EQ(uint256_t::load_le(ret.offset), 2);
    ASSERT_EQ(uint256_t::load_le(ret.size), 1);
}

TEST(Emitter, mov_literal_to_ymm)
{
    std::vector<uint256_t> literals{
        0, // vpxor
        std::numeric_limits<uint256_t>::max(), // vpcmpeqd (ymm)
        std::numeric_limits<uint256_t>::max() >> 128, // vpcmpeqd (xmm)
        std::numeric_limits<uint32_t>::max() - 2, // vmovd
        std::numeric_limits<uint64_t>::max() - 2, // vmovq
        (std::numeric_limits<uint256_t>::max() >> 128) - 2, // vmovups (xmm)
        std::numeric_limits<uint256_t>::max() - 2, // vmovaps (ymm)
    };

    for (auto const &lit0 : literals) {
        for (auto const &lit1 : literals) {
            auto ir = basic_blocks::BasicBlocksIR::unsafe_from(
                {PUSH0, PUSH0, RETURN});

            asmjit::JitRuntime rt;
            TestEmitter emit{rt, ir.codesize};
            (void)emit.begin_new_block(ir.blocks()[0]);
            Stack &stack = emit.get_stack();
            emit.push(lit0);
            emit.push(lit1);

            auto e0 = stack.get(0);
            emit.mov_stack_index_to_avx_reg(0);
            stack.spill_literal(e0);
            ASSERT_TRUE(
                e0->avx_reg() && !e0->stack_offset() && !e0->literal() &&
                !e0->general_reg());

            auto e1 = stack.get(1);
            emit.mov_stack_index_to_avx_reg(1);
            stack.spill_literal(e1);
            ASSERT_TRUE(
                e1->avx_reg() && !e1->stack_offset() && !e1->literal() &&
                !e1->general_reg());

            emit.return_();

            entrypoint_t entry = emit.finish_contract(rt);
            auto ctx = test_context();
            auto const &ret = ctx.result;

            auto stack_memory = test_stack_memory();
            entry(&ctx, stack_memory.get());

            ASSERT_EQ(ret.status, runtime::StatusCode::Success);
            ASSERT_EQ(uint256_t::load_le(ret.offset), lit1);
            ASSERT_EQ(uint256_t::load_le(ret.size), lit0);
        }
    }
}

TEST(Emitter, mov_stack_index_to_general_reg)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH1, 1, PUSH1, 2});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    Stack &stack = emit.get_stack();
    emit.push(1);
    emit.push(2);

    auto e1 = stack.get(1);

    emit.mov_stack_index_to_general_reg(1); // literal -> general reg
    stack.spill_literal(e1);
    ASSERT_TRUE(
        e1->general_reg() && !e1->stack_offset() && !e1->literal() &&
        !e1->avx_reg());

    emit.mov_stack_index_to_general_reg(1); // general reg -> general reg
    ASSERT_TRUE(
        e1->general_reg() && !e1->stack_offset() && !e1->literal() &&
        !e1->avx_reg());

    emit.mov_stack_index_to_avx_reg(1);
    (void)stack.spill_general_reg(e1);
    ASSERT_TRUE(
        e1->avx_reg() && !e1->stack_offset() && !e1->literal() &&
        !e1->general_reg());

    emit.mov_stack_index_to_general_reg(
        1); // avx reg -> stack offset & general reg
    (void)stack.spill_avx_reg(e1);
    (void)stack.spill_general_reg(e1);
    ASSERT_TRUE(
        e1->stack_offset() && !e1->avx_reg() && !e1->literal() &&
        !e1->general_reg());

    emit.mov_stack_index_to_general_reg(1); // stack offset -> general reg
    stack.spill_stack_offset(e1);
    ASSERT_TRUE(
        e1->general_reg() && !e1->avx_reg() && !e1->literal() &&
        !e1->stack_offset());

    e1.reset();

    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    auto stack_memory = test_stack_memory();
    entry(&ctx, stack_memory.get());

    ASSERT_EQ(ret.status, runtime::StatusCode::Success);
    ASSERT_EQ(uint256_t::load_le(ret.offset), 2);
    ASSERT_EQ(uint256_t::load_le(ret.size), 1);
}

TEST(Emitter, mov_stack_index_to_stack_offset)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH1, 1, PUSH1, 2});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    Stack &stack = emit.get_stack();
    emit.push(1);
    emit.push(2);

    auto e1 = stack.get(1);

    emit.mov_stack_index_to_stack_offset(1); // literal -> stack offset
    stack.spill_literal(e1);
    ASSERT_TRUE(
        e1->stack_offset() && !e1->general_reg() && !e1->literal() &&
        e1->avx_reg());

    auto *spill = stack.spill_avx_reg(e1);
    ASSERT_EQ(spill, nullptr);
    ASSERT_TRUE(
        e1->stack_offset() && !e1->general_reg() && !e1->literal() &&
        !e1->avx_reg());

    emit.mov_stack_index_to_stack_offset(1); // stack offset -> stack offset
    ASSERT_TRUE(
        e1->stack_offset() && !e1->general_reg() && !e1->literal() &&
        !e1->avx_reg());

    emit.mov_stack_index_to_avx_reg(1);
    stack.spill_stack_offset(e1);
    ASSERT_TRUE(
        e1->avx_reg() && !e1->stack_offset() && !e1->literal() &&
        !e1->general_reg());

    emit.mov_stack_index_to_stack_offset(1); // avx reg -> stack offset
    spill = stack.spill_avx_reg(e1);
    ASSERT_EQ(spill, nullptr);
    ASSERT_TRUE(
        e1->stack_offset() && !e1->avx_reg() && !e1->literal() &&
        !e1->general_reg());

    emit.mov_stack_index_to_general_reg(1); // stack offset -> general reg
    stack.spill_stack_offset(e1);
    ASSERT_TRUE(
        e1->general_reg() && !e1->avx_reg() && !e1->literal() &&
        !e1->stack_offset());

    emit.mov_stack_index_to_stack_offset(1); // general reg -> stack offset
    spill = stack.spill_general_reg(e1);
    ASSERT_EQ(spill, nullptr);
    ASSERT_TRUE(
        e1->stack_offset() && !e1->avx_reg() && !e1->literal() &&
        !e1->general_reg());

    e1.reset();

    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    auto stack_memory = test_stack_memory();
    entry(&ctx, stack_memory.get());

    ASSERT_EQ(ret.status, runtime::StatusCode::Success);
    ASSERT_EQ(uint256_t::load_le(ret.offset), 2);
    ASSERT_EQ(uint256_t::load_le(ret.size), 1);
}

TEST(Emitter, discharge_deferred_comparison)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(
        {PUSH0, PUSH0, LT, DUP1, DUP1, PUSH0, SWAP1, POP, LT, RETURN});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    Stack const &stack = emit.get_stack();
    emit.push(2);
    mov_literal_to_location_type(emit, 0, Emitter::LocationType::StackOffset);
    emit.push(1);
    ASSERT_FALSE(stack.has_deferred_comparison());
    emit.lt();
    ASSERT_TRUE(stack.has_deferred_comparison_at(0));
    emit.dup(1);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0));
    ASSERT_TRUE(stack.has_deferred_comparison_at(1));
    emit.dup(1);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0));
    ASSERT_TRUE(stack.has_deferred_comparison_at(1));
    ASSERT_TRUE(stack.has_deferred_comparison_at(2));
    emit.push(3);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0));
    ASSERT_TRUE(stack.has_deferred_comparison_at(1));
    ASSERT_TRUE(stack.has_deferred_comparison_at(2));
    ASSERT_FALSE(stack.has_deferred_comparison_at(3));
    emit.swap(1);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0));
    ASSERT_TRUE(stack.has_deferred_comparison_at(1));
    ASSERT_FALSE(stack.has_deferred_comparison_at(2));
    ASSERT_TRUE(stack.has_deferred_comparison_at(3));
    emit.pop();
    emit.lt();
    ASSERT_FALSE(stack.has_deferred_comparison_at(0));
    ASSERT_TRUE(stack.has_deferred_comparison_at(1));
    emit.return_();
    ASSERT_FALSE(stack.has_deferred_comparison());

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    auto stack_memory = test_stack_memory();
    entry(&ctx, stack_memory.get());

    ASSERT_EQ(ret.status, runtime::StatusCode::Success);
    ASSERT_EQ(uint256_t::load_le(ret.offset), 0);
    ASSERT_EQ(uint256_t::load_le(ret.size), 1);
}

TEST(Emitter, discharge_negated_deferred_comparison)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(
        {PUSH0,
         PUSH0,
         LT,
         DUP1,
         ISZERO,
         SWAP1,
         DUP1,
         ISZERO,
         SWAP2,
         ISZERO,
         SWAP2,
         LT,
         SWAP1,
         ISZERO,
         ISZERO,
         ISZERO,
         RETURN});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    Stack const &stack = emit.get_stack();
    emit.push(2);
    mov_literal_to_location_type(emit, 0, Emitter::LocationType::StackOffset);
    emit.push(1);
    ASSERT_FALSE(stack.has_deferred_comparison());
    emit.lt();
    ASSERT_TRUE(stack.has_deferred_comparison_at(0)); // 1
    emit.dup(1);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0)); // 1
    ASSERT_TRUE(stack.has_deferred_comparison_at(1)); // 1
    emit.iszero();
    ASSERT_TRUE(stack.has_deferred_comparison_at(0)); // 1
    ASSERT_TRUE(stack.has_deferred_comparison_at(1)); // 0
    emit.swap(1);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0)); // 0
    ASSERT_TRUE(stack.has_deferred_comparison_at(1)); // 1
    emit.dup(1);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0)); // 0
    ASSERT_TRUE(stack.has_deferred_comparison_at(1)); // 1
    ASSERT_TRUE(stack.has_deferred_comparison_at(2)); // 1
    emit.iszero();
    ASSERT_TRUE(stack.has_deferred_comparison_at(0)); // 0
    ASSERT_TRUE(stack.has_deferred_comparison_at(1)); // 1
    ASSERT_TRUE(stack.has_deferred_comparison_at(2)); // 0
    emit.swap(2);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0)); // 0
    ASSERT_TRUE(stack.has_deferred_comparison_at(1)); // 1
    ASSERT_TRUE(stack.has_deferred_comparison_at(2)); // 0
    emit.iszero();
    ASSERT_TRUE(stack.has_deferred_comparison_at(0)); // 0
    ASSERT_TRUE(stack.has_deferred_comparison_at(1)); // 1
    ASSERT_TRUE(stack.has_deferred_comparison_at(2)); // 1
    emit.swap(2);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0)); // 1
    ASSERT_TRUE(stack.has_deferred_comparison_at(1)); // 1
    ASSERT_TRUE(stack.has_deferred_comparison_at(2)); // 0
    emit.lt();
    ASSERT_FALSE(stack.has_deferred_comparison_at(0)); // 1
    ASSERT_TRUE(stack.has_deferred_comparison_at(1)); // 1
    emit.swap(1);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0)); // 1
    ASSERT_FALSE(stack.has_deferred_comparison_at(1)); // 1
    emit.iszero();
    ASSERT_FALSE(stack.has_deferred_comparison_at(0)); // 1
    ASSERT_TRUE(stack.has_deferred_comparison_at(1)); // 0
    emit.iszero();
    ASSERT_FALSE(stack.has_deferred_comparison_at(0)); // 1
    ASSERT_TRUE(stack.has_deferred_comparison_at(1)); // 1
    emit.iszero();
    ASSERT_FALSE(stack.has_deferred_comparison_at(0)); // 1
    ASSERT_TRUE(stack.has_deferred_comparison_at(1)); // 0
    emit.return_();
    ASSERT_FALSE(stack.has_deferred_comparison());

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    auto stack_memory = test_stack_memory();
    entry(&ctx, stack_memory.get());

    ASSERT_EQ(ret.status, runtime::StatusCode::Success);
    ASSERT_EQ(uint256_t::load_le(ret.offset), 0);
    ASSERT_EQ(uint256_t::load_le(ret.size), 1);
}

TEST(Emitter, lt)
{
    asmjit::JitRuntime rt;
    pure_bin_instr_test(rt, LT, &Emitter::lt, 5, 6, 1);
    pure_bin_instr_test(rt, LT, &Emitter::lt, 6, 5, 0);
    pure_bin_instr_test(rt, LT, &Emitter::lt, -1, -1, 0);
    pure_bin_instr_test(
        rt, LT, &Emitter::lt, {0, 0, -1, -1}, {0, 0, -1, -1}, 0);
    pure_bin_instr_test(
        rt,
        LT,
        &Emitter::lt,
        std::numeric_limits<uint256_t>::max(),
        std::numeric_limits<uint256_t>::max() - 1,
        0);
    pure_bin_instr_test(
        rt,
        LT,
        &Emitter::lt,
        std::numeric_limits<uint256_t>::max() - 1,
        std::numeric_limits<uint256_t>::max(),
        1);
    pure_bin_instr_test(rt, LT, &Emitter::lt, {0, 0, 1, 0}, {0, 0, 0, 1}, 1);
    pure_bin_instr_test(rt, LT, &Emitter::lt, {0, 0, 0, 1}, {0, 0, 1, 0}, 0);
}

TEST(Emitter, lt_same)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, DUP1, LT});
    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(0);
    emit.dup(1);
    mov_literal_to_location_type(emit, 0, Emitter::LocationType::AvxReg);
    auto e0 = emit.get_stack().get(0);
    auto e1 = emit.get_stack().get(1);
    ASSERT_EQ(e0, e1);
    emit.lt();
    ASSERT_EQ(emit.get_stack().get(0)->literal()->value, uint256_t{0});
}

TEST(Emitter, gt)
{
    asmjit::JitRuntime rt;
    pure_bin_instr_test(rt, GT, &Emitter::gt, 5, 6, 0);
    pure_bin_instr_test(rt, GT, &Emitter::gt, 6, 5, 1);
    pure_bin_instr_test(rt, GT, &Emitter::gt, -1, -1, 0);
    pure_bin_instr_test(
        rt, GT, &Emitter::gt, {0, 0, -1, -1}, {0, 0, -1, -1}, 0);
    pure_bin_instr_test(
        rt,
        GT,
        &Emitter::gt,
        std::numeric_limits<uint256_t>::max(),
        std::numeric_limits<uint256_t>::max() - 1,
        1);
    pure_bin_instr_test(
        rt,
        GT,
        &Emitter::gt,
        std::numeric_limits<uint256_t>::max() - 1,
        std::numeric_limits<uint256_t>::max(),
        0);
    pure_bin_instr_test(rt, LT, &Emitter::gt, {0, 0, 1, 0}, {0, 0, 0, 1}, 0);
    pure_bin_instr_test(rt, LT, &Emitter::gt, {0, 0, 0, 1}, {0, 0, 1, 0}, 1);
}

TEST(Emitter, gt_same)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, DUP1, GT});
    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(0);
    emit.dup(1);
    mov_literal_to_location_type(emit, 0, Emitter::LocationType::AvxReg);
    auto e0 = emit.get_stack().get(0);
    auto e1 = emit.get_stack().get(1);
    ASSERT_EQ(e0, e1);
    emit.gt();
    ASSERT_EQ(emit.get_stack().get(0)->literal()->value, uint256_t{0});
}

TEST(Emitter, slt)
{
    asmjit::JitRuntime rt;
    pure_bin_instr_test(rt, SLT, &Emitter::slt, 5, 6, 1);
    pure_bin_instr_test(rt, SLT, &Emitter::slt, 6, 5, 0);
    pure_bin_instr_test(rt, SLT, &Emitter::slt, -1, -1, 0);
    pure_bin_instr_test(
        rt, SLT, &Emitter::slt, {0, 0, -1, -1}, {0, 0, -1, -1}, 0);
    pure_bin_instr_test(
        rt,
        SLT,
        &Emitter::slt,
        std::numeric_limits<uint256_t>::max(),
        std::numeric_limits<uint256_t>::max() - 1,
        0);
    pure_bin_instr_test(
        rt,
        SLT,
        &Emitter::slt,
        std::numeric_limits<uint256_t>::max() - 1,
        std::numeric_limits<uint256_t>::max(),
        1);
    pure_bin_instr_test(
        rt,
        SLT,
        &Emitter::slt,
        std::numeric_limits<uint256_t>::max() >> 1,
        0,
        0);
    pure_bin_instr_test(
        rt,
        SLT,
        &Emitter::slt,
        0,
        std::numeric_limits<uint256_t>::max() >> 1,
        1);
    pure_bin_instr_test(rt, SLT, &Emitter::slt, uint256_t{1} << 255, 0, 1);
    pure_bin_instr_test(rt, SLT, &Emitter::slt, 0, uint256_t{1} << 255, 0);
    pure_bin_instr_test(rt, SLT, &Emitter::slt, {0, 0, 1, 0}, {0, 0, 0, 1}, 1);
    pure_bin_instr_test(rt, SLT, &Emitter::slt, {0, 0, 0, 1}, {0, 0, 1, 0}, 0);
}

TEST(Emitter, slt_same)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, DUP1, SLT});
    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(0);
    emit.dup(1);
    mov_literal_to_location_type(emit, 0, Emitter::LocationType::AvxReg);
    auto e0 = emit.get_stack().get(0);
    auto e1 = emit.get_stack().get(1);
    ASSERT_EQ(e0, e1);
    emit.slt();
    ASSERT_EQ(emit.get_stack().get(0)->literal()->value, uint256_t{0});
}

TEST(Emitter, sgt)
{
    asmjit::JitRuntime rt;
    pure_bin_instr_test(rt, SGT, &Emitter::sgt, 5, 6, 0);
    pure_bin_instr_test(rt, SGT, &Emitter::sgt, 6, 5, 1);
    pure_bin_instr_test(rt, SGT, &Emitter::sgt, -1, -1, 0);
    pure_bin_instr_test(
        rt, SGT, &Emitter::sgt, {0, 0, -1, -1}, {0, 0, -1, -1}, 0);
    pure_bin_instr_test(
        rt,
        SGT,
        &Emitter::sgt,
        std::numeric_limits<uint256_t>::max(),
        std::numeric_limits<uint256_t>::max() - 1,
        1);
    pure_bin_instr_test(
        rt,
        SGT,
        &Emitter::sgt,
        std::numeric_limits<uint256_t>::max() - 1,
        std::numeric_limits<uint256_t>::max(),
        0);
    pure_bin_instr_test(
        rt,
        SGT,
        &Emitter::sgt,
        std::numeric_limits<uint256_t>::max() >> 1,
        0,
        1);
    pure_bin_instr_test(
        rt,
        SGT,
        &Emitter::sgt,
        0,
        std::numeric_limits<uint256_t>::max() >> 1,
        0);
    pure_bin_instr_test(rt, SGT, &Emitter::sgt, uint256_t{1} << 255, 0, 0);
    pure_bin_instr_test(rt, SGT, &Emitter::sgt, 0, uint256_t{1} << 255, 1);
    pure_bin_instr_test(rt, SGT, &Emitter::sgt, {0, 0, 1, 0}, {0, 0, 0, 1}, 0);
    pure_bin_instr_test(rt, SGT, &Emitter::sgt, {0, 0, 0, 1}, {0, 0, 1, 0}, 1);
}

TEST(Emitter, sgt_same)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, DUP1, SGT});
    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(0);
    emit.dup(1);
    mov_literal_to_location_type(emit, 0, Emitter::LocationType::AvxReg);
    auto e0 = emit.get_stack().get(0);
    auto e1 = emit.get_stack().get(1);
    ASSERT_EQ(e0, e1);
    emit.sgt();
    ASSERT_EQ(emit.get_stack().get(0)->literal()->value, uint256_t{0});
}

TEST(Emitter, sub)
{
    asmjit::JitRuntime rt;
    pure_bin_instr_test(
        rt, SUB, &Emitter::sub, 5, 6, std::numeric_limits<uint256_t>::max());
    pure_bin_instr_test(rt, SUB, &Emitter::sub, -1, -1, 0);
    pure_bin_instr_test(
        rt,
        SUB,
        &Emitter::sub,
        std::numeric_limits<uint256_t>::max(),
        std::numeric_limits<uint256_t>::max() - 1,
        1);
    pure_bin_instr_test(
        rt,
        SUB,
        &Emitter::sub,
        std::numeric_limits<uint256_t>::max() - 1,
        std::numeric_limits<uint256_t>::max(),
        std::numeric_limits<uint256_t>::max());
}

TEST(Emitter, sub_with_elim_operation)
{
    asmjit::JitRuntime rt;
    uint256_t const x{uint64_t{1} << 63, 3 << 1, 7 << 10, 15 << 20};
    uint256_t y{0};
    pure_bin_instr_test(rt, SUB, &Emitter::sub, x, y, x - y);
    pure_bin_instr_test(rt, SUB, &Emitter::sub, y, x, y - x);
    y[3] = 10;
    pure_bin_instr_test(rt, SUB, &Emitter::sub, x, y, x - y);
    pure_bin_instr_test(rt, SUB, &Emitter::sub, y, x, y - x);
    y[3] = 0;
    y[2] = uint64_t{1} << 63;
    pure_bin_instr_test(rt, SUB, &Emitter::sub, x, y, x - y);
    pure_bin_instr_test(rt, SUB, &Emitter::sub, y, x, y - x);
    y[2] = 0;
    y[1] = std::numeric_limits<uint64_t>::max();
    pure_bin_instr_test(rt, SUB, &Emitter::sub, x, y, x - y);
    pure_bin_instr_test(rt, SUB, &Emitter::sub, y, x, y - x);
}

TEST(Emitter, sub_identity)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, PUSH0, SUB});
    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(0);
    emit.push(10);
    mov_literal_to_location_type(emit, 1, Emitter::LocationType::GeneralReg);
    auto e = emit.get_stack().get(1);
    emit.sub();
    ASSERT_EQ(emit.get_stack().get(0), e);
}

TEST(Emitter, add)
{
    asmjit::JitRuntime rt;
    pure_bin_instr_test(rt, ADD, &Emitter::add, 5, 6, 11);
    pure_bin_instr_test(
        rt,
        ADD,
        &Emitter::add,
        -1,
        -1,
        uint256_t{0, 1, 0, 0} + uint256_t{0, 1, 0, 0} - 2);
    pure_bin_instr_test(
        rt,
        ADD,
        &Emitter::add,
        std::numeric_limits<uint256_t>::max(),
        std::numeric_limits<uint256_t>::max() - 1,
        std::numeric_limits<uint256_t>::max() - 2);
    pure_bin_instr_test(
        rt,
        ADD,
        &Emitter::add,
        std::numeric_limits<uint256_t>::max() - 1,
        std::numeric_limits<uint256_t>::max(),
        std::numeric_limits<uint256_t>::max() - 2);
}

TEST(Emitter, add_with_elim_operation)
{
    asmjit::JitRuntime rt;
    uint256_t const x{uint64_t{1} << 63, 3 << 1, 7 << 10, 15 << 20};
    uint256_t y{0};
    pure_bin_instr_test(rt, ADD, &Emitter::add, x, y, x + y);
    pure_bin_instr_test(rt, ADD, &Emitter::add, y, x, x + y);
    y[3] = 10;
    pure_bin_instr_test(rt, ADD, &Emitter::add, x, y, x + y);
    pure_bin_instr_test(rt, ADD, &Emitter::add, y, x, x + y);
    y[3] = 0;
    y[2] = uint64_t{1} << 63;
    pure_bin_instr_test(rt, ADD, &Emitter::add, x, y, x + y);
    pure_bin_instr_test(rt, ADD, &Emitter::add, y, x, x + y);
    y[2] = 0;
    y[1] = std::numeric_limits<uint64_t>::max();
    pure_bin_instr_test(rt, ADD, &Emitter::add, x, y, x + y);
    pure_bin_instr_test(rt, ADD, &Emitter::add, y, x, x + y);
}

TEST(Emitter, add_identity_right)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, PUSH0, ADD});
    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(0);
    emit.push(10);
    mov_literal_to_location_type(emit, 1, Emitter::LocationType::GeneralReg);
    auto e = emit.get_stack().get(1);
    emit.add();
    ASSERT_EQ(emit.get_stack().get(0), e);
}

TEST(Emitter, add_identity_left)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, PUSH0, ADD});
    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(10);
    emit.push(0);
    mov_literal_to_location_type(emit, 0, Emitter::LocationType::GeneralReg);
    auto e = emit.get_stack().get(0);
    emit.add();
    ASSERT_EQ(emit.get_stack().get(0), e);
}

TEST(Emitter, mul)
{
    uint256_t bit256{0, 0, 0, static_cast<uint64_t>(1) << 63};
    uint256_t bit62{static_cast<uint64_t>(1) << 63};
    uint256_t clear_lhs{2, 3, 4, 5};
    uint256_t clear0{
        0x8765432187654321, 0x1234567812345678, 0x8765432187654321, 0x11};
    uint256_t clear1{0, 0x1234567812345678, 0x8765432187654321, 0x11};
    uint256_t clear2{0x1234567812345678, 0, 0x8765432187654321, 0x11};
    uint256_t clear3{0x1234567812345678, 0x8765432187654321, 0, 0x11};
    uint256_t clear4{0x1234567812345678, 0x8765432187654321, 0x11, 0};
    uint256_t clear12{0, 0, 0x8765432187654321, 0x1234567812345678};
    uint256_t clear23{0x8765432187654321, 0, 0, 0x1234567812345678};
    uint256_t clear34{0x8765432187654321, 0x1234567812345678, 0, 0};
    uint256_t clear123{0, 0, 0, 0x1234567812345678};
    uint256_t clear234{0x8765432187654321, 0, 0, 0};
    std::vector<std::pair<uint256_t, uint256_t>> const pre_inputs{
        {0, 0},
        {0, bit256},
        {bit256, 0},
        {1, 1},
        {1, bit256},
        {bit256, 1},
        {bit62, bit256},
        {bit256, bit62},
        {5, 6},
        {5, bit62},
        {bit62, 5},
        {clear_lhs, clear0},
        {clear_lhs, clear1},
        {clear_lhs, clear2},
        {clear_lhs, clear3},
        {clear_lhs, clear4},
        {clear_lhs, clear12},
        {clear_lhs, clear23},
        {clear_lhs, clear34},
        {clear_lhs, clear123},
        {clear_lhs, clear234}};

    std::vector<std::pair<uint256_t, uint256_t>> inputs;
    for (auto const &[x, y] : pre_inputs) {
        inputs.emplace_back(x, y);
        inputs.emplace_back(-x, y);
        inputs.emplace_back(x, -y);
        inputs.emplace_back(-x, -y);
    }

    asmjit::JitRuntime rt;
    for (auto const &[a, b] : inputs) {
        auto const expected = a * b;
        pure_bin_instr_test(
            rt,
            PUSH0,
            [&](Emitter &em) {
                em.mul<EvmChain<EVMC_FRONTIER>>(
                    std::numeric_limits<int32_t>::max());
            },
            a,
            b,
            expected);
    }
}

TEST(Emitter, udiv)
{
    uint256_t bit256{0, 0, 0, static_cast<uint64_t>(1) << 63};
    uint256_t bit255{0, 0, 0, static_cast<uint64_t>(1) << 62};
    std::vector<std::pair<uint256_t, uint256_t>> const inputs{
        {0, 0},
        {0, bit256},
        {bit256, 0},
        {1, 1},
        {1, bit256},
        {bit256, 1},
        {bit256, bit255},
        {bit255, bit256},
        {bit256 + 2, bit255 + 1},
        {bit255 + 2, bit256 + 1}};
    asmjit::JitRuntime rt;
    for (auto const &[a, b] : inputs) {
        auto const expected = b == 0 ? 0 : a / b;
        pure_bin_instr_test(
            rt,
            PUSH0,
            [&](Emitter &em) {
                em.udiv<EvmChain<EVMC_FRONTIER>>(
                    std::numeric_limits<int32_t>::max());
            },
            a,
            b,
            expected);
    }
}

TEST(Emitter, sdiv)
{
    uint256_t bit256{0, 0, 0, static_cast<uint64_t>(1) << 63};
    uint256_t bit255{0, 0, 0, static_cast<uint64_t>(1) << 62};
    uint256_t bit64{static_cast<uint64_t>(1) << 63};
    uint256_t bit65{0, 1, 0, 0};
    uint256_t bit193{0, 0, 0, 1};
    uint256_t const bit63{static_cast<uint64_t>(1) << 62};
    std::vector<std::pair<uint256_t, uint256_t>> const inputs{
        {0, 0},
        {0, bit256},
        {bit256, 0},
        {1, 1},
        {1, bit256},
        {bit256, 1},
        {bit256, bit255},
        {bit255, bit256},
        {bit255, bit255},
        {-bit255, bit255},
        {bit255, -bit255},
        {-bit255, -bit255},
        {bit256, bit256},
        {bit256 + 1, bit256},
        {bit256, bit256 + 1},
        {bit256, bit64},
        {bit256 + 16, bit64},
        {bit256, -bit64},
        {bit256 + 16, -bit64},
        {bit256, bit65},
        {bit256 + 16, bit65},
        {bit256, -bit65},
        {bit256 + 16, -bit65},
        {-bit256, bit193},
        {-(bit256 + 16), bit193},
        {-bit256, -bit193},
        {-(bit256 + 16), -bit193},
        {bit64 * 3, bit64},
        {bit64 * 3, -bit64},
        {bit64 * 3 + bit63, bit64},
        {bit64 * 3 + bit63, -bit64},
        {-(bit64 * 3), bit64},
        {-(bit64 * 3), -bit64},
        {-(bit64 * 3 + bit63), bit64},
        {-(bit64 * 3 + bit63), -bit64}};
    asmjit::JitRuntime rt;
    for (auto const &[a, b] : inputs) {
        auto const expected = b == 0 ? 0 : sdivrem(a, b).quot;
        pure_bin_instr_test(
            rt,
            PUSH0,
            [&](Emitter &em) {
                em.sdiv<EvmChain<EVMC_FRONTIER>>(
                    std::numeric_limits<int32_t>::max());
            },
            a,
            b,
            expected);
    }
}

TEST(Emitter, umod)
{
    uint256_t bit256{0, 0, 0, static_cast<uint64_t>(1) << 63};
    uint256_t bit64{static_cast<uint64_t>(1) << 63};
    std::vector<std::pair<uint256_t, uint256_t>> const inputs{
        {0, 0},
        {bit64, 0},
        {0, bit64},
        {1, 1},
        {bit64, 1},
        {1, bit64},
        {bit64 - 2, bit64},
        {bit64, bit64 - 2},
        {bit256, bit64},
        {bit64, bit256},
        {bit256 + 1, bit64},
        {bit64, bit256 + 1}};
    asmjit::JitRuntime rt;
    for (auto const &[a, b] : inputs) {
        auto const expected = b == 0 ? 0 : a % b;
        pure_bin_instr_test(
            rt,
            PUSH0,
            [&](Emitter &em) {
                em.umod<EvmChain<EVMC_FRONTIER>>(
                    std::numeric_limits<int32_t>::max());
            },
            a,
            b,
            expected);
    }
}

TEST(Emitter, smod)
{
    uint256_t bit256{0, 0, 0, static_cast<uint64_t>(1) << 63};
    uint256_t bit255{0, 0, 0, static_cast<uint64_t>(1) << 62};
    uint256_t bit64{static_cast<uint64_t>(1) << 63};
    std::vector<std::pair<uint256_t, uint256_t>> const inputs{
        {0, 0},
        {bit64, 0},
        {0, bit64},

        {1, 1},
        {bit64, 1},
        {1, bit64},

        {bit64, 5},
        {-bit64, 5},
        {5, bit64},
        {5, -bit64},

        {bit64 - 2, bit64},
        {-(bit64 - 2), bit64},
        {bit64 - 2, -bit64},
        {-(bit64 - 2), -bit64},
        {bit64, bit64 - 2},
        {-bit64, bit64 - 2},
        {bit64, -(bit64 - 2)},
        {-bit64, -(bit64 - 2)},

        {bit256, bit64},
        {bit256, -bit64},
        {bit256 + 16, bit64},
        {bit256 + 16, -bit64},
        {bit64, bit256},
        {-bit64, bit256},

        {bit255, bit64},
        {-bit255, bit64},
        {bit255, -bit64},
        {-bit255, -bit64},
        {bit64, bit255},
        {-bit64, bit255},
        {bit64, -bit255},
        {-bit64, -bit255},

        {bit256 + 1, bit64},
        {bit64, bit256 + 1},
        {bit256 + 1, -bit64},
        {-bit64, bit256 + 1}};

    asmjit::JitRuntime rt;
    for (auto const &[a, b] : inputs) {
        auto const expected = b == 0 ? 0 : sdivrem(a, b).rem;
        pure_bin_instr_test(
            rt,
            PUSH0,
            [&](Emitter &em) {
                em.smod<EvmChain<EVMC_FRONTIER>>(
                    std::numeric_limits<int32_t>::max());
            },
            a,
            b,
            expected);
    }
}

TEST(Emitter, addmod_opt)
{
    asmjit::JitRuntime rt;
    {
        // Constant folding tests.
        std::vector<std::tuple<uint256_t, uint256_t, uint256_t>> inputs{
            {0, 0, 0},
            {1, 1, 0},
            {2, 4, 1},
            {2, 3, 4},
            {{0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF}, 1, 2},
            {43194, 13481, 1024},
            {0xFFFFFFFFF, 0x1, 512},
            {std::numeric_limits<uint256_t>::max(), 1, 10},
            {std::numeric_limits<uint256_t>::max() - 1,
             std::numeric_limits<uint256_t>::max() - 1,
             std::numeric_limits<uint256_t>::max()},
            {{0xffffffffffffffff,
              0xFFFFFFFFFFFFFFFF,
              0xFFFFFFFFFFFFFFFF,
              0xFFFFFFFFFFFFFFFE},
             {0xFFFFFFFFFFFFFFFF,
              0xFFFFFFFFFFFFFFFF,
              0xFFFFFFFFFFFFFFFF,
              0xFFFFFFFFFFFFFFFE},
             {0xFFFFFFFFFFFFFFFF,
              0xFFFFFFFFFFFFFFFF,
              0xFFFFFFFFFFFFFFFF,
              0xFFFFFFFFFFFFFFFF}}};
        for (auto &[a, b, m] : inputs) {
            auto expected = m == 0 ? 0 : addmod(a, b, m);
            pure_bin_instr_test(
                rt,
                PUSH0,
                [&](Emitter &em) {
                    em.pop();
                    em.pop();
                    em.push(m);
                    em.push(b);
                    em.push(a);
                    ASSERT_TRUE(em.addmod_opt());
                },
                0,
                0,
                expected);
        }
    }

    {
        // Known powers of two tests
        std::vector<std::tuple<uint256_t, uint256_t, uint256_t>> inputs{
            {0, 0, 0},
            {1, 1, 0},
            {2, 4, 1},
            {2, 3, 4},
            {1, 1, monad::vm::runtime::pow2(8)},
            {std::numeric_limits<uint8_t>::max(),
             1,
             monad::vm::runtime::pow2(8)},
            {std::numeric_limits<uint16_t>::max(),
             1,
             monad::vm::runtime::pow2(16)},
            {std::numeric_limits<uint32_t>::max(),
             1,
             monad::vm::runtime::pow2(32)},
            {std::numeric_limits<uint32_t>::max(),
             std::numeric_limits<uint32_t>::max(),
             monad::vm::runtime::pow2(32)},
            {std::numeric_limits<uint64_t>::max(),
             3,
             monad::vm::runtime::pow2(63)},
            {std::numeric_limits<uint64_t>::max(),
             1,
             monad::vm::runtime::pow2(64)},
            {std::numeric_limits<uint32_t>::max(),
             std::numeric_limits<uint8_t>::max(),
             monad::vm::runtime::pow2(62)},
            {std::numeric_limits<uint64_t>::max(), 1, 16},
            {std::numeric_limits<uint64_t>::max(),
             1,
             monad::vm::runtime::pow2(8)},
            {std::numeric_limits<uint64_t>::max(),
             std::numeric_limits<uint32_t>::max(),
             monad::vm::runtime::pow2(72)},
            {std::numeric_limits<uint8_t>::max(),
             1,
             monad::vm::runtime::pow2(128)},
            {std::numeric_limits<uint8_t>::max(),
             1,
             monad::vm::runtime::pow2(192)},
            {{0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF}, 1, 2},
            {43194, 13481, 1024},
            {0xFFFFFFFFF, 0x1, 512},
            {std::numeric_limits<uint256_t>::max(), 1, 8},
            {std::numeric_limits<uint256_t>::max() -
                 (std::numeric_limits<uint256_t>::max() / 2),
             std::numeric_limits<uint64_t>::max(),
             monad::vm::runtime::pow2(60)},
            {0, std::numeric_limits<uint256_t>::max(), 2},
            {std::numeric_limits<uint256_t>::max(), 0, 2}};
        for (auto &[a, b, m] : inputs) {
            auto expected = m == 0 ? 0 : addmod(a, b, m);
            pure_bin_instr_test(
                rt,
                PUSH0,
                [&](Emitter &em) {
                    em.push(m);
                    em.swap(2);
                    em.swap(1);
                    ASSERT_TRUE(em.addmod_opt());
                },
                a,
                b,
                expected);
        }
    }
}

TEST(Emitter, addmod_opt_with_elim_operation)
{
    uint256_t const x{
        (uint64_t{1} << 63) | 2, 3 << 1, (7 << 10) | 1, (15 << 20) | 7};
    std::vector<std::pair<uint256_t, uint256_t>> const inputs{
        {x, 0},
        {x, {0, 0, 0, (1 << 20) | 2}},
        {x, {0, 0, (2 << 10) | 3, 0}},
        {x, {0, std::numeric_limits<uint64_t>::max(), 0, 0}}};
    std::vector<int> shifts = {0, 1, 2, 3};
    for (int i = 4; i < 252; i += 4) {
        shifts.push_back(i);
    }
    for (int i = 252; i < 256; ++i) {
        shifts.push_back(i);
    }
    asmjit::JitRuntime rt;
    for (int const shift : shifts) {
        uint256_t m = uint256_t{1} << shift;
        for (auto [a, b] : inputs) {
            auto expected = m == 0 ? 0 : addmod(a, b, m);
            pure_bin_instr_test(
                rt,
                PUSH0,
                [&](Emitter &em) {
                    em.push(m);
                    em.swap(2);
                    em.swap(1);
                    ASSERT_TRUE(em.addmod_opt());
                },
                a,
                b,
                expected);
        }
    }
}

TEST(Emitter, addmod_nonopt)
{
    asmjit::JitRuntime rt;
    {
        pure_bin_instr_test(
            rt,
            PUSH0,
            [&](Emitter &em) {
                em.push(3);
                mov_literal_to_location_type(
                    em,
                    em.get_stack().top_index(),
                    Emitter::LocationType::GeneralReg);
                em.swap(2);
                em.swap(1);
                // The modulus is in a register
                ASSERT_FALSE(em.addmod_opt());
                em.call_runtime(10, true, runtime::addmod);
            },
            4,
            3,
            1);
    }

    {
        pure_bin_instr_test(
            rt,
            PUSH0,
            [&](Emitter &em) {
                em.push(2);
                mov_literal_to_location_type(
                    em,
                    em.get_stack().top_index(),
                    Emitter::LocationType::GeneralReg);
                em.swap(2);
                em.swap(1);
                // The modulus is not a literal
                ASSERT_FALSE(em.addmod_opt());
                em.call_runtime(10, true, runtime::addmod);
            },
            4,
            3,
            1);
    }
}

TEST(Emitter, mulmod)
{
    uint256_t const clear0{
        0x8765432187654321,
        0x1234567812345678,
        0x8765432187654321,
        0x1234567812345678};
    uint256_t const clear1{0, clear0[1], clear0[2], clear0[3]};
    uint256_t const clear2{clear0[0], 0, clear0[2], clear0[3]};
    uint256_t const clear3{clear0[0], clear0[1], 0, clear0[3]};
    uint256_t const clear4{clear0[0], clear0[1], clear0[2], 0};
    uint256_t const clear12{0, 0, clear0[2], clear0[3]};
    uint256_t const clear23{clear0[0], 0, 0, clear0[3]};
    uint256_t const clear34{clear0[0], clear0[1], 0, 0};
    uint256_t const clear14{0, clear0[1], clear0[2], 0};
    uint256_t const clear123{0, 0, 0, clear0[3]};
    uint256_t const clear234{clear0[0], 0, 0, 0};
    uint256_t const x{2, 3, 4, 5};

    std::vector<std::pair<uint256_t, uint256_t>> const pre_inputs{
        {clear0, x},
        {x, clear1},
        {clear2, x},
        {x, clear3},
        {clear4, x},
        {x, clear12},
        {clear23, x},
        {x, clear34},
        {clear14, x},
        {x, clear123},
        {clear234, x}};

    std::vector<std::pair<uint256_t, uint256_t>> inputs;
    for (auto const &[x, y] : pre_inputs) {
        inputs.emplace_back(x, y);
        inputs.emplace_back(-x, y);
        inputs.emplace_back(x, -y);
        inputs.emplace_back(-x, -y);
    }

    std::vector<int> shifts = {0, 1, 2, 3};
    for (int i = 4; i < 252; i += 4) {
        shifts.push_back(i);
    }
    for (int i = 252; i < 256; ++i) {
        shifts.push_back(i);
    }

    asmjit::JitRuntime rt;
    for (auto const &s : shifts) {
        for (auto &[a, b] : inputs) {
            uint256_t m = uint256_t{1} << s;
            auto expected = m == 0 ? 0 : mulmod(a, b, m);
            pure_bin_instr_test(
                rt,
                PUSH0,
                [&](Emitter &em) {
                    em.push(m);
                    em.swap(2);
                    em.swap(1);
                    em.mulmod<EvmChain<EVMC_LATEST_STABLE_REVISION>>(1000);
                },
                a,
                b,
                expected);
            pure_bin_instr_test(
                rt,
                PUSH0,
                [&](Emitter &em) {
                    em.swap(1);
                    em.push(m);
                    em.swap(2);
                    em.swap(1);
                    em.mulmod<EvmChain<EVMC_LATEST_STABLE_REVISION>>(1000);
                },
                a,
                b,
                expected);
        }
    }

    std::vector<uint256_t> const non_shift_mods = {
        uint256_t{31}, clear0, clear234, -uint256_t{31}, -clear0, -clear234};
    for (auto const &m : non_shift_mods) {
        for (auto &[a, b] : inputs) {
            auto expected = m == 0 ? 0 : mulmod(a, b, m);
            pure_bin_instr_test(
                rt,
                PUSH0,
                [&](Emitter &em) {
                    em.push(m);
                    em.swap(2);
                    em.swap(1);
                    em.mulmod<EvmChain<EVMC_LATEST_STABLE_REVISION>>(1000);
                },
                a,
                b,
                expected);
            pure_bin_instr_test(
                rt,
                PUSH0,
                [&](Emitter &em) {
                    em.swap(1);
                    em.push(m);
                    em.swap(2);
                    em.swap(1);
                    em.mulmod<EvmChain<EVMC_LATEST_STABLE_REVISION>>(1000);
                },
                a,
                b,
                expected);
        }
    }
}

TEST(Emitter, and_)
{
    asmjit::JitRuntime rt;
    pure_bin_instr_test(rt, AND, &Emitter::and_, 1, 3, 1);
    pure_bin_instr_test(rt, AND, &Emitter::and_, 2, 1, 0);
    pure_bin_instr_test(
        rt,
        AND,
        &Emitter::and_,
        std::numeric_limits<uint256_t>::max(),
        std::numeric_limits<uint256_t>::max() - 1,
        std::numeric_limits<uint256_t>::max() - 1);
}

TEST(Emitter, and_with_elim_operation)
{
    asmjit::JitRuntime rt;
    uint256_t const x{uint64_t{1} << 63, 3 << 1, 7 << 10, 15 << 20};
    uint256_t y{std::numeric_limits<uint256_t>::max()};
    pure_bin_instr_test(rt, AND, &Emitter::and_, x, y, x & y);
    pure_bin_instr_test(rt, AND, &Emitter::and_, y, x, y & x);
    y[3] = 1 << 20;
    pure_bin_instr_test(rt, AND, &Emitter::and_, x, y, x & y);
    pure_bin_instr_test(rt, AND, &Emitter::and_, y, x, y & x);
    y[1] = 2 << 1;
    pure_bin_instr_test(rt, AND, &Emitter::and_, x, y, x & y);
    pure_bin_instr_test(rt, AND, &Emitter::and_, y, x, y & x);
    y[0] = (uint64_t{1} << 63) | 1;
    pure_bin_instr_test(rt, AND, &Emitter::and_, x, y, x & y);
    pure_bin_instr_test(rt, AND, &Emitter::and_, y, x, y & x);
}

TEST(Emitter, and_identity_left)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, PUSH0, AND});
    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(10);
    emit.push(std::numeric_limits<uint256_t>::max());
    mov_literal_to_location_type(emit, 0, Emitter::LocationType::AvxReg);
    auto e = emit.get_stack().get(0);
    emit.and_();
    ASSERT_EQ(emit.get_stack().get(0), e);
}

TEST(Emitter, and_identity_right)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, PUSH0, AND});
    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(std::numeric_limits<uint256_t>::max());
    emit.push(10);
    mov_literal_to_location_type(emit, 1, Emitter::LocationType::AvxReg);
    auto e = emit.get_stack().get(1);
    emit.and_();
    ASSERT_EQ(emit.get_stack().get(0), e);
}

TEST(Emitter, or_)
{
    asmjit::JitRuntime rt;
    pure_bin_instr_test(rt, OR, &Emitter::or_, 1, 3, 3);
    pure_bin_instr_test(rt, OR, &Emitter::or_, 2, 1, 3);
    pure_bin_instr_test(
        rt,
        OR,
        &Emitter::or_,
        std::numeric_limits<uint256_t>::max(),
        std::numeric_limits<uint256_t>::max() - 1,
        std::numeric_limits<uint256_t>::max());
}

TEST(Emitter, or_with_elim_operation)
{
    asmjit::JitRuntime rt;
    uint256_t const x{uint64_t{1} << 63, 3 << 1, 7 << 10, 15 << 20};
    uint256_t y{0};
    pure_bin_instr_test(rt, OR, &Emitter::or_, x, y, x | y);
    pure_bin_instr_test(rt, OR, &Emitter::or_, y, x, y | x);
    y[3] = 10;
    pure_bin_instr_test(rt, OR, &Emitter::or_, x, y, x | y);
    pure_bin_instr_test(rt, OR, &Emitter::or_, y, x, y | x);
    y[1] = std::numeric_limits<uint64_t>::max();
    pure_bin_instr_test(rt, OR, &Emitter::or_, x, y, x | y);
    pure_bin_instr_test(rt, OR, &Emitter::or_, y, x, y | x);
    y[2] = uint64_t{1} << 63;
    pure_bin_instr_test(rt, OR, &Emitter::or_, x, y, x | y);
    pure_bin_instr_test(rt, OR, &Emitter::or_, y, x, y | x);
}

TEST(Emitter, or_identity_left)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, PUSH0, OR});
    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(10);
    emit.push(0);
    mov_literal_to_location_type(emit, 0, Emitter::LocationType::AvxReg);
    auto e = emit.get_stack().get(0);
    emit.or_();
    ASSERT_EQ(emit.get_stack().get(0), e);
}

TEST(Emitter, or_identity_right)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, PUSH0, AND});
    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(0);
    emit.push(10);
    mov_literal_to_location_type(emit, 1, Emitter::LocationType::AvxReg);
    auto e = emit.get_stack().get(1);
    emit.or_();
    ASSERT_EQ(emit.get_stack().get(0), e);
}

TEST(Emitter, xor_)
{
    asmjit::JitRuntime rt;
    pure_bin_instr_test(rt, XOR, &Emitter::xor_, 1, 3, 2);
    pure_bin_instr_test(rt, XOR, &Emitter::xor_, 3, 1, 2);
    pure_bin_instr_test(rt, XOR, &Emitter::xor_, 2, 1, 3);
    pure_bin_instr_test(rt, XOR, &Emitter::xor_, 1, 2, 3);
    pure_bin_instr_test(
        rt, XOR, &Emitter::xor_, {0, 1, 1, 0}, {0, 0, 1, 0}, {0, 1, 0, 0});
    pure_bin_instr_test(
        rt, XOR, &Emitter::xor_, {0, 0, 1, 0}, {0, 1, 1, 0}, {0, 1, 0, 0});
    pure_bin_instr_test(
        rt,
        XOR,
        &Emitter::xor_,
        std::numeric_limits<uint256_t>::max(),
        std::numeric_limits<uint256_t>::max() - 1,
        1);
    pure_bin_instr_test(
        rt,
        XOR,
        &Emitter::xor_,
        std::numeric_limits<uint256_t>::max() - 1,
        std::numeric_limits<uint256_t>::max(),
        1);
    pure_bin_instr_test(
        rt,
        XOR,
        &Emitter::xor_,
        std::numeric_limits<uint256_t>::max(),
        0,
        std::numeric_limits<uint256_t>::max());
    pure_bin_instr_test(
        rt,
        XOR,
        &Emitter::xor_,
        0,
        std::numeric_limits<uint256_t>::max(),
        std::numeric_limits<uint256_t>::max());
}

TEST(Emitter, xor_same)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, DUP1, XOR});
    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(0);
    emit.dup(1);
    mov_literal_to_location_type(emit, 0, Emitter::LocationType::AvxReg);
    auto e0 = emit.get_stack().get(0);
    auto e1 = emit.get_stack().get(1);
    ASSERT_EQ(e0, e1);
    emit.xor_();
    ASSERT_EQ(emit.get_stack().get(0)->literal()->value, uint256_t{0});
}

TEST(Emitter, eq)
{
    asmjit::JitRuntime rt;
    pure_bin_instr_test(rt, EQ, &Emitter::eq, 0, 0, 1);
    pure_bin_instr_test(rt, EQ, &Emitter::eq, 1, 1, 1);
    pure_bin_instr_test(rt, EQ, &Emitter::eq, 1, 0, 0);
    pure_bin_instr_test(rt, EQ, &Emitter::eq, 0, 1, 0);
    pure_bin_instr_test(rt, EQ, &Emitter::eq, {0, 1}, 0, 0);
    pure_bin_instr_test(rt, EQ, &Emitter::eq, 0, {0, 1}, 0);
    pure_bin_instr_test(rt, EQ, &Emitter::eq, {1, 1}, {0, 1}, 0);
    pure_bin_instr_test(rt, EQ, &Emitter::eq, {0, 1}, {1, 1}, 0);
    pure_bin_instr_test(rt, EQ, &Emitter::eq, {0, 0, 1, 0}, {0, 0, 1, 0}, 1);
    pure_bin_instr_test(rt, EQ, &Emitter::eq, {0, 0, 1, 0}, {0, 0, 3, 0}, 0);
    pure_bin_instr_test(rt, EQ, &Emitter::eq, {0, 0, 3, 0}, {0, 0, 1, 0}, 0);
    pure_bin_instr_test(
        rt,
        EQ,
        &Emitter::eq,
        std::numeric_limits<uint256_t>::max(),
        std::numeric_limits<uint256_t>::max() - 1,
        0);
    pure_bin_instr_test(
        rt,
        EQ,
        &Emitter::eq,
        std::numeric_limits<uint256_t>::max() - 1,
        std::numeric_limits<uint256_t>::max(),
        0);
    pure_bin_instr_test(
        rt,
        EQ,
        &Emitter::eq,
        std::numeric_limits<uint256_t>::max(),
        std::numeric_limits<uint256_t>::max(),
        1);
}

TEST(Emitter, eq_same)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, DUP1, EQ});
    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(0);
    emit.dup(1);
    mov_literal_to_location_type(emit, 0, Emitter::LocationType::AvxReg);
    auto e0 = emit.get_stack().get(0);
    auto e1 = emit.get_stack().get(1);
    ASSERT_EQ(e0, e1);
    emit.eq();
    ASSERT_EQ(emit.get_stack().get(0)->literal()->value, uint256_t{1});
}

TEST(Emitter, byte)
{
    asmjit::JitRuntime rt;
    pure_bin_instr_test(rt, BYTE, &Emitter::byte, 31, 1, 1);
    pure_bin_instr_test(
        rt,
        BYTE,
        &Emitter::byte,
        0,
        {0x3333333333333333,
         0x2222222222222222,
         0x1111111111111111,
         0x8877665544332211},
        0x88);
    pure_bin_instr_test(
        rt, BYTE, &Emitter::byte, 8, {0, 0, 0x8877665544332211, 0}, 0x88);
    pure_bin_instr_test(
        rt, BYTE, &Emitter::byte, 17, {0, 0x8877665544332211, 0, 0}, 0x77);
    pure_bin_instr_test(
        rt, BYTE, &Emitter::byte, 26, {0x8877665544332211, 0, 0, 0}, 0x66);
    pure_bin_instr_test(
        rt, BYTE, &Emitter::byte, 4, {0, 0, 0, 0x8877665544332211}, 0x44);
    pure_bin_instr_test(rt, BYTE, &Emitter::byte, 32, {-1, -1, -1, -1}, 0);
    pure_bin_instr_test(
        rt,
        BYTE,
        &Emitter::byte,
        std::numeric_limits<uint256_t>::max(),
        {-1, -1, -1, -1},
        0);
    uint256_t value{
        0x0807060504030201,
        0x100f0e0d0c0b0a09,
        0x8887868584838281,
        0x908f8e8d8c8b8a89};
    for (uint64_t i = 0; i <= 32; i += 1) {
        uint256_t indices[5] = {
            i,
            i | (uint256_t{1} << 65),
            i | (uint256_t{1} << 128),
            i | (uint256_t{1} << 224),
            i | (uint256_t{1} << 255)};
        for (auto const &i : indices) {
            pure_bin_instr_test(
                rt, BYTE, &Emitter::byte, i, value, runtime::byte(i, value));
        }
    }
}

TEST(Emitter, signextend)
{
    asmjit::JitRuntime rt;
    pure_bin_instr_test(
        rt, SIGNEXTEND, &Emitter::signextend, 0, 255, {-1, -1, -1, -1});
    pure_bin_instr_test(
        rt,
        SIGNEXTEND,
        &Emitter::signextend,
        1,
        0x8000,
        {-1 & ~0x7fff, -1, -1, -1});
    pure_bin_instr_test(
        rt, SIGNEXTEND, &Emitter::signextend, 1, 0x7000, 0x7000);
    pure_bin_instr_test(
        rt,
        SIGNEXTEND,
        &Emitter::signextend,
        25,
        {0, 0, 0, 0xff00},
        {0, 0, 0, ~0xff});
    pure_bin_instr_test(
        rt,
        SIGNEXTEND,
        &Emitter::signextend,
        25,
        {0, 0, 0, 0x7f00},
        {0, 0, 0, 0x7f00});
    pure_bin_instr_test(
        rt, SIGNEXTEND, &Emitter::signextend, 31, {0, 0, 0, -1}, {0, 0, 0, -1});
    pure_bin_instr_test(
        rt, SIGNEXTEND, &Emitter::signextend, 32, {0, 0, 0, -1}, {0, 0, 0, -1});

    uint256_t bits = {
        0x5555555555555555,
        0x5555555555555555,
        0x5555555555555555,
        0x5555555555555555}; // Alternating 0 and 1
    for (size_t i = 0; i <= 32; i++) {
        // 0x55 always has the sign bit off
        pure_bin_instr_test(
            rt, SIGNEXTEND, &Emitter::signextend, i, bits, signextend(i, bits));
        // 0xAA (~0x55) always has the sign bit on
        pure_bin_instr_test(
            rt,
            SIGNEXTEND,
            &Emitter::signextend,
            i,
            ~bits,
            signextend(i, ~bits));
    }
}

TEST(Emitter, shl)
{
    asmjit::JitRuntime rt;
    pure_bin_instr_test(rt, SHL, &Emitter::shl, 3, 1, 1 << 3);
    pure_bin_instr_test(
        rt,
        SHL,
        &Emitter::shl,
        255,
        1,
        {0, 0, 0, static_cast<uint64_t>(1) << 63});
    pure_bin_instr_test(
        rt,
        SHL,
        &Emitter::shl,
        63,
        ~static_cast<uint64_t>(0),
        {static_cast<uint64_t>(1) << 63,
         ~(static_cast<uint64_t>(1) << 63),
         0,
         0});
    pure_bin_instr_test(
        rt,
        SHL,
        &Emitter::shl,
        127,
        std::numeric_limits<uint256_t>::max(),
        {0,
         static_cast<uint64_t>(1) << 63,
         ~static_cast<uint64_t>(0),
         ~static_cast<uint64_t>(0)});
    pure_bin_instr_test(
        rt, SHL, &Emitter::shl, 256, std::numeric_limits<uint256_t>::max(), 0);
    pure_bin_instr_test(
        rt, SHL, &Emitter::shl, 257, std::numeric_limits<uint256_t>::max(), 0);

    uint256_t value{
        0x0807060504030201,
        0x100f0e0d0c0b0a09,
        0x8887868584838281,
        0x908f8e8d8c8b8a89};
    for (uint64_t i = 0; i <= 260; i += 4) {
        uint256_t shifts[5] = {
            i,
            i | (uint256_t{1} << 65),
            i | (uint256_t{1} << 128),
            i | (uint256_t{1} << 224),
            i | (uint256_t{1} << 255)};
        for (auto const &s : shifts) {
            pure_bin_instr_test(rt, SHL, &Emitter::shl, s, value, value << s);
        }
    }
}

TEST(Emitter, shl_identity)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, PUSH0, SHL});
    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(2);
    emit.push(0);
    mov_literal_to_location_type(emit, 0, Emitter::LocationType::GeneralReg);
    auto e = emit.get_stack().get(0);
    emit.shl();
    ASSERT_EQ(emit.get_stack().get(0), e);
}

TEST(Emitter, shl_0)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, PUSH0, SHL});
    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(0);
    emit.push(2);
    mov_literal_to_location_type(emit, 1, Emitter::LocationType::GeneralReg);
    auto e = emit.get_stack().get(0);
    emit.shl();
    ASSERT_EQ(emit.get_stack().get(0), e);
}

TEST(Emitter, shr)
{
    asmjit::JitRuntime rt;
    pure_bin_instr_test(rt, SHR, &Emitter::shr, 1, 2, 1);
    pure_bin_instr_test(
        rt,
        SHR,
        &Emitter::shr,
        63,
        {0, -1, 0, 0},
        {~static_cast<uint64_t>(0) - 1, 1, 0, 0});
    pure_bin_instr_test(
        rt,
        SHR,
        &Emitter::shr,
        127,
        std::numeric_limits<uint256_t>::max(),
        {~static_cast<uint64_t>(0), ~static_cast<uint64_t>(0), 1, 0});
    pure_bin_instr_test(
        rt, SHR, &Emitter::shr, 256, std::numeric_limits<uint256_t>::max(), 0);
    pure_bin_instr_test(
        rt, SHR, &Emitter::shr, 257, std::numeric_limits<uint256_t>::max(), 0);

    uint256_t value{
        0x0807060504030201,
        0x100f0e0d0c0b0a09,
        0x8887868584838281,
        0x908f8e8d8c8b8a89};
    for (uint64_t i = 0; i <= 260; i += 4) {
        uint256_t shifts[5] = {
            i,
            i | (uint256_t{1} << 65),
            i | (uint256_t{1} << 128),
            i | (uint256_t{1} << 224),
            i | (uint256_t{1} << 255)};
        for (auto const &s : shifts) {
            pure_bin_instr_test(rt, SHR, &Emitter::shr, s, value, value >> s);
        }
    }
}

TEST(Emitter, shr_identity)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, PUSH0, SHR});
    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(2);
    emit.push(0);
    mov_literal_to_location_type(emit, 0, Emitter::LocationType::GeneralReg);
    auto e = emit.get_stack().get(0);
    emit.shr();
    ASSERT_EQ(emit.get_stack().get(0), e);
}

TEST(Emitter, shr_0)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, PUSH0, SHR});
    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(0);
    emit.push(2);
    mov_literal_to_location_type(emit, 1, Emitter::LocationType::GeneralReg);
    auto e = emit.get_stack().get(0);
    emit.shr();
    ASSERT_EQ(emit.get_stack().get(0), e);
}

TEST(Emitter, sar)
{
    asmjit::JitRuntime rt;
    pure_bin_instr_test(rt, SAR, &Emitter::sar, 1, 2, 1);
    pure_bin_instr_test(
        rt,
        SAR,
        &Emitter::sar,
        63,
        {0, -1, 0, 0},
        {~static_cast<uint64_t>(0) - 1, 1, 0, 0});
    pure_bin_instr_test(
        rt,
        SAR,
        &Emitter::sar,
        63,
        {0, -1, 0, -1},
        {~static_cast<uint64_t>(0) - 1,
         1,
         ~static_cast<uint64_t>(0) - 1,
         ~static_cast<uint64_t>(0)});
    pure_bin_instr_test(
        rt,
        SAR,
        &Emitter::sar,
        127,
        std::numeric_limits<uint256_t>::max(),
        std::numeric_limits<uint256_t>::max());
    pure_bin_instr_test(
        rt,
        SAR,
        &Emitter::sar,
        256,
        std::numeric_limits<uint256_t>::max(),
        std::numeric_limits<uint256_t>::max());
    pure_bin_instr_test(
        rt,
        SAR,
        &Emitter::sar,
        257,
        std::numeric_limits<uint256_t>::max(),
        std::numeric_limits<uint256_t>::max());
    pure_bin_instr_test(
        rt,
        SAR,
        &Emitter::sar,
        256,
        {0, 0, 0, ~(static_cast<uint64_t>(1) << 63)},
        0);
    pure_bin_instr_test(
        rt,
        SAR,
        &Emitter::sar,
        257,
        {0, 0, 0, ~(static_cast<uint64_t>(1) << 63)},
        0);

    uint256_t value{
        0x0807060504030201,
        0x100f0e0d0c0b0a09,
        0x8887868584838281,
        0x908f8e8d8c8b8a89};
    for (uint64_t i = 0; i <= 260; i += 4) {
        uint256_t shifts[5] = {
            i,
            i | (uint256_t{1} << 65),
            i | (uint256_t{1} << 128),
            i | (uint256_t{1} << 224),
            i | (uint256_t{1} << 255)};
        for (auto const &s : shifts) {
            pure_bin_instr_test(
                rt, SAR, &Emitter::sar, s, value, sar(s, value));
            pure_bin_instr_test(
                rt, SAR, &Emitter::sar, s, ~value, sar(s, ~value));
        }
    }
}

TEST(Emitter, sar_identity)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, PUSH0, SAR});
    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(2);
    emit.push(0);
    mov_literal_to_location_type(emit, 0, Emitter::LocationType::GeneralReg);
    auto e = emit.get_stack().get(0);
    emit.sar();
    ASSERT_EQ(emit.get_stack().get(0), e);
}

TEST(Emitter, sar_0)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, PUSH0, SAR});
    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(0);
    emit.push(2);
    mov_literal_to_location_type(emit, 1, Emitter::LocationType::GeneralReg);
    auto e = emit.get_stack().get(0);
    emit.sar();
    ASSERT_EQ(emit.get_stack().get(0), e);
}

TEST(Emitter, sar_max)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, PUSH0, SAR});
    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(std::numeric_limits<uint256_t>::max());
    emit.push(2);
    mov_literal_to_location_type(emit, 1, Emitter::LocationType::GeneralReg);
    auto e = emit.get_stack().get(0);
    emit.sar();
    ASSERT_EQ(emit.get_stack().get(0), e);
}

TEST(Emitter, call_runtime_pure)
{
    asmjit::JitRuntime rt;
    pure_bin_instr_test(
        rt,
        DIV,
        [](Emitter &emit) { emit.udiv<EvmChain<EVMC_FRONTIER>>(0); },
        1000,
        4,
        250);
}

TEST(Emitter, call_runtime_impl)
{
    asmjit::JitRuntime rt;
    pure_bin_instr_test(
        rt,
        EXP,
        [](Emitter &emit) { emit.exp<EvmChain<EVMC_FRONTIER>>(0); },
        10,
        20,
        100000000000000000000_u256);
}

TEST(Emitter, call_runtime_12_arg_fun)
{
    static_assert(Emitter::MAX_RUNTIME_ARGS == 12);
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(
        {PUSH0,
         PUSH0,
         PUSH0,
         PUSH0,
         PUSH0,
         PUSH0,
         PUSH0,
         PUSH0,
         PUSH0,
         PUSH0,
         CALL,
         RETURN});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    for (int32_t i = 0; i < 10; ++i) {
        emit.push(i);
        mov_literal_to_location_type(emit, i, Emitter::LocationType::AvxReg);
    }
    emit.call_runtime(10, true, runtime_test_12_arg_fun);
    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context(10);
    auto const &ret = ctx.result;

    auto stack_memory = test_stack_memory();
    entry(&ctx, stack_memory.get());

    ASSERT_EQ(uint256_t::load_le(ret.offset), 5);
    ASSERT_EQ(uint256_t::load_le(ret.size), 0);
}

TEST(Emitter, call_runtime_11_arg_fun)
{
    static_assert(Emitter::MAX_RUNTIME_ARGS == 12);
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(
        {PUSH0,
         PUSH0,
         PUSH0,
         PUSH0,
         PUSH0,
         PUSH0,
         PUSH0,
         PUSH0,
         PUSH0,
         CALL,
         RETURN});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    for (int32_t i = 0; i < 9; ++i) {
        emit.push(i);
        mov_literal_to_location_type(emit, i, Emitter::LocationType::AvxReg);
    }
    emit.call_runtime(9, true, runtime_test_11_arg_fun);
    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context(10);
    auto const &ret = ctx.result;

    auto stack_memory = test_stack_memory();
    entry(&ctx, stack_memory.get());

    ASSERT_EQ(uint256_t::load_le(ret.offset), 5);
    ASSERT_EQ(uint256_t::load_le(ret.size), 0);
}

TEST(Emitter, runtime_exit)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(
        {PUSH0, PUSH0, PUSH0, EXP, RETURN});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(0);
    emit.push(300);
    emit.push(10);
    emit.call_runtime(9, true, runtime::exp<EvmChain<EVMC_SPURIOUS_DRAGON>>);
    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context(99);
    auto const &ret = ctx.result;

    auto stack_memory = test_stack_memory();
    entry(&ctx, stack_memory.get());

    ASSERT_EQ(ret.status, runtime::StatusCode::OutOfGas);
}

TEST(Emitter, address)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({ADDRESS, ADDRESS});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.address();
    emit.address();
    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    for (uint8_t i = 0; i < 20; ++i) {
        ctx.env.recipient.bytes[19 - i] = i + 1;
    }
    uint256_t result;
    uint8_t *result_bytes = result.as_bytes();
    for (uint8_t i = 0; i < 20; ++i) {
        result_bytes[i] = i + 1;
    }

    entry(&ctx, nullptr);

    ASSERT_EQ(uint256_t::load_le(ret.offset), result);
    ASSERT_EQ(uint256_t::load_le(ret.size), result);
}

TEST(Emitter, origin)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({ORIGIN, ORIGIN});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.origin();
    emit.origin();
    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    ctx.env.tx_context.tx_origin.bytes[18] = 2;

    entry(&ctx, nullptr);

    ASSERT_EQ(uint256_t::load_le(ret.offset), 0x200);
    ASSERT_EQ(uint256_t::load_le(ret.size), 0x200);
}

TEST(Emitter, gasprice)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({GASPRICE, GASPRICE});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.gasprice();
    emit.gasprice();
    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    ctx.env.tx_context.tx_gas_price.bytes[30] = 3;

    entry(&ctx, nullptr);

    ASSERT_EQ(uint256_t::load_le(ret.offset), 0x300);
    ASSERT_EQ(uint256_t::load_le(ret.size), 0x300);
}

TEST(Emitter, gaslimit)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({GASLIMIT, GASLIMIT});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.gaslimit();
    emit.gaslimit();
    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    ctx.env.tx_context.block_gas_limit = 4;

    entry(&ctx, nullptr);

    ASSERT_EQ(uint256_t::load_le(ret.offset), 4);
    ASSERT_EQ(uint256_t::load_le(ret.size), 4);
}

TEST(Emitter, coinbase)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({COINBASE, COINBASE});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.coinbase();
    emit.coinbase();
    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    ctx.env.tx_context.block_coinbase.bytes[18] = 5;

    entry(&ctx, nullptr);

    ASSERT_EQ(uint256_t::load_le(ret.offset), 0x500);
    ASSERT_EQ(uint256_t::load_le(ret.size), 0x500);
}

TEST(Emitter, timestamp)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({TIMESTAMP, TIMESTAMP});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.timestamp();
    emit.timestamp();
    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    ctx.env.tx_context.block_timestamp = 6;

    entry(&ctx, nullptr);

    ASSERT_EQ(uint256_t::load_le(ret.offset), 6);
    ASSERT_EQ(uint256_t::load_le(ret.size), 6);
}

TEST(Emitter, number)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({NUMBER, NUMBER});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.number();
    emit.number();
    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    ctx.env.tx_context.block_number = 7;

    entry(&ctx, nullptr);

    ASSERT_EQ(uint256_t::load_le(ret.offset), 7);
    ASSERT_EQ(uint256_t::load_le(ret.size), 7);
}

TEST(Emitter, prevrandao)
{
    auto ir =
        basic_blocks::BasicBlocksIR::unsafe_from({DIFFICULTY, DIFFICULTY});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.prevrandao();
    emit.prevrandao();
    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    ctx.env.tx_context.block_prev_randao.bytes[30] = 8;

    entry(&ctx, nullptr);

    ASSERT_EQ(uint256_t::load_le(ret.offset), 0x800);
    ASSERT_EQ(uint256_t::load_le(ret.size), 0x800);
}

TEST(Emitter, chainid)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({CHAINID, CHAINID});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.chainid();
    emit.chainid();
    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    ctx.env.tx_context.chain_id.bytes[30] = 9;

    entry(&ctx, nullptr);

    ASSERT_EQ(uint256_t::load_le(ret.offset), 0x900);
    ASSERT_EQ(uint256_t::load_le(ret.size), 0x900);
}

TEST(Emitter, basefee)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({BASEFEE, BASEFEE});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.basefee();
    emit.basefee();
    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    ctx.env.tx_context.block_base_fee.bytes[30] = 0xa;

    entry(&ctx, nullptr);

    ASSERT_EQ(uint256_t::load_le(ret.offset), 0xa00);
    ASSERT_EQ(uint256_t::load_le(ret.size), 0xa00);
}

TEST(Emitter, blobbasefee)
{
    auto ir =
        basic_blocks::BasicBlocksIR::unsafe_from({BLOBBASEFEE, BLOBBASEFEE});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.blobbasefee();
    emit.blobbasefee();
    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    ctx.env.tx_context.blob_base_fee.bytes[30] = 0xb;

    entry(&ctx, nullptr);

    ASSERT_EQ(uint256_t::load_le(ret.offset), 0xb00);
    ASSERT_EQ(uint256_t::load_le(ret.size), 0xb00);
}

TEST(Emitter, caller)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({CALLER, CALLER});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.caller();
    emit.caller();
    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    for (uint8_t i = 0; i < 20; ++i) {
        ctx.env.sender.bytes[19 - i] = i + 1;
    }
    uint256_t result;
    uint8_t *result_bytes = result.as_bytes();
    for (uint8_t i = 0; i < 20; ++i) {
        result_bytes[i] = i + 1;
    }

    entry(&ctx, nullptr);

    ASSERT_EQ(uint256_t::load_le(ret.offset), result);
    ASSERT_EQ(uint256_t::load_le(ret.size), result);
}

TEST(Emitter, calldatasize)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(
        {CALLDATASIZE, CALLDATASIZE, RETURN});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.calldatasize();
    emit.calldatasize();
    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;
    ctx.env.input_data_size = 5;

    entry(&ctx, nullptr);

    ASSERT_EQ(uint256_t::load_le(ret.offset), 5);
    ASSERT_EQ(uint256_t::load_le(ret.size), 5);
}

TEST(Emitter, returndatasize)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(
        {RETURNDATASIZE, RETURNDATASIZE, RETURN});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.returndatasize();
    emit.returndatasize();
    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;
    ctx.env.return_data_size = 6;

    entry(&ctx, nullptr);

    ASSERT_EQ(uint256_t::load_le(ret.offset), 6);
    ASSERT_EQ(uint256_t::load_le(ret.size), 6);
}

TEST(Emitter, msize)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({MSIZE, MSIZE, RETURN});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.msize();
    emit.msize();
    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;
    ctx.memory.size = 0xffffffff;

    entry(&ctx, nullptr);

    ASSERT_EQ(uint256_t::load_le(ret.offset), 0xffffffff);
    ASSERT_EQ(uint256_t::load_le(ret.size), 0xffffffff);
}

TEST(Emitter, MemoryInstructions)
{
    auto run_mstore_mstore8_mload = [](basic_blocks::BasicBlocksIR const &ir,
                                       unsigned used_reg_count,
                                       bool dup,
                                       bool m8,
                                       Emitter::LocationType store_loc1,
                                       Emitter::LocationType store_loc2,
                                       Emitter::LocationType load_loc) {
        asmjit::JitRuntime rt;
        TestEmitter emit{rt, ir.codesize};
        (void)emit.begin_new_block(ir.blocks()[0]);

        int32_t top_ix = -1;

        for (unsigned i = 0; i < used_reg_count; ++i) {
            ++top_ix;
            emit.push(0);
            mov_literal_to_location_type(
                emit, top_ix, Emitter::LocationType::GeneralReg);
        }

        ++top_ix;
        emit.push(uint256_t{1, 2, 3, 4});
        mov_literal_to_location_type(emit, top_ix, store_loc1);

        ++top_ix;
        emit.push(0);
        mov_literal_to_location_type(emit, top_ix, store_loc2);

        if (dup) {
            ++top_ix;
            emit.dup(2);
            ++top_ix;
            emit.dup(2);
        }

        top_ix -= 2;
        if (m8) {
            emit.mstore8();
        }
        else {
            emit.mstore();
        }

        for (unsigned i = 0; i < used_reg_count; ++i) {
            ++top_ix;
            emit.push(0);
            mov_literal_to_location_type(
                emit, top_ix, Emitter::LocationType::GeneralReg);
        }

        ++top_ix;
        emit.push(0);
        mov_literal_to_location_type(emit, top_ix, load_loc);

        if (dup) {
            emit.dup(1);
        }

        emit.mload();

        emit.dup(1);
        emit.return_();

        entrypoint_t entry = emit.finish_contract(rt);
        auto ctx = test_context();
        auto const &ret = ctx.result;

        auto stack_memory = test_stack_memory();
        entry(&ctx, stack_memory.get());

        if (m8) {
            ASSERT_EQ(
                uint256_t::load_le(ret.offset),
                uint256_t(0, 0, 0, uint64_t{1} << 56));
            ASSERT_EQ(
                uint256_t::load_le(ret.size),
                uint256_t(0, 0, 0, uint64_t{1} << 56));
        }
        else {
            ASSERT_EQ(uint256_t::load_le(ret.offset), uint256_t(1, 2, 3, 4));
            ASSERT_EQ(uint256_t::load_le(ret.size), uint256_t(1, 2, 3, 4));
        }
    };

    for (int i = 0; i < 16; ++i) {
        std::vector<uint8_t> bytecode;
        if (i & 4) {
            // with dup
            bytecode = {
                PUSH0,
                PUSH0,
                PUSH0,
                PUSH1,
                1,
                PUSH0,
                DUP2,
                DUP2,
                MSTORE,
                PUSH0,
                PUSH0,
                PUSH0,
                PUSH0,
                DUP1,
                MLOAD,
                DUP1,
                RETURN};
        }
        else {
            // without dup
            bytecode = {
                PUSH0,
                PUSH0,
                PUSH0,
                PUSH1,
                1,
                PUSH0,
                MSTORE,
                PUSH0,
                PUSH0,
                PUSH0,
                PUSH0,
                MLOAD,
                DUP1,
                RETURN};
        }
        auto ir = basic_blocks::BasicBlocksIR::unsafe_from(bytecode);

        for (auto sloc1 : all_locations) {
            for (auto sloc2 : all_locations) {
                for (auto lloc : all_locations) {
                    run_mstore_mstore8_mload(
                        ir, i & 3, i & 4, i & 8, sloc1, sloc2, lloc);
                }
            }
        }
    }
}

TEST(Emitter, mstore_not_bounded_by_bits)
{
    std::vector<uint8_t> bytecode{PUSH0, PUSH0, MSTORE};

    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(bytecode);

    for (auto loc : all_locations) {
        asmjit::JitRuntime rt;
        TestEmitter emit{rt, ir.codesize};
        (void)emit.begin_new_block(ir.blocks().at(0));

        emit.push(0);
        emit.push((uint256_t{1} << runtime::Memory::offset_bits) - 1);
        mov_literal_to_location_type(emit, 1, loc);

        emit.mstore();
        emit.stop();

        entrypoint_t entry = emit.finish_contract(rt);
        auto ctx = test_context();
        auto const &ret = ctx.result;
        auto stack_memory = test_stack_memory();
        entry(&ctx, stack_memory.get());

        ASSERT_EQ(ret.status, runtime::StatusCode::Success);
    }

    for (auto loc : all_locations) {
        asmjit::JitRuntime rt;
        TestEmitter emit{rt, ir.codesize};
        (void)emit.begin_new_block(ir.blocks().at(0));

        emit.push(0);
        emit.push(uint256_t{1} << runtime::Memory::offset_bits);
        mov_literal_to_location_type(emit, 1, loc);

        emit.mstore();
        emit.stop();

        entrypoint_t entry = emit.finish_contract(rt);
        auto ctx = test_context();
        auto const &ret = ctx.result;
        auto stack_memory = test_stack_memory();
        entry(&ctx, stack_memory.get());

        ASSERT_EQ(ret.status, runtime::StatusCode::Error);
    }
}

TEST(Emitter, mload_not_bounded_by_bits)
{
    std::vector<uint8_t> bytecode{PUSH0, MLOAD};

    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(bytecode);

    for (auto loc : all_locations) {
        asmjit::JitRuntime rt;
        TestEmitter emit{rt, ir.codesize};
        (void)emit.begin_new_block(ir.blocks().at(0));

        emit.push((uint256_t{1} << runtime::Memory::offset_bits) - 1);
        mov_literal_to_location_type(emit, 0, loc);

        emit.mload();
        emit.stop();

        entrypoint_t entry = emit.finish_contract(rt);
        auto ctx = test_context();
        auto const &ret = ctx.result;
        auto stack_memory = test_stack_memory();
        entry(&ctx, stack_memory.get());

        ASSERT_EQ(ret.status, runtime::StatusCode::Success);
    }

    for (auto loc : all_locations) {
        asmjit::JitRuntime rt;
        TestEmitter emit{rt, ir.codesize};
        (void)emit.begin_new_block(ir.blocks().at(0));

        emit.push(uint256_t{1} << runtime::Memory::offset_bits);
        mov_literal_to_location_type(emit, 0, loc);

        emit.mload();
        emit.stop();

        entrypoint_t entry = emit.finish_contract(rt);
        auto ctx = test_context();
        auto const &ret = ctx.result;
        auto stack_memory = test_stack_memory();
        entry(&ctx, stack_memory.get());

        ASSERT_EQ(ret.status, runtime::StatusCode::Error);
    }
}

TEST(Emitter, calldataload)
{
    auto ctx = test_context();
    uint8_t calldata[33];
    for (uint8_t i = 0; i < sizeof(calldata); ++i) {
        calldata[i] = i + 1;
    }
    ctx.env.input_data = calldata;
    ctx.env.input_data_size = sizeof(calldata);

    for (auto loc : all_locations) {
        for (uint8_t used_regs = 0; used_regs <= 3; ++used_regs) {
            for (uint8_t offset = 0; offset <= sizeof(calldata); ++offset) {
                std::vector<uint8_t> bytecode;
                for (uint8_t i = 0; i < used_regs; ++i) {
                    bytecode.push_back(PUSH0);
                }
                bytecode.push_back(PUSH0);
                bytecode.push_back(DUP1);
                bytecode.push_back(CALLDATALOAD);
                bytecode.push_back(PUSH0);
                bytecode.push_back(CALLDATALOAD);
                bytecode.push_back(RETURN);

                auto const ir =
                    basic_blocks::BasicBlocksIR::unsafe_from(bytecode);

                asmjit::JitRuntime rt;
                TestEmitter emit{rt, ir.codesize};
                (void)emit.begin_new_block(ir.blocks()[0]);

                int32_t top_ix = -1;
                for (uint8_t i = 0; i < used_regs; ++i) {
                    ++top_ix;
                    emit.push(0);
                    mov_literal_to_location_type(
                        emit, top_ix, Emitter::LocationType::GeneralReg);
                }

                ++top_ix;
                emit.push(offset);
                ++top_ix;
                emit.dup(1);
                mov_literal_to_location_type(emit, top_ix, loc);
                emit.calldataload();

                ++top_ix;
                emit.push(offset);
                mov_literal_to_location_type(emit, top_ix, loc);
                emit.calldataload();
                emit.return_();

                entrypoint_t entry = emit.finish_contract(rt);
                auto const &ret = ctx.result;

                auto stack_memory = test_stack_memory();
                entry(&ctx, stack_memory.get());

                uint256_t expected;
                std::memcpy(
                    expected.as_bytes(),
                    calldata + offset,
                    std::min(sizeof(expected), sizeof(calldata) - offset));

                ASSERT_EQ(uint256_t::load_le(ret.offset), expected.to_be());
                ASSERT_EQ(uint256_t::load_le(ret.size), expected.to_be());
            }
        }
    }
}

TEST(Emitter, calldataload_not_bounded_by_bits)
{
    std::vector<uint8_t> bytecode{PUSH0, CALLDATALOAD, DUP1, RETURN};

    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(bytecode);

    static constexpr uint32_t input_data_size = (uint64_t{1} << 32) - 1;
    std::unique_ptr<uint8_t[]> input_data{new uint8_t[input_data_size]};
    input_data[input_data_size - 1] = 0xff;

    for (auto loc : all_locations) {
        asmjit::JitRuntime rt;
        TestEmitter emit{rt, ir.codesize};
        (void)emit.begin_new_block(ir.blocks().at(0));

        emit.push(input_data_size - 1);
        mov_literal_to_location_type(emit, 0, loc);

        emit.calldataload();
        emit.dup(1);
        emit.return_();

        entrypoint_t entry = emit.finish_contract(rt);
        auto ctx = test_context();
        ctx.env.input_data = input_data.get();
        ctx.env.input_data_size = input_data_size;
        auto const &ret = ctx.result;
        auto stack_memory = test_stack_memory();
        entry(&ctx, stack_memory.get());

        ASSERT_EQ(ret.status, runtime::StatusCode::Success);
        ASSERT_EQ(uint256_t::load_le(ret.offset), uint256_t{0xff} << 248);
        ASSERT_EQ(uint256_t::load_le(ret.size), uint256_t{0xff} << 248);
    }

    for (auto loc : all_locations) {
        asmjit::JitRuntime rt;
        TestEmitter emit{rt, ir.codesize};
        (void)emit.begin_new_block(ir.blocks().at(0));

        emit.push(input_data_size);
        mov_literal_to_location_type(emit, 0, loc);

        emit.calldataload();
        emit.dup(1);
        emit.return_();

        entrypoint_t entry = emit.finish_contract(rt);
        auto ctx = test_context();
        ctx.env.input_data = input_data.get();
        ctx.env.input_data_size = input_data_size;
        auto const &ret = ctx.result;
        auto stack_memory = test_stack_memory();
        entry(&ctx, stack_memory.get());

        ASSERT_EQ(ret.status, runtime::StatusCode::Success);
        ASSERT_EQ(uint256_t::load_le(ret.offset), 0);
        ASSERT_EQ(uint256_t::load_le(ret.size), 0);
    }

    for (auto loc : all_locations) {
        asmjit::JitRuntime rt;
        TestEmitter emit{rt, ir.codesize};
        (void)emit.begin_new_block(ir.blocks().at(0));

        emit.push(uint256_t{input_data_size} + 1);
        mov_literal_to_location_type(emit, 0, loc);

        emit.calldataload();
        emit.dup(1);
        emit.return_();

        entrypoint_t entry = emit.finish_contract(rt);
        auto ctx = test_context();
        ctx.env.input_data = input_data.get();
        ctx.env.input_data_size = input_data_size;
        auto const &ret = ctx.result;
        auto stack_memory = test_stack_memory();
        entry(&ctx, stack_memory.get());

        ASSERT_EQ(ret.status, runtime::StatusCode::Success);
        ASSERT_EQ(uint256_t::load_le(ret.offset), 0);
        ASSERT_EQ(uint256_t::load_le(ret.size), 0);
    }
}

TEST(Emitter, gas)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({GAS, GAS, RETURN});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.gas(2);
    emit.gas(2);
    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context(10);
    auto const &ret = ctx.result;

    entry(&ctx, nullptr);

    ASSERT_EQ(uint256_t::load_le(ret.offset), 12);
    ASSERT_EQ(uint256_t::load_le(ret.size), 12);
}

TEST(Emitter, callvalue)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({CALLVALUE, CALLVALUE});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.callvalue();
    emit.callvalue();
    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;

    for (uint8_t i = 0; i < 32; ++i) {
        ctx.env.value.bytes[31 - i] = i + 1;
    }
    uint256_t result;
    uint8_t *result_bytes = result.as_bytes();
    for (uint8_t i = 0; i < 32; ++i) {
        result_bytes[i] = i + 1;
    }

    entry(&ctx, nullptr);

    ASSERT_EQ(uint256_t::load_le(ret.offset), result);
    ASSERT_EQ(uint256_t::load_le(ret.size), result);
}

TEST(Emitter, iszero)
{
    asmjit::JitRuntime rt;
    pure_una_instr_test(rt, ISZERO, &Emitter::iszero, 0, 1);
    pure_una_instr_test(rt, ISZERO, &Emitter::iszero, 1, 0);
    pure_una_instr_test(rt, ISZERO, &Emitter::iszero, -1, 0);
    pure_una_instr_test(
        rt, ISZERO, &Emitter::iszero, std::numeric_limits<uint256_t>::max(), 0);
}

TEST(Emitter, not_)
{
    asmjit::JitRuntime rt;
    pure_una_instr_test(
        rt, NOT, &Emitter::not_, 0, std::numeric_limits<uint256_t>::max());
    pure_una_instr_test(
        rt, NOT, &Emitter::not_, 1, std::numeric_limits<uint256_t>::max() - 1);
    pure_una_instr_test(rt, NOT, &Emitter::not_, -1, {0, -1, -1, -1});
    pure_una_instr_test(
        rt, NOT, &Emitter::not_, std::numeric_limits<uint256_t>::max(), 0);
}

TEST(Emitter, jump)
{
    for (auto loc1 : all_locations) {
        for (auto loc2 : all_locations) {
            for (auto loc_dest : all_locations) {
                jump_test(loc1, loc2, loc_dest, false);
                jump_test(loc1, loc2, loc_dest, true);
            }
        }
    }
}

TEST(Emitter, jump_bad_jumpdest)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, JUMP});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(0);
    emit.jump();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;
    auto stack_memory = test_stack_memory();
    entry(&ctx, stack_memory.get());

    ASSERT_EQ(ret.status, runtime::StatusCode::Error);
}

TEST(Emitter, jumpi)
{
    asmjit::JitRuntime rt;
    for (auto loc1 : all_locations) {
        for (auto loc2 : all_locations) {
            for (auto loc_cond : all_locations) {
                for (auto loc_dest : all_locations) {
                    for (int8_t i = 0; i < 32; ++i) {
                        jumpi_test(
                            rt,
                            loc1,
                            loc2,
                            loc_cond,
                            loc_dest,
                            i & 1,
                            i & 2,
                            i & 4,
                            i & 8,
                            i & 16);
                    }
                }
            }
        }
    }
}

TEST(Emitter, jumpi_bad_jumpdest)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, PUSH0, JUMPI});

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);
    emit.push(1);
    emit.push(1);
    emit.jumpi(ir.blocks().at(1));

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;
    auto stack_memory = test_stack_memory();
    entry(&ctx, stack_memory.get());

    ASSERT_EQ(ret.status, runtime::StatusCode::Error);
}

TEST(Emitter, block_epilogue)
{
    for (auto loc1 : all_locations) {
        if (loc1 == Emitter::LocationType::Literal) {
            continue;
        }
        for (auto loc2 : all_locations) {
            if (loc2 == Emitter::LocationType::Literal) {
                continue;
            }
            for (auto loc3 : all_locations) {
                for (auto loc4 : all_locations) {
                    for (auto loc5 : all_locations) {
                        block_epilogue_test(loc1, loc2, loc3, loc4, loc5);
                    }
                }
            }
        }
    }
}

TEST(Emitter, SpillGeneralRegister)
{
    std::vector<uint8_t> bytecode;
    for (size_t i = 0; i <= GENERAL_REG_COUNT; ++i) {
        bytecode.push_back(ADDRESS);
    }
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(bytecode);

    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);

    Stack &stack = emit.get_stack();

    for (int32_t i = 0; i < GENERAL_REG_COUNT; ++i) {
        emit.address();
        ASSERT_TRUE(stack.get(i)->general_reg().has_value());
    }

    emit.address();
    ASSERT_TRUE(stack.get(GENERAL_REG_COUNT)->general_reg().has_value());

    size_t reg_count = 0;
    for (int32_t i = 0; i <= GENERAL_REG_COUNT; ++i) {
        reg_count += stack.get(i)->general_reg().has_value();
        if (!stack.get(i)->general_reg().has_value()) {
            ASSERT_TRUE(stack.get(i)->stack_offset().has_value());
        }
    }
    ASSERT_EQ(reg_count, GENERAL_REG_COUNT);
}

TEST(Emitter, SpillAvxRegister)
{
    std::vector<uint8_t> bytecode;
    for (size_t i = 0; i <= 3 + AVX_REG_COUNT; ++i) {
        bytecode.push_back(CALLVALUE);
    }
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(bytecode);

    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks()[0]);

    Stack &stack = emit.get_stack();

    for (int i = 0; i < 3; ++i) {
        emit.callvalue();
        ASSERT_TRUE(stack.get(i)->general_reg().has_value());
        ASSERT_FALSE(stack.get(i)->avx_reg().has_value());
    }
    for (int32_t i = 3; i < 3 + AVX_REG_COUNT; ++i) {
        emit.callvalue();
        ASSERT_TRUE(stack.get(i)->avx_reg().has_value());
    }

    emit.callvalue();
    ASSERT_TRUE(stack.get(AVX_REG_COUNT)->avx_reg().has_value());

    size_t avx_count = 0;
    for (int32_t i = 3; i <= 3 + AVX_REG_COUNT; ++i) {
        avx_count += stack.get(i)->avx_reg().has_value();
        if (!stack.get(i)->avx_reg().has_value()) {
            ASSERT_TRUE(stack.get(i)->stack_offset().has_value());
        }
    }
    ASSERT_EQ(avx_count, AVX_REG_COUNT);
}

TEST(Emitter, QuadraticCompileTimeRegression)
{
    std::vector<uint8_t> bytecode;
    for (int i = 0; i < 1000; ++i) {
        bytecode.push_back(CODESIZE);
    }
    for (int i = 0; i < 500; ++i) {
        bytecode.push_back(CALLVALUE);
        bytecode.push_back(CALLVALUE);
        bytecode.push_back(JUMPI);
    }

    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(bytecode);

    asmjit::JitRuntime const rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks().at(0));

    for (int i = 0; i < 1000; ++i) {
        emit.codesize();
    }
    for (size_t i = 0; i < 500; ++i) {
        emit.callvalue();
        emit.callvalue();
        emit.jumpi(ir.blocks().at(i + 1));
        (void)emit.begin_new_block(ir.blocks().at(i + 1));
    }
    emit.stop();

    ASSERT_LT(emit.estimate_size(), 256 * 1024);
}

TEST(Emitter, SpillInMovGeneralRegToAvxRegRegression)
{
    std::vector<uint8_t> bytecode;
    for (size_t i = 0; i < 17; ++i) {
        bytecode.push_back(PUSH0);
    }

    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(bytecode);

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks().at(0));

    Stack &stack = emit.get_stack();

    for (int32_t i = 0; i < 16; ++i) {
        emit.push(i);
        ASSERT_TRUE(stack.has_free_avx_reg());
        mov_literal_to_location_type(emit, i, Emitter::LocationType::AvxReg);
    }
    ASSERT_FALSE(stack.has_free_avx_reg());

    emit.push(16);
    mov_literal_to_location_type(emit, 16, Emitter::LocationType::GeneralReg);
    emit.mov_stack_index_to_avx_reg(16);
    (void)stack.spill_general_reg(stack.get(16));

    emit.return_();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;
    auto stack_memory = test_stack_memory();
    entry(&ctx, stack_memory.get());

    ASSERT_EQ(ret.status, runtime::StatusCode::Success);
    ASSERT_EQ(uint256_t::load_le(ret.offset), 16);
    ASSERT_EQ(uint256_t::load_le(ret.size), 15);
}

TEST(Emitter, ReleaseSrcAndDestRegression)
{
    std::vector<uint8_t> bytecode{ADDRESS, DUP1, AND, STOP};

    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(bytecode);

    asmjit::JitRuntime rt;
    TestEmitter emit{rt, ir.codesize};
    (void)emit.begin_new_block(ir.blocks().at(0));

    Stack &stack = emit.get_stack();

    emit.address();
    emit.mov_stack_index_to_avx_reg(0);
    (void)stack.spill_general_reg(stack.get(0));
    ASSERT_FALSE(stack.get(0)->literal().has_value());
    ASSERT_FALSE(stack.get(0)->stack_offset().has_value());
    ASSERT_FALSE(stack.get(0)->general_reg().has_value());
    ASSERT_TRUE(stack.get(0)->avx_reg().has_value());

    emit.dup(1);
    emit.and_();
    emit.stop();

    entrypoint_t entry = emit.finish_contract(rt);
    auto ctx = test_context();
    auto const &ret = ctx.result;
    auto stack_memory = test_stack_memory();
    entry(&ctx, stack_memory.get());

    ASSERT_EQ(ret.status, runtime::StatusCode::Success);
}

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
#include <category/vm/compiler/ir/bound_inference.hpp>
#include <category/vm/compiler/ir/instruction.hpp>
#include <category/vm/compiler/ir/x86.hpp>
#include <category/vm/compiler/ir/x86/emitter.hpp>
#include <category/vm/compiler/ir/x86/types.hpp>
#include <category/vm/compiler/types.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/runtime/bin.hpp>

#include <asmjit/core/jitruntime.h>

#include <quill/Quill.h>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <variant>

using namespace monad::vm::compiler;
using namespace monad::vm::compiler::basic_blocks;
using namespace monad::vm::compiler::native;
using namespace monad::vm::interpreter;

namespace
{
    using monad::Traits;

#ifdef COMPARE_BOUND_ANALYSIS
    #define PRE_EMIT_HOOK(instr) \
        auto const result_bound = \
                bound_inference::compute_result_bound<instr, traits>(emit);

    #define POST_EMIT_HOOK() \
        auto tos = emit.get_stack().top(); \
        if (!tos->literal()) { \
            MONAD_VM_ASSERT(tos->bit_upper_bound() <= result_bound) \
        }
#else
    #define PRE_EMIT_HOOK(instr)
    #define POST_EMIT_HOOK()
#endif

    template <Traits traits>
    void emit_instr(
        Emitter &emit, Instruction const &instr, int64_t remaining_base_gas)
    {
        using enum OpCode;
        switch (instr.opcode()) {
        case Add: {
            PRE_EMIT_HOOK(Add);
            emit.add();
            POST_EMIT_HOOK();
            break;
        }
        case Mul: {
            PRE_EMIT_HOOK(Mul);
            emit.mul(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }

        case Sub: {
            PRE_EMIT_HOOK(Sub);
            emit.sub();
            POST_EMIT_HOOK();
            break;
        }

        case Div: {
            PRE_EMIT_HOOK(Div);
            emit.udiv(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        case SDiv: {
            PRE_EMIT_HOOK(SDiv);
            emit.sdiv(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        case Mod: {
            PRE_EMIT_HOOK(Mod);
            emit.umod(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        case SMod: {
            PRE_EMIT_HOOK(SMod);
            emit.smod(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        case AddMod: {
            PRE_EMIT_HOOK(AddMod);
            emit.addmod(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        case MulMod: {
            PRE_EMIT_HOOK(MulMod);
            emit.mulmod(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        case Exp: {
            PRE_EMIT_HOOK(Exp);
            emit.exp<traits>(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        case SignExtend: {
            PRE_EMIT_HOOK(SignExtend);
            emit.signextend();
            POST_EMIT_HOOK();
            break;
        }
        case Lt: {
            PRE_EMIT_HOOK(Lt);
            emit.lt();
            POST_EMIT_HOOK();
            break;
        }
        case Gt: {
            PRE_EMIT_HOOK(Gt);
            emit.gt();
            POST_EMIT_HOOK();
            break;
        }
        case SLt: {
            PRE_EMIT_HOOK(SLt);
            emit.slt();
            POST_EMIT_HOOK();
            break;
        }
        case SGt: {
            PRE_EMIT_HOOK(SGt);
            emit.sgt();
            POST_EMIT_HOOK();
            break;
        }
        case Eq: {
            PRE_EMIT_HOOK(Eq);
            emit.eq();
            POST_EMIT_HOOK();
            break;
        }
        case IsZero: {
            PRE_EMIT_HOOK(IsZero);
            emit.iszero();
            POST_EMIT_HOOK();
            break;
        }
        case And: {
            PRE_EMIT_HOOK(And);
            emit.and_();
            POST_EMIT_HOOK();
            break;
        }
        case Or: {
            PRE_EMIT_HOOK(Or);
            emit.or_();
            POST_EMIT_HOOK();
            break;
        }
        case XOr: {
            PRE_EMIT_HOOK(XOr);
            emit.xor_();
            POST_EMIT_HOOK();
            break;
        }
        case Not: {
            PRE_EMIT_HOOK(Not);
            emit.not_();
            POST_EMIT_HOOK();
            break;
        }
        case Byte: {
            PRE_EMIT_HOOK(Byte);
            emit.byte();
            POST_EMIT_HOOK();
            break;
        }
        case Shl: {
            PRE_EMIT_HOOK(Shl);
            emit.shl();
            POST_EMIT_HOOK();
            break;
        }
        case Shr: {
            PRE_EMIT_HOOK(Shr);
            emit.shr();
            POST_EMIT_HOOK();
            break;
        }
        case Sar: {
            PRE_EMIT_HOOK(Sar);
            emit.sar();
            POST_EMIT_HOOK();
            break;
        }
        case Clz: {
            PRE_EMIT_HOOK(Clz);
            emit.clz();
            POST_EMIT_HOOK();
            break;
        }
        case Sha3: {
            PRE_EMIT_HOOK(Sha3);
            emit.sha3<traits>(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        case Address: {
            PRE_EMIT_HOOK(Address);
            emit.address();
            POST_EMIT_HOOK();
            break;
        }
        case Balance: {
            PRE_EMIT_HOOK(Balance);
            emit.balance<traits>(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        case Origin: {
            PRE_EMIT_HOOK(Origin);
            emit.origin();
            POST_EMIT_HOOK();
            break;
        }
        case Caller: {
            PRE_EMIT_HOOK(Caller);
            emit.caller();
            POST_EMIT_HOOK();
            break;
        }
        case CallValue: {
            PRE_EMIT_HOOK(CallValue);
            emit.callvalue();
            POST_EMIT_HOOK();
            break;
        }
        case CallDataLoad: {
            PRE_EMIT_HOOK(CallDataLoad);
            emit.calldataload();
            POST_EMIT_HOOK();
            break;
        }
        case CallDataSize: {
            PRE_EMIT_HOOK(CallDataSize);
            emit.calldatasize();
            POST_EMIT_HOOK();
            break;
        }
        case CallDataCopy:
            emit.calldatacopy<traits>(remaining_base_gas);
            break;
        case CodeSize: {
            PRE_EMIT_HOOK(CodeSize);
            emit.codesize();
            POST_EMIT_HOOK();
            break;
        }
        case CodeCopy:
            emit.codecopy<traits>(remaining_base_gas);
            break;
        case GasPrice: {
            PRE_EMIT_HOOK(GasPrice);
            emit.gasprice();
            POST_EMIT_HOOK();
            break;
        }
        case ExtCodeSize: {
            PRE_EMIT_HOOK(ExtCodeSize);
            emit.extcodesize<traits>(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        case ExtCodeCopy:
            emit.extcodecopy<traits>(remaining_base_gas);
            break;
        case ReturnDataSize: {
            PRE_EMIT_HOOK(ReturnDataSize);
            emit.returndatasize();
            POST_EMIT_HOOK();
            break;
        }
        case ReturnDataCopy:
            emit.returndatacopy<traits>(remaining_base_gas);
            break;
        case ExtCodeHash: {
            PRE_EMIT_HOOK(ExtCodeHash);
            emit.extcodehash<traits>(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        case BlockHash: {
            PRE_EMIT_HOOK(BlockHash);
            emit.blockhash<traits>(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        case Coinbase: {
            PRE_EMIT_HOOK(Coinbase);
            emit.coinbase();
            POST_EMIT_HOOK();
            break;
        }
        case Timestamp: {
            PRE_EMIT_HOOK(Timestamp);
            emit.timestamp();
            POST_EMIT_HOOK();
            break;
        }
        case Number: {
            PRE_EMIT_HOOK(Number);
            emit.number();
            POST_EMIT_HOOK();
            break;
        }
        case Difficulty: {
            PRE_EMIT_HOOK(Difficulty);
            emit.prevrandao();
            POST_EMIT_HOOK();
            break;
        }
        case GasLimit: {
            PRE_EMIT_HOOK(GasLimit);
            emit.gaslimit();
            POST_EMIT_HOOK();
            break;
        }
        case ChainId: {
            PRE_EMIT_HOOK(ChainId);
            emit.chainid();
            POST_EMIT_HOOK();
            break;
        }
        case SelfBalance: {
            PRE_EMIT_HOOK(SelfBalance);
            emit.selfbalance<traits>(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        case BaseFee: {
            PRE_EMIT_HOOK(BaseFee);
            emit.basefee();
            POST_EMIT_HOOK();
            break;
        }
        case BlobHash: {
            PRE_EMIT_HOOK(BlobHash);
            emit.blobhash<traits>(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        case BlobBaseFee: {
            PRE_EMIT_HOOK(BlobBaseFee);
            emit.blobbasefee();
            POST_EMIT_HOOK();
            break;
        }
        case Pop:
            emit.pop();
            break;
        case MLoad: {
            PRE_EMIT_HOOK(MLoad);
            emit.mload();
            POST_EMIT_HOOK();
            break;
        }
        case MStore:
            emit.mstore();
            break;
        case MStore8:
            emit.mstore8();
            break;
        case SLoad: {
            PRE_EMIT_HOOK(SLoad);
            emit.sload<traits>(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        case SStore:
            emit.sstore<traits>(remaining_base_gas);
            break;
        case Pc: {
            PRE_EMIT_HOOK(Pc);
            emit.push(instr.pc());
            POST_EMIT_HOOK();
            break;
        }
        case MSize: {
            PRE_EMIT_HOOK(MSize);
            emit.msize();
            POST_EMIT_HOOK();
            break;
        }
        case Gas: {
            PRE_EMIT_HOOK(Gas);
            emit.gas(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        case TLoad: {
            PRE_EMIT_HOOK(TLoad);
            emit.tload<traits>(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        case TStore:
            emit.tstore<traits>(remaining_base_gas);
            break;
        case MCopy:
            emit.mcopy<traits>(remaining_base_gas);
            break;
        case Push: {
            PRE_EMIT_HOOK(Push);
            emit.push(instr.immediate_value());
            POST_EMIT_HOOK();
            break;
        }
        case Dup: {
            emit.dup(instr.index());
            break;
        }
        case Swap:
            emit.swap(instr.index());
            break;
        case Log:
            switch (instr.index()) {
            case 0:
                emit.log0<traits>(remaining_base_gas);
                break;
            case 1:
                emit.log1<traits>(remaining_base_gas);
                break;
            case 2:
                emit.log2<traits>(remaining_base_gas);
                break;
            case 3:
                emit.log3<traits>(remaining_base_gas);
                break;
            case 4:
                emit.log4<traits>(remaining_base_gas);
                break;
            default:
                MONAD_VM_ASSERT(false);
            }
            break;
        case Create: {
            PRE_EMIT_HOOK(Create);
            emit.create<traits>(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        case Call: {
            PRE_EMIT_HOOK(Call);
            emit.call<traits>(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        case CallCode: {
            PRE_EMIT_HOOK(CallCode);
            emit.callcode<traits>(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        case DelegateCall: {
            PRE_EMIT_HOOK(DelegateCall);
            emit.delegatecall<traits>(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        case Create2: {
            PRE_EMIT_HOOK(Create2);
            emit.create2<traits>(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        case StaticCall: {
            PRE_EMIT_HOOK(StaticCall);
            emit.staticcall<traits>(remaining_base_gas);
            POST_EMIT_HOOK();
            break;
        }
        }
    }

    [[gnu::always_inline]]
    inline void require_code_size_in_bound(
        Emitter &emit, native_code_size_t max_native_size)
    {
        size_t const size_estimate = emit.estimate_size();
        if (MONAD_VM_UNLIKELY(size_estimate > *max_native_size)) {
            throw Nativecode::SizeEstimateOutOfBounds{size_estimate};
        }
    }

    [[gnu::always_inline]]
    inline void post_instruction_emit(
        Emitter &emit, Instruction const &instr, CompilerConfig const &config)
    {
        (void)emit;
        (void)instr;
        (void)config;
#ifdef MONAD_COMPILER_TESTING
        if (config.post_instruction_emit_hook) {
            config.post_instruction_emit_hook(emit, instr);
        }
#endif
    }

    template <Traits traits>
    void emit_instrs(
        Emitter &emit, Block const &block, int64_t instr_gas,
        native_code_size_t max_native_size, CompilerConfig const &config)
    {
        int64_t remaining_base_gas = instr_gas;
        for (auto const &instr : block.instrs) {
            MONAD_VM_DEBUG_ASSERT(
                remaining_base_gas >= instr.static_gas_cost());
            remaining_base_gas -= instr.static_gas_cost();
            emit_instr<traits>(emit, instr, remaining_base_gas);
            require_code_size_in_bound(emit, max_native_size);
            post_instruction_emit(emit, instr, config);
        }
    }

    template <Traits traits>
    void
    emit_terminator(Emitter &emit, BasicBlocksIR const &ir, Block const &block)
    {
        // Remaining block base gas is zero for terminator instruction,
        // because there are no more instructions left in the block.
        constexpr int64_t remaining_base_gas = 0;
        using enum basic_blocks::Terminator;
        switch (block.terminator) {
        case FallThrough:
            emit.fallthrough();
            break;
        case JumpI:
            MONAD_VM_DEBUG_ASSERT(block.fallthrough_dest != INVALID_BLOCK_ID);
            emit.jumpi(ir.blocks()[block.fallthrough_dest]);
            break;
        case Jump:
            emit.jump();
            break;
        case Return:
            emit.return_();
            break;
        case Stop:
            emit.stop();
            break;
        case Revert:
            emit.revert();
            break;
        case SelfDestruct:
            emit.selfdestruct<traits>(remaining_base_gas);
            break;
        case InvalidInstruction:
            emit.invalid_instruction();
            break;
        }
    }

    void emit_gas_decrement(
        Emitter &emit, BasicBlocksIR const &ir, Block const &block,
        int64_t block_base_gas)
    {
        if (ir.jump_dests().contains(block.offset)) {
            emit.gas_decrement_unbounded_work(block_base_gas + 1);
        }
        else {
            emit.gas_decrement_static_work(block_base_gas);
        }
    }

    template <Traits traits>
    std::shared_ptr<Nativecode> compile_contract(
        asmjit::JitRuntime &rt, std::uint8_t const *contract_code,
        code_size_t contract_code_size, CompilerConfig const &config)
    {
        auto const ir =
            basic_blocks::make_ir<traits>(contract_code, contract_code_size);
        return compile_basic_blocks<traits>(rt, ir, config);
    }
}

namespace monad::vm::compiler::native
{
    template <Traits traits>
    std::shared_ptr<Nativecode> compile(
        asmjit::JitRuntime &rt, std::uint8_t const *contract_code,
        code_size_t contract_code_size, CompilerConfig const &config)
    {
        try {
            return ::compile_contract<traits>(
                rt, contract_code, contract_code_size, config);
        }
        catch (Emitter::Error const &e) {
            LOG_ERROR("ERROR: X86 emitter: failed compile: {}", e.what());
            return std::make_shared<Nativecode>(
                rt, traits::id(), nullptr, std::monostate{});
        }
        catch (Nativecode::SizeEstimateOutOfBounds const &e) {
            LOG_WARNING(
                "WARNING: X86 emitter: native code out of bound: {}",
                e.size_estimate);
            return std::make_shared<Nativecode>(
                rt, traits::id(), nullptr, e.size_estimate);
        }
    }

    EXPLICIT_TRAITS(compile);

    template <Traits traits>
    std::shared_ptr<Nativecode> compile_basic_blocks(
        asmjit::JitRuntime &rt, basic_blocks::BasicBlocksIR const &ir,
        CompilerConfig const &config)
    {
        Emitter emit{rt, ir.codesize, config};
        for (auto const &[d, _] : ir.jump_dests()) {
            emit.add_jump_dest(d);
        }
        native_code_size_t const max_native_size =
            max_code_size(config.max_code_size_offset, ir.codesize);
        for (Block const &block : ir.blocks()) {
            bool const can_enter_block = emit.begin_new_block(block);
            if (can_enter_block) {
                int64_t const base_gas = block_base_gas<traits>(block);
                emit_gas_decrement(emit, ir, block, base_gas);
                emit_instrs<traits>(
                    emit, block, base_gas, max_native_size, config);
                emit_terminator<traits>(emit, ir, block);
            }
            require_code_size_in_bound(emit, max_native_size);
        }
        size_t const size_estimate = emit.estimate_size();
        auto entry = emit.finish_contract(rt);
        MONAD_VM_DEBUG_ASSERT(size_estimate <= *max_native_size);
        return std::make_shared<Nativecode>(
            rt,
            traits::id(),
            entry,
            native_code_size_t::unsafe_from(
                static_cast<uint32_t>(size_estimate)));
    }

    EXPLICIT_TRAITS(compile_basic_blocks);
}

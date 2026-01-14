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

    [[gnu::always_inline]]
    void set_bit_bound(Emitter &emit, std::uint32_t result_bound)
    {
        emit.get_stack()
            .get(emit.get_stack().top_index())
            ->set_bit_upper_bound(result_bound);
    }

    template <Traits traits>
    void emit_instr(
        Emitter &emit, Instruction const &instr, int64_t remaining_base_gas)
    {
        using enum OpCode;
        switch (instr.opcode()) {
        case Add: {
            auto const result_bound =
                bound_inference::compute_result_bound<Add, traits>(emit);
            emit.add();
            set_bit_bound(emit, result_bound);
            break;
        }
        case Mul: {
            auto const result_bound =
                bound_inference::compute_result_bound<Mul, traits>(emit);
            emit.mul(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }

        case Sub: {
            auto const result_bound =
                bound_inference::compute_result_bound<Sub, traits>(emit);
            emit.sub();
            set_bit_bound(emit, result_bound);
            break;
        }

        case Div: {
            auto const result_bound =
                bound_inference::compute_result_bound<Div, traits>(emit);
            emit.udiv(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }
        case SDiv: {
            auto const result_bound =
                bound_inference::compute_result_bound<SDiv, traits>(emit);
            emit.sdiv(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }
        case Mod: {
            auto const result_bound =
                bound_inference::compute_result_bound<Mod, traits>(emit);
            emit.umod(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }
        case SMod: {
            auto const result_bound =
                bound_inference::compute_result_bound<SMod, traits>(emit);
            emit.smod(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }
        case AddMod: {
            auto const result_bound =
                bound_inference::compute_result_bound<AddMod, traits>(emit);
            emit.addmod(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }
        case MulMod: {
            auto const result_bound =
                bound_inference::compute_result_bound<MulMod, traits>(emit);
            emit.mulmod(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }
        case Exp: {
            auto const result_bound =
                bound_inference::compute_result_bound<Exp, traits>(emit);
            emit.exp<traits>(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }
        case SignExtend: {
            auto const result_bound =
                bound_inference::compute_result_bound<SignExtend, traits>(emit);
            emit.signextend();
            set_bit_bound(emit, result_bound);
            break;
        }
        case Lt: {
            auto const result_bound =
                bound_inference::compute_result_bound<Lt, traits>(emit);
            emit.lt();
            set_bit_bound(emit, result_bound);
            break;
        }
        case Gt: {
            auto const result_bound =
                bound_inference::compute_result_bound<Gt, traits>(emit);
            emit.gt();
            set_bit_bound(emit, result_bound);
            break;
        }
        case SLt: {
            auto const result_bound =
                bound_inference::compute_result_bound<SLt, traits>(emit);
            emit.slt();
            set_bit_bound(emit, result_bound);
            break;
        }
        case SGt: {
            auto const result_bound =
                bound_inference::compute_result_bound<SGt, traits>(emit);
            emit.sgt();
            set_bit_bound(emit, result_bound);
            break;
        }
        case Eq: {
            auto const result_bound =
                bound_inference::compute_result_bound<Eq, traits>(emit);
            emit.eq();
            set_bit_bound(emit, result_bound);
            break;
        }
        case IsZero: {
            auto const result_bound =
                bound_inference::compute_result_bound<IsZero, traits>(emit);
            emit.iszero();
            set_bit_bound(emit, result_bound);
            break;
        }
        case And: {
            auto const result_bound =
                bound_inference::compute_result_bound<And, traits>(emit);
            emit.and_();
            set_bit_bound(emit, result_bound);
            break;
        }
        case Or: {
            auto const result_bound =
                bound_inference::compute_result_bound<Or, traits>(emit);
            emit.or_();
            set_bit_bound(emit, result_bound);
            break;
        }
        case XOr: {
            auto const result_bound =
                bound_inference::compute_result_bound<XOr, traits>(emit);
            emit.xor_();
            set_bit_bound(emit, result_bound);
            break;
        }
        case Not: {
            auto const result_bound =
                bound_inference::compute_result_bound<Not, traits>(emit);
            emit.not_();
            set_bit_bound(emit, result_bound);
            break;
        }
        case Byte: {
            auto const result_bound =
                bound_inference::compute_result_bound<Byte, traits>(emit);
            emit.byte();
            set_bit_bound(emit, result_bound);
            break;
        }
        case Shl: {
            auto const result_bound =
                bound_inference::compute_result_bound<Shl, traits>(emit);
            emit.shl();
            set_bit_bound(emit, result_bound);
            break;
        }
        case Shr: {
            auto const result_bound =
                bound_inference::compute_result_bound<Shr, traits>(emit);
            emit.shr();
            set_bit_bound(emit, result_bound);
            break;
        }
        case Sar: {
            auto const result_bound =
                bound_inference::compute_result_bound<Sar, traits>(emit);
            emit.sar();
            set_bit_bound(emit, result_bound);
            break;
        }
        case Clz: {
            auto const result_bound =
                bound_inference::compute_result_bound<Clz, traits>(emit);
            emit.clz();
            set_bit_bound(emit, result_bound);
            break;
        }
        case Sha3: {
            auto const result_bound =
                bound_inference::compute_result_bound<Sha3, traits>(emit);
            emit.sha3<traits>(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }
        case Address: {
            auto const result_bound =
                bound_inference::compute_result_bound<Address, traits>(emit);
            emit.address();
            set_bit_bound(emit, result_bound);
            break;
        }
        case Balance: {
            auto const result_bound =
                bound_inference::compute_result_bound<Balance, traits>(emit);
            emit.balance<traits>(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }
        case Origin: {
            auto const result_bound =
                bound_inference::compute_result_bound<Origin, traits>(emit);
            emit.origin();
            set_bit_bound(emit, result_bound);
            break;
        }
        case Caller: {
            auto const result_bound =
                bound_inference::compute_result_bound<Caller, traits>(emit);
            emit.caller();
            set_bit_bound(emit, result_bound);
            break;
        }
        case CallValue: {
            auto const result_bound =
                bound_inference::compute_result_bound<CallValue, traits>(emit);
            emit.callvalue();
            set_bit_bound(emit, result_bound);
            break;
        }
        case CallDataLoad: {
            auto const result_bound =
                bound_inference::compute_result_bound<CallDataLoad, traits>(
                    emit);
            emit.calldataload();
            set_bit_bound(emit, result_bound);
            break;
        }
        case CallDataSize: {
            auto const result_bound =
                bound_inference::compute_result_bound<CallDataSize, traits>(
                    emit);
            emit.calldatasize();
            set_bit_bound(emit, result_bound);
            break;
        }
        case CallDataCopy:
            emit.calldatacopy<traits>(remaining_base_gas);
            break;
        case CodeSize: {
            auto const result_bound =
                bound_inference::compute_result_bound<CodeSize, traits>(emit);
            emit.codesize();
            set_bit_bound(emit, result_bound);
            break;
        }
        case CodeCopy:
            emit.codecopy<traits>(remaining_base_gas);
            break;
        case GasPrice: {
            auto const result_bound =
                bound_inference::compute_result_bound<GasPrice, traits>(emit);
            emit.gasprice();
            set_bit_bound(emit, result_bound);
            break;
        }
        case ExtCodeSize: {
            auto const result_bound =
                bound_inference::compute_result_bound<ExtCodeSize, traits>(
                    emit);
            emit.extcodesize<traits>(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }
        case ExtCodeCopy:
            emit.extcodecopy<traits>(remaining_base_gas);
            break;
        case ReturnDataSize: {
            auto const result_bound =
                bound_inference::compute_result_bound<ReturnDataSize, traits>(
                    emit);
            emit.returndatasize();
            set_bit_bound(emit, result_bound);
            break;
        }
        case ReturnDataCopy:
            emit.returndatacopy<traits>(remaining_base_gas);
            break;
        case ExtCodeHash: {
            auto const result_bound =
                bound_inference::compute_result_bound<ExtCodeHash, traits>(
                    emit);
            emit.extcodehash<traits>(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }
        case BlockHash: {
            auto const result_bound =
                bound_inference::compute_result_bound<BlockHash, traits>(emit);
            emit.blockhash<traits>(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }
        case Coinbase: {
            auto const result_bound =
                bound_inference::compute_result_bound<Coinbase, traits>(emit);
            emit.coinbase();
            set_bit_bound(emit, result_bound);
            break;
        }
        case Timestamp: {
            auto const result_bound =
                bound_inference::compute_result_bound<Timestamp, traits>(emit);
            emit.timestamp();
            set_bit_bound(emit, result_bound);
            break;
        }
        case Number: {
            auto const result_bound =
                bound_inference::compute_result_bound<Number, traits>(emit);
            emit.number();
            set_bit_bound(emit, result_bound);
            break;
        }
        case Difficulty: {
            auto const result_bound =
                bound_inference::compute_result_bound<Difficulty, traits>(emit);
            emit.prevrandao();
            set_bit_bound(emit, result_bound);
            break;
        }
        case GasLimit: {
            auto const result_bound =
                bound_inference::compute_result_bound<GasLimit, traits>(emit);
            emit.gaslimit();
            set_bit_bound(emit, result_bound);
            break;
        }
        case ChainId: {
            auto const result_bound =
                bound_inference::compute_result_bound<ChainId, traits>(emit);
            emit.chainid();
            set_bit_bound(emit, result_bound);
            break;
        }
        case SelfBalance: {
            auto const result_bound =
                bound_inference::compute_result_bound<SelfBalance, traits>(
                    emit);
            emit.selfbalance<traits>(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }
        case BaseFee: {
            auto const result_bound =
                bound_inference::compute_result_bound<BaseFee, traits>(emit);
            emit.basefee();
            set_bit_bound(emit, result_bound);
            break;
        }
        case BlobHash: {
            auto const result_bound =
                bound_inference::compute_result_bound<BlobHash, traits>(emit);
            emit.blobhash<traits>(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }
        case BlobBaseFee: {
            auto const result_bound =
                bound_inference::compute_result_bound<BlobBaseFee, traits>(
                    emit);
            emit.blobbasefee();
            set_bit_bound(emit, result_bound);
            break;
        }
        case Pop:
            emit.pop();
            break;
        case MLoad: {
            auto const result_bound =
                bound_inference::compute_result_bound<MLoad, traits>(emit);
            emit.mload();
            set_bit_bound(emit, result_bound);
            break;
        }
        case MStore:
            emit.mstore();
            break;
        case MStore8:
            emit.mstore8();
            break;
        case SLoad: {
            auto const result_bound =
                bound_inference::compute_result_bound<SLoad, traits>(emit);
            emit.sload<traits>(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }
        case SStore:
            emit.sstore<traits>(remaining_base_gas);
            break;
        case Pc: {
            auto const result_bound =
                bound_inference::compute_result_bound<Pc, traits>(emit);
            emit.push(instr.pc());
            set_bit_bound(emit, result_bound);
            break;
        }
        case MSize: {
            auto const result_bound =
                bound_inference::compute_result_bound<MSize, traits>(emit);
            emit.msize();
            set_bit_bound(emit, result_bound);
            break;
        }
        case Gas: {
            auto const result_bound =
                bound_inference::compute_result_bound<Gas, traits>(emit);
            emit.gas(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }
        case TLoad: {
            auto const result_bound =
                bound_inference::compute_result_bound<TLoad, traits>(emit);
            emit.tload<traits>(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }
        case TStore:
            emit.tstore<traits>(remaining_base_gas);
            break;
        case MCopy:
            emit.mcopy<traits>(remaining_base_gas);
            break;
        case Push: {
            auto const result_bound =
                bound_inference::compute_result_bound<Push, traits>(emit);
            emit.push(instr.immediate_value());
            set_bit_bound(emit, result_bound);
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
            auto const result_bound =
                bound_inference::compute_result_bound<Create, traits>(emit);
            emit.create<traits>(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }
        case Call: {
            auto const result_bound =
                bound_inference::compute_result_bound<Call, traits>(emit);
            emit.call<traits>(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }
        case CallCode: {
            auto const result_bound =
                bound_inference::compute_result_bound<CallCode, traits>(emit);
            emit.callcode<traits>(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }
        case DelegateCall: {
            auto const result_bound =
                bound_inference::compute_result_bound<DelegateCall, traits>(
                    emit);
            emit.delegatecall<traits>(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }
        case Create2: {
            auto const result_bound =
                bound_inference::compute_result_bound<Create2, traits>(emit);
            emit.create2<traits>(remaining_base_gas);
            set_bit_bound(emit, result_bound);
            break;
        }
        case StaticCall: {
            auto const result_bound =
                bound_inference::compute_result_bound<StaticCall, traits>(emit);
            emit.staticcall<traits>(remaining_base_gas);
            set_bit_bound(emit, result_bound);
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

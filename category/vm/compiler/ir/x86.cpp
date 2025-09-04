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

    template <Traits traits>
    void emit_instr(
        Emitter &emit, Instruction const &instr, int64_t remaining_base_gas)
    {
        using enum OpCode;
        switch (instr.opcode()) {
        case Add:
            emit.add();
            break;
        case Mul:
            emit.mul(remaining_base_gas);
            break;
        case Sub:
            emit.sub();
            break;
        case Div:
            emit.udiv(remaining_base_gas);
            break;
        case SDiv:
            emit.sdiv(remaining_base_gas);
            break;
        case Mod:
            emit.umod(remaining_base_gas);
            break;
        case SMod:
            emit.smod(remaining_base_gas);
            break;
        case AddMod:
            emit.addmod(remaining_base_gas);
            break;
        case MulMod:
            emit.mulmod(remaining_base_gas);
            break;
        case Exp:
            emit.exp<traits>(remaining_base_gas);
            break;
        case SignExtend:
            emit.signextend();
            break;
        case Lt:
            emit.lt();
            break;
        case Gt:
            emit.gt();
            break;
        case SLt:
            emit.slt();
            break;
        case SGt:
            emit.sgt();
            break;
        case Eq:
            emit.eq();
            break;
        case IsZero:
            emit.iszero();
            break;
        case And:
            emit.and_();
            break;
        case Or:
            emit.or_();
            break;
        case XOr:
            emit.xor_();
            break;
        case Not:
            emit.not_();
            break;
        case Byte:
            emit.byte();
            break;
        case Shl:
            emit.shl();
            break;
        case Shr:
            emit.shr();
            break;
        case Sar:
            emit.sar();
            break;
        case Clz:
            emit.clz();
            break;
        case Sha3:
            emit.sha3<traits>(remaining_base_gas);
            break;
        case Address:
            emit.address();
            break;
        case Balance:
            emit.balance<traits>(remaining_base_gas);
            break;
        case Origin:
            emit.origin();
            break;
        case Caller:
            emit.caller();
            break;
        case CallValue:
            emit.callvalue();
            break;
        case CallDataLoad:
            emit.calldataload();
            break;
        case CallDataSize:
            emit.calldatasize();
            break;
        case CallDataCopy:
            emit.calldatacopy<traits>(remaining_base_gas);
            break;
        case CodeSize:
            emit.codesize();
            break;
        case CodeCopy:
            emit.codecopy<traits>(remaining_base_gas);
            break;
        case GasPrice:
            emit.gasprice();
            break;
        case ExtCodeSize:
            emit.extcodesize<traits>(remaining_base_gas);
            break;
        case ExtCodeCopy:
            emit.extcodecopy<traits>(remaining_base_gas);
            break;
        case ReturnDataSize:
            emit.returndatasize();
            break;
        case ReturnDataCopy:
            emit.returndatacopy<traits>(remaining_base_gas);
            break;
        case ExtCodeHash:
            emit.extcodehash<traits>(remaining_base_gas);
            break;
        case BlockHash:
            emit.blockhash<traits>(remaining_base_gas);
            break;
        case Coinbase:
            emit.coinbase();
            break;
        case Timestamp:
            emit.timestamp();
            break;
        case Number:
            emit.number();
            break;
        case Difficulty:
            emit.prevrandao();
            break;
        case GasLimit:
            emit.gaslimit();
            break;
        case ChainId:
            emit.chainid();
            break;
        case SelfBalance:
            emit.selfbalance<traits>(remaining_base_gas);
            break;
        case BaseFee:
            emit.basefee();
            break;
        case BlobHash:
            emit.blobhash<traits>(remaining_base_gas);
            break;
        case BlobBaseFee:
            emit.blobbasefee();
            break;
        case Pop:
            emit.pop();
            break;
        case MLoad:
            emit.mload();
            break;
        case MStore:
            emit.mstore();
            break;
        case MStore8:
            emit.mstore8();
            break;
        case SLoad:
            emit.sload<traits>(remaining_base_gas);
            break;
        case SStore:
            emit.sstore<traits>(remaining_base_gas);
            break;
        case Pc:
            emit.push(instr.pc());
            break;
        case MSize:
            emit.msize();
            break;
        case Gas:
            emit.gas(remaining_base_gas);
            break;
        case TLoad:
            emit.tload<traits>(remaining_base_gas);
            break;
        case TStore:
            emit.tstore<traits>(remaining_base_gas);
            break;
        case MCopy:
            emit.mcopy<traits>(remaining_base_gas);
            break;
        case Push:
            emit.push(instr.immediate_value());
            break;
        case Dup:
            emit.dup(instr.index());
            break;
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
        case Create:
            emit.create<traits>(remaining_base_gas);
            break;
        case Call:
            emit.call<traits>(remaining_base_gas);
            break;
        case CallCode:
            emit.callcode<traits>(remaining_base_gas);
            break;
        case DelegateCall:
            emit.delegatecall<traits>(remaining_base_gas);
            break;
        case Create2:
            emit.create2<traits>(remaining_base_gas);
            break;
        case StaticCall:
            emit.staticcall<traits>(remaining_base_gas);
            break;
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
    inline void pre_instruction_emit(
        Emitter &emit, CompilerConfig const &config, size_t block_id, size_t instr_index, Instruction const &instr)
    {
        (void)emit;
        (void)config;
        (void)block_id;
        (void)instr_index;
        (void)instr;
#ifdef MONAD_COMPILER_TESTING
        if (config.pre_instruction_emit_hook) {
            config.pre_instruction_emit_hook(emit, block_id, instr_index, instr);
        }
#endif
    }

    [[gnu::always_inline]]
    inline void
    post_instruction_emit(Emitter &emit, CompilerConfig const &config, size_t block_id, size_t instr_index, Instruction const &instr)
    {
        (void)emit;
        (void)config;
        (void)block_id;
        (void)instr_index;
        (void)instr;
#ifdef MONAD_COMPILER_TESTING
        if (config.post_instruction_emit_hook) {
            config.post_instruction_emit_hook(emit, block_id, instr_index, instr);
        }
#endif
    }

    template <Traits traits>
    void emit_instrs(
        Emitter &emit, size_t block_id, Block const &block, int64_t instr_gas,
        native_code_size_t max_native_size, CompilerConfig const &config)
    {
        int64_t remaining_base_gas = instr_gas;
        for (size_t i = 0; i < block.instrs.size(); ++i) {
            auto const &instr = block.instrs[i];
            MONAD_VM_DEBUG_ASSERT(
                remaining_base_gas >= instr.static_gas_cost());
            pre_instruction_emit(emit, config, block_id, i, instr);
            remaining_base_gas -= instr.static_gas_cost();
            emit_instr<traits>(emit, instr, remaining_base_gas);
            require_code_size_in_bound(emit, max_native_size);
            post_instruction_emit(emit, config, block_id, i, instr);
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
        for (size_t block_id = 0; block_id < ir.blocks().size(); ++block_id) {
            Block const &block = ir.blocks()[block_id];
            bool const can_enter_block = emit.begin_new_block(block);
            if (can_enter_block) {
                int64_t const base_gas = block_base_gas<traits>(block);
                emit_gas_decrement(emit, ir, block, base_gas);
                emit_instrs<traits>(
                    emit, block_id, block, base_gas, max_native_size, config);
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

#include <monad/vm/compiler/ir/basic_blocks.hpp>
#include <monad/vm/compiler/ir/instruction.hpp>
#include <monad/vm/compiler/ir/x86.hpp>
#include <monad/vm/compiler/ir/x86/emitter.hpp>
#include <monad/vm/compiler/ir/x86/types.hpp>
#include <monad/vm/compiler/types.hpp>
#include <monad/vm/core/assert.h>

#include <evmc/evmc.h>

#include <asmjit/core/jitruntime.h>

#include <cstddef>
#include <cstdint>
#include <format>
#include <iostream>
#include <limits>
#include <memory>
#include <span>

using namespace monad::vm::compiler;
using namespace monad::vm::compiler::basic_blocks;
using namespace monad::vm::compiler::native;

namespace
{
    template <evmc_revision rev>
    void emit_instr(
        Emitter &emit, Instruction const &instr, int32_t remaining_base_gas)
    {
        using enum OpCode;
        switch (instr.opcode()) {
        case Add:
            emit.add();
            break;
        case Mul:
            emit.mul<rev>(remaining_base_gas);
            break;
        case Sub:
            emit.sub();
            break;
        case Div:
            emit.udiv<rev>(remaining_base_gas);
            break;
        case SDiv:
            emit.sdiv<rev>(remaining_base_gas);
            break;
        case Mod:
            emit.umod<rev>(remaining_base_gas);
            break;
        case SMod:
            emit.smod<rev>(remaining_base_gas);
            break;
        case AddMod:
            emit.addmod<rev>(remaining_base_gas);
            break;
        case MulMod:
            emit.mulmod<rev>(remaining_base_gas);
            break;
        case Exp:
            emit.exp<rev>(remaining_base_gas);
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
        case Sha3:
            emit.sha3<rev>(remaining_base_gas);
            break;
        case Address:
            emit.address();
            break;
        case Balance:
            emit.balance<rev>(remaining_base_gas);
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
            emit.calldatacopy<rev>(remaining_base_gas);
            break;
        case CodeSize:
            emit.codesize();
            break;
        case CodeCopy:
            emit.codecopy<rev>(remaining_base_gas);
            break;
        case GasPrice:
            emit.gasprice();
            break;
        case ExtCodeSize:
            emit.extcodesize<rev>(remaining_base_gas);
            break;
        case ExtCodeCopy:
            emit.extcodecopy<rev>(remaining_base_gas);
            break;
        case ReturnDataSize:
            emit.returndatasize();
            break;
        case ReturnDataCopy:
            emit.returndatacopy<rev>(remaining_base_gas);
            break;
        case ExtCodeHash:
            emit.extcodehash<rev>(remaining_base_gas);
            break;
        case BlockHash:
            emit.blockhash<rev>(remaining_base_gas);
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
            emit.selfbalance<rev>(remaining_base_gas);
            break;
        case BaseFee:
            emit.basefee();
            break;
        case BlobHash:
            emit.blobhash<rev>(remaining_base_gas);
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
            emit.sload<rev>(remaining_base_gas);
            break;
        case SStore:
            emit.sstore<rev>(remaining_base_gas);
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
            emit.tload<rev>(remaining_base_gas);
            break;
        case TStore:
            emit.tstore<rev>(remaining_base_gas);
            break;
        case MCopy:
            emit.mcopy<rev>(remaining_base_gas);
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
                emit.log0<rev>(remaining_base_gas);
                break;
            case 1:
                emit.log1<rev>(remaining_base_gas);
                break;
            case 2:
                emit.log2<rev>(remaining_base_gas);
                break;
            case 3:
                emit.log3<rev>(remaining_base_gas);
                break;
            case 4:
                emit.log4<rev>(remaining_base_gas);
                break;
            default:
                MONAD_VM_ASSERT(false);
            }
            break;
        case Create:
            emit.create<rev>(remaining_base_gas);
            break;
        case Call:
            emit.call<rev>(remaining_base_gas);
            break;
        case CallCode:
            emit.callcode<rev>(remaining_base_gas);
            break;
        case DelegateCall:
            emit.delegatecall<rev>(remaining_base_gas);
            break;
        case Create2:
            emit.create2<rev>(remaining_base_gas);
            break;
        case StaticCall:
            emit.staticcall<rev>(remaining_base_gas);
            break;
        }
    }

    struct SizeEstimateOutOfBounds
    {
        size_t size_estimate;
    };

    [[gnu::always_inline]]
    inline void
    require_code_size_in_bound(Emitter &emit, size_t max_native_size)
    {
        size_t const size_estimate = emit.estimate_size();
        if (MONAD_VM_UNLIKELY(size_estimate > max_native_size)) {
            throw SizeEstimateOutOfBounds{size_estimate};
        }
    }

    [[gnu::always_inline]]
    inline void
    post_instruction_emit(Emitter &emit, CompilerConfig const &config)
    {
        (void)emit;
        (void)config;
#ifdef MONAD_COMPILER_TESTING
        if (config.post_instruction_emit_hook) {
            config.post_instruction_emit_hook(emit);
        }
#endif
    }

    template <evmc_revision rev>
    void emit_instrs(
        Emitter &emit, Block const &block, int32_t instr_gas,
        size_t max_native_size, CompilerConfig const &config)
    {
        MONAD_VM_ASSERT(instr_gas <= std::numeric_limits<int32_t>::max());
        int32_t remaining_base_gas = instr_gas;
        for (auto const &instr : block.instrs) {
            MONAD_VM_DEBUG_ASSERT(
                remaining_base_gas >= instr.static_gas_cost());
            remaining_base_gas -= instr.static_gas_cost();
            emit_instr<rev>(emit, instr, remaining_base_gas);
            require_code_size_in_bound(emit, max_native_size);
            post_instruction_emit(emit, config);
        }
    }

    template <evmc_revision rev>
    void
    emit_terminator(Emitter &emit, BasicBlocksIR const &ir, Block const &block)
    {
        // Remaining block base gas is zero for terminator instruction,
        // because there are no more instructions left in the block.
        constexpr int32_t remaining_base_gas = 0;
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
            emit.selfdestruct<rev>(remaining_base_gas);
            break;
        case InvalidInstruction:
            emit.invalid_instruction();
            break;
        }
    }

    void emit_gas_decrement(
        Emitter &emit, BasicBlocksIR const &ir, Block const &block,
        int32_t block_base_gas, int32_t *accumulated_base_gas)
    {
        if (ir.jump_dests().contains(block.offset)) {
            *accumulated_base_gas = 0;
            emit.gas_decrement_check_non_negative(block_base_gas + 1);
            return;
        }

        // Arbitrary gas threshold for when to emit gas check.
        // Needs to be big enough to make the gas check insignificant,
        // and small enough to avoid exploitation of the optimization.
        constexpr int32_t STATIC_GAS_CHECK_THRESHOLD = 1000;

        int32_t const acc = *accumulated_base_gas + block_base_gas;
        if (acc < STATIC_GAS_CHECK_THRESHOLD) {
            *accumulated_base_gas = acc;
            emit.gas_decrement_no_check(block_base_gas);
        }
        else {
            *accumulated_base_gas = 0;
            emit.gas_decrement_check_non_negative(block_base_gas);
        }
    }

    template <evmc_revision rev>
    std::shared_ptr<Nativecode> compile_basic_blocks(
        asmjit::JitRuntime &rt, BasicBlocksIR const &ir,
        CompilerConfig const &config)
    {
        Emitter emit{rt, ir.codesize, config};
        for (auto const &[d, _] : ir.jump_dests()) {
            emit.add_jump_dest(d);
        }
        size_t const max_native_size =
            max_code_size(config.max_code_size_offset, ir.codesize);
        int32_t accumulated_base_gas = 0;
        for (Block const &block : ir.blocks()) {
            bool const can_enter_block = emit.begin_new_block(block);
            if (can_enter_block) {
                int32_t const base_gas = block_base_gas<rev>(block);
                emit_gas_decrement(
                    emit, ir, block, base_gas, &accumulated_base_gas);
                emit_instrs<rev>(
                    emit, block, base_gas, max_native_size, config);
                emit_terminator<rev>(emit, ir, block);
            }
            require_code_size_in_bound(emit, max_native_size);
        }
        size_t const size_estimate = emit.estimate_size();
        auto entry = emit.finish_contract(rt);
        return std::make_shared<Nativecode>(rt, rev, entry, size_estimate);
    }

    template <evmc_revision Rev>
    std::shared_ptr<Nativecode> compile_contract(
        asmjit::JitRuntime &rt, std::span<uint8_t const> contract,
        CompilerConfig const &config)
    {
        auto ir = BasicBlocksIR(basic_blocks::make_ir<Rev>(contract));
        return compile_basic_blocks<Rev>(rt, ir, config);
    }
}

namespace monad::vm::compiler::native
{
    std::shared_ptr<Nativecode> compile(
        asmjit::JitRuntime &rt, std::span<uint8_t const> contract,
        evmc_revision rev, CompilerConfig const &config)
    {
        try {
            switch (rev) {
            case EVMC_FRONTIER:
                return ::compile_contract<EVMC_FRONTIER>(rt, contract, config);
            case EVMC_HOMESTEAD:
                return ::compile_contract<EVMC_HOMESTEAD>(rt, contract, config);
            case EVMC_TANGERINE_WHISTLE:
                return ::compile_contract<EVMC_TANGERINE_WHISTLE>(
                    rt, contract, config);
            case EVMC_SPURIOUS_DRAGON:
                return ::compile_contract<EVMC_SPURIOUS_DRAGON>(
                    rt, contract, config);
            case EVMC_BYZANTIUM:
                return ::compile_contract<EVMC_BYZANTIUM>(rt, contract, config);
            case EVMC_CONSTANTINOPLE:
                return ::compile_contract<EVMC_CONSTANTINOPLE>(
                    rt, contract, config);
            case EVMC_PETERSBURG:
                return ::compile_contract<EVMC_PETERSBURG>(
                    rt, contract, config);
            case EVMC_ISTANBUL:
                return ::compile_contract<EVMC_ISTANBUL>(rt, contract, config);
            case EVMC_BERLIN:
                return ::compile_contract<EVMC_BERLIN>(rt, contract, config);
            case EVMC_LONDON:
                return ::compile_contract<EVMC_LONDON>(rt, contract, config);
            case EVMC_PARIS:
                return ::compile_contract<EVMC_PARIS>(rt, contract, config);
            case EVMC_SHANGHAI:
                return ::compile_contract<EVMC_SHANGHAI>(rt, contract, config);
            case EVMC_CANCUN:
                return ::compile_contract<EVMC_CANCUN>(rt, contract, config);
            case EVMC_PRAGUE:
                return ::compile_contract<EVMC_PRAGUE>(rt, contract, config);
            default:
                MONAD_VM_ASSERT(false);
            }
        }
        catch (Emitter::Error const &e) {
            std::cerr << std::format(
                             "ERROR: X86 emitter: failed compile: {}", e.what())
                      << std::endl;
            return std::make_shared<Nativecode>(rt, rev, nullptr, 0);
        }
        catch (SizeEstimateOutOfBounds const &e) {
            if (config.verbose) {
                std::cerr
                    << std::format(
                           "WARNING: X86 emitter: native code out of bound: {}",
                           e.size_estimate)
                    << std::endl;
            }
            return std::make_shared<Nativecode>(
                rt, rev, nullptr, e.size_estimate);
        }
    }

    std::shared_ptr<Nativecode> compile_basic_blocks(
        evmc_revision rev, asmjit::JitRuntime &rt,
        basic_blocks::BasicBlocksIR const &ir, CompilerConfig const &config)
    {
        switch (rev) {
        case EVMC_FRONTIER:
            return ::compile_basic_blocks<EVMC_FRONTIER>(rt, ir, config);
        case EVMC_HOMESTEAD:
            return ::compile_basic_blocks<EVMC_HOMESTEAD>(rt, ir, config);
        case EVMC_TANGERINE_WHISTLE:
            return ::compile_basic_blocks<EVMC_TANGERINE_WHISTLE>(
                rt, ir, config);
        case EVMC_SPURIOUS_DRAGON:
            return ::compile_basic_blocks<EVMC_SPURIOUS_DRAGON>(rt, ir, config);
        case EVMC_BYZANTIUM:
            return ::compile_basic_blocks<EVMC_BYZANTIUM>(rt, ir, config);
        case EVMC_CONSTANTINOPLE:
            return ::compile_basic_blocks<EVMC_CONSTANTINOPLE>(rt, ir, config);
        case EVMC_PETERSBURG:
            return ::compile_basic_blocks<EVMC_PETERSBURG>(rt, ir, config);
        case EVMC_ISTANBUL:
            return ::compile_basic_blocks<EVMC_ISTANBUL>(rt, ir, config);
        case EVMC_BERLIN:
            return ::compile_basic_blocks<EVMC_BERLIN>(rt, ir, config);
        case EVMC_LONDON:
            return ::compile_basic_blocks<EVMC_LONDON>(rt, ir, config);
        case EVMC_PARIS:
            return ::compile_basic_blocks<EVMC_PARIS>(rt, ir, config);
        case EVMC_SHANGHAI:
            return ::compile_basic_blocks<EVMC_SHANGHAI>(rt, ir, config);
        case EVMC_CANCUN:
            return ::compile_basic_blocks<EVMC_CANCUN>(rt, ir, config);
        case EVMC_PRAGUE:
            return ::compile_basic_blocks<EVMC_PRAGUE>(rt, ir, config);
        default:
            MONAD_VM_ASSERT(false);
        }
    }
}

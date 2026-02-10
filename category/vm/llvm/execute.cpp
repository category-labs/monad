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
#include <category/vm/compiler/types.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/llvm/dependency_blocks.hpp>
#include <category/vm/llvm/emitter.hpp>
#include <category/vm/llvm/llvm_state.hpp>
#include <category/vm/runtime/data.hpp>
#include <category/vm/runtime/environment.hpp>
#include <category/vm/runtime/keccak.hpp>
#include <category/vm/runtime/log.hpp>
#include <category/vm/runtime/memory.hpp>
#include <category/vm/runtime/storage.hpp>
#include <category/vm/runtime/types.hpp>

#include <evmc/evmc.h>

#include <llvm-c/Target.h>

#include <cstdint>
#include <format>
#include <fstream>
#include <memory>
#include <mutex>
#include <span>
#include <string>
#include <string_view>

namespace monad::vm::llvm
{
    using namespace monad::vm::runtime;
    using namespace monad::vm::dependency_blocks;

    extern "C" void llvm_runtime_trampoline(
        // put contract args here and update entry.S accordingly
        uint256_t *, Context *,
        // %rdx contract function ptr
        void (*)(),
        // %rcx &ctx->exit_stack_ptr
        void **);

    void rt_exit [[noreturn]] (Context *ctx, uint64_t x)
    {
        ctx->exit(static_cast<StatusCode>(x));
    };

    std::once_flag llvm_needs_init;

    void init_llvm()
    {
        LLVMInitializeNativeTarget();
        LLVMInitializeNativeAsmPrinter();
    }

    std::shared_ptr<LLVMState> make_shared_llvm_state()
    {
        std::call_once(llvm_needs_init, init_llvm);
        return std::make_shared<LLVMState>();
    }

    template <Traits traits>
    std::shared_ptr<LLVMState> load_from_disk_impl(std::string_view fn)
    {
        auto ptr = make_shared_llvm_state();
        LLVMState &llvm = *ptr;

        llvm.insert_symbol(
            "ffi_context_expand_memory", (void *)context_expand_memory);

        llvm.insert_symbol(
            "ffi_llvm_runtime_debug", (void *)llvm_runtime_debug);
        llvm.insert_symbol(
            "ffi_llvm_runtime_debug_pointer",
            (void *)llvm_runtime_debug_pointer);
        llvm.insert_symbol(
            "ffi_llvm_runtime_debug_string", (void *)llvm_runtime_debug_string);
        llvm.insert_symbol(
            "ffi_llvm_runtime_debug_word", (void *)llvm_runtime_debug_word);
        llvm.insert_symbol(
            "ffi_llvm_runtime_debug_i32", (void *)llvm_runtime_debug_i32);

        llvm.insert_symbol("ffi_SSTORE", (void *)sstore<traits>);
        llvm.insert_symbol("ffi_CREATE", (void *)create<traits>);
        llvm.insert_symbol("ffi_CREATE2", (void *)create2<traits>);
        llvm.insert_symbol("ffi_DELEGATECALL", (void *)delegatecall<traits>);
        llvm.insert_symbol("ffi_STATICCALL", (void *)staticcall<traits>);
        llvm.insert_symbol("ffi_CALL", (void *)call<traits>);
        llvm.insert_symbol("ffi_CALLCODE", (void *)callcode<traits>);
        llvm.insert_symbol("ffi_SELFBALANCE", (void *)selfbalance);
        llvm.insert_symbol("ffi_BALANCE", (void *)balance<traits>);
        llvm.insert_symbol("ffi_EXTCODEHASH", (void *)extcodehash<traits>);
        llvm.insert_symbol("ffi_EXTCODESIZE", (void *)extcodesize<traits>);
        llvm.insert_symbol("ffi_SLOAD", (void *)sload<traits>);
        llvm.insert_symbol("ffi_BLOBHASH", (void *)blobhash);
        llvm.insert_symbol("ffi_BLOCKHASH", (void *)blockhash);
        llvm.insert_symbol("ffi_TLOAD", (void *)tload);
        llvm.insert_symbol("ffi_EXP", (void *)exp<traits>);

        llvm.insert_symbol("ffi_KECCAK256", (void *)sha3);

        llvm.insert_symbol("ffi_TSTORE", (void *)tstore);
        llvm.insert_symbol("ffi_CALLDATACOPY", (void *)calldatacopy);
        llvm.insert_symbol("ffi_CODECOPY", (void *)codecopy);
        llvm.insert_symbol("ffi_MCOPY", (void *)mcopy);
        llvm.insert_symbol("ffi_RETURNDATACOPY", (void *)returndatacopy);
        llvm.insert_symbol("ffi_EXTCODECOPY", (void *)extcodecopy<traits>);
        llvm.insert_symbol("ffi_LOG0", (void *)log0);
        llvm.insert_symbol("ffi_LOG1", (void *)log1);
        llvm.insert_symbol("ffi_LOG2", (void *)log2);
        llvm.insert_symbol("ffi_LOG3", (void *)log3);
        llvm.insert_symbol("ffi_LOG4", (void *)log4);

        llvm.insert_symbol("rt_EXIT", (void *)&rt_exit);
        llvm.insert_symbol("ffi_SelfDestruct", (void *)selfdestruct<traits>);

        llvm.set_contract_addr_from_disk(fn);

        return ptr;
    };

    template <Traits traits>
    std::shared_ptr<LLVMState> compile_basicblocks_impl(
        BasicBlocksIR const &ir, std::string const &dbg_nm = "")
    {
        auto ptr = make_shared_llvm_state();
        LLVMState &llvm = *ptr;

        DependencyBlocksIR dep_ir = make_DependencyBlocksIR<traits>(ir);

        if (!dbg_nm.empty()) {
            std::ofstream out(std::format("{}.ir", dbg_nm));
            auto const ir_str = std::format("{}", ir);
            out << ir_str;
            auto const dep_ir_str = std::format("\n{}", dep_ir);
            out << dep_ir_str;
            out.close();
        }

        MONAD_VM_ASSERT(ir.is_valid());

        llvm.insert_symbol("rt_EXIT", (void *)&rt_exit);

        Emitter<traits> emitter{llvm, dep_ir};

        emitter.emit_contract();
        if (!dbg_nm.empty()) {
            llvm.dump_module(std::format("{}.ll", dbg_nm));
        }

        llvm.set_contract_addr(dbg_nm);

        return ptr;
    }

    EXPLICIT_TRAITS(compile_basicblocks_impl);

    template <Traits traits>
    std::shared_ptr<LLVMState>
    compile_impl(std::span<uint8_t const> code, std::string const &dbg_nm = "")
    {
        BasicBlocksIR const ir = unsafe_make_ir<traits>(code);
        return compile_basicblocks_impl<traits>(ir, dbg_nm);
    }

    std::shared_ptr<LLVMState>
    load_from_disk(evmc_revision rev, std::string_view fn)
    {
        switch (rev) {
        case EVMC_SPURIOUS_DRAGON:
            return load_from_disk_impl<EvmTraits<EVMC_SPURIOUS_DRAGON>>(fn);

        case EVMC_BYZANTIUM:
            return load_from_disk_impl<EvmTraits<EVMC_BYZANTIUM>>(fn);

        case EVMC_CONSTANTINOPLE:
            return load_from_disk_impl<EvmTraits<EVMC_CONSTANTINOPLE>>(fn);

        case EVMC_PETERSBURG:
            return load_from_disk_impl<EvmTraits<EVMC_PETERSBURG>>(fn);

        case EVMC_ISTANBUL:
            return load_from_disk_impl<EvmTraits<EVMC_ISTANBUL>>(fn);

        case EVMC_BERLIN:
            return load_from_disk_impl<EvmTraits<EVMC_BERLIN>>(fn);

        case EVMC_LONDON:
            return load_from_disk_impl<EvmTraits<EVMC_LONDON>>(fn);

        case EVMC_PARIS:
            return load_from_disk_impl<EvmTraits<EVMC_PARIS>>(fn);

        case EVMC_SHANGHAI:
            return load_from_disk_impl<EvmTraits<EVMC_SHANGHAI>>(fn);

        case EVMC_CANCUN:
            return load_from_disk_impl<EvmTraits<EVMC_CANCUN>>(fn);

        case EVMC_PRAGUE:
            return load_from_disk_impl<EvmTraits<EVMC_PRAGUE>>(fn);

        default:
            MONAD_VM_ASSERT(rev == EVMC_OSAKA);
            return load_from_disk_impl<EvmTraits<EVMC_OSAKA>>(fn);
        }
    }

    void execute(LLVMState &llvm, Context &ctx, uint256_t *evm_stack)
    {
        llvm_runtime_trampoline(
            evm_stack, &ctx, llvm.contract_addr, &ctx.exit_stack_ptr);
    }

    std::shared_ptr<LLVMState> compile(
        evmc_revision rev, std::span<uint8_t const> code,
        std::string const &dbg_nm)
    {
        switch (rev) {
        case EVMC_SPURIOUS_DRAGON:
            return compile_impl<EvmTraits<EVMC_SPURIOUS_DRAGON>>(code, dbg_nm);

        case EVMC_BYZANTIUM:
            return compile_impl<EvmTraits<EVMC_BYZANTIUM>>(code, dbg_nm);

        case EVMC_CONSTANTINOPLE:
            return compile_impl<EvmTraits<EVMC_CONSTANTINOPLE>>(code, dbg_nm);

        case EVMC_PETERSBURG:
            return compile_impl<EvmTraits<EVMC_PETERSBURG>>(code, dbg_nm);

        case EVMC_ISTANBUL:
            return compile_impl<EvmTraits<EVMC_ISTANBUL>>(code, dbg_nm);

        case EVMC_BERLIN:
            return compile_impl<EvmTraits<EVMC_BERLIN>>(code, dbg_nm);

        case EVMC_LONDON:
            return compile_impl<EvmTraits<EVMC_LONDON>>(code, dbg_nm);

        case EVMC_PARIS:
            return compile_impl<EvmTraits<EVMC_PARIS>>(code, dbg_nm);

        case EVMC_SHANGHAI:
            return compile_impl<EvmTraits<EVMC_SHANGHAI>>(code, dbg_nm);

        case EVMC_CANCUN:
            return compile_impl<EvmTraits<EVMC_CANCUN>>(code, dbg_nm);

        case EVMC_PRAGUE:
            return compile_impl<EvmTraits<EVMC_PRAGUE>>(code, dbg_nm);

        default:
            MONAD_VM_ASSERT(rev == EVMC_OSAKA);
            return compile_impl<EvmTraits<EVMC_OSAKA>>(code, dbg_nm);
        }
    }
}

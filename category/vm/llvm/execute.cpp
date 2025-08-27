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

#include <category/vm/llvm/emitter.hpp>
#include <category/vm/llvm/llvm_state.hpp>

#include <category/vm/compiler/ir/basic_blocks.hpp>
#include <category/vm/compiler/types.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/evm/chain.hpp>
#include <category/vm/runtime/types.hpp>

#include <evmc/evmc.h>

#include <cstdint>
#include <format>
#include <fstream>
#include <memory>
#include <span>
#include <string>

namespace monad::vm::llvm
{
    using namespace monad::vm::runtime;

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

    template <Traits traits>
    std::shared_ptr<LLVMState>
    compile_impl(std::span<uint8_t const> code, std::string const &dbg_nm = "")
    {
        auto ptr = std::make_shared<LLVMState>();
        LLVMState &llvm = *ptr;

        auto ir = unsafe_make_ir<traits>(code);

        if (dbg_nm != "") {
            std::ofstream out(std::format("{}.ir", dbg_nm));
            auto ir_str = std::format("{}", ir);
            out << ir_str;
            out.close();
        }

        MONAD_VM_DEBUG_ASSERT(ir.is_valid());

        llvm.insert_symbol("rt_EXIT", (void *)&rt_exit);

        Emitter<traits> emitter{llvm, ir};

        if (dbg_nm != "") {
            std::ofstream out(std::format("{}_opt.ir", dbg_nm));
            auto ir_str = std::format("{}", ir);
            out << ir_str;
            out.close();
        }

        emitter.emit_contract();

        if (dbg_nm != "") {
            llvm.dump_module(std::format("{}.ll", dbg_nm));
        }

        llvm.set_contract_addr(dbg_nm);
        return ptr;
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
        case EVMC_FRONTIER:
            return compile_impl<EvmChain<EVMC_FRONTIER>>(code, dbg_nm);

        case EVMC_HOMESTEAD:
            return compile_impl<EvmChain<EVMC_HOMESTEAD>>(code, dbg_nm);

        case EVMC_TANGERINE_WHISTLE:
            return compile_impl<EvmChain<EVMC_TANGERINE_WHISTLE>>(code, dbg_nm);

        case EVMC_SPURIOUS_DRAGON:
            return compile_impl<EvmChain<EVMC_SPURIOUS_DRAGON>>(code, dbg_nm);

        case EVMC_BYZANTIUM:
            return compile_impl<EvmChain<EVMC_BYZANTIUM>>(code, dbg_nm);

        case EVMC_CONSTANTINOPLE:
            return compile_impl<EvmChain<EVMC_CONSTANTINOPLE>>(code, dbg_nm);

        case EVMC_PETERSBURG:
            return compile_impl<EvmChain<EVMC_PETERSBURG>>(code, dbg_nm);

        case EVMC_ISTANBUL:
            return compile_impl<EvmChain<EVMC_ISTANBUL>>(code, dbg_nm);

        case EVMC_BERLIN:
            return compile_impl<EvmChain<EVMC_BERLIN>>(code, dbg_nm);

        case EVMC_LONDON:
            return compile_impl<EvmChain<EVMC_LONDON>>(code, dbg_nm);

        case EVMC_PARIS:
            return compile_impl<EvmChain<EVMC_PARIS>>(code, dbg_nm);

        case EVMC_SHANGHAI:
            return compile_impl<EvmChain<EVMC_SHANGHAI>>(code, dbg_nm);

        case EVMC_CANCUN:
            return compile_impl<EvmChain<EVMC_CANCUN>>(code, dbg_nm);

        case EVMC_PRAGUE:
            return compile_impl<EvmChain<EVMC_PRAGUE>>(code, dbg_nm);

        default:
            MONAD_VM_ASSERT(rev == EVMC_OSAKA);
            return compile_impl<EvmChain<EVMC_OSAKA>>(code, dbg_nm);
        }
    }
}

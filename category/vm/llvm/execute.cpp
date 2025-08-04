#include <category/vm/llvm/emitter.hpp>
#include <category/vm/llvm/llvm_state.hpp>

#include <category/vm/compiler/ir/basic_blocks.hpp>
#include <category/vm/compiler/types.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/runtime/types.hpp>

#include <evmc/evmc.h>

#include <chrono>
#include <cstdint>
#include <format>
#include <fstream>
#include <iostream>
#include <memory>
#include <span>

#ifdef MONAD_VM_LLVM_DEBUG
static auto const *isq = std::getenv("MONAD_LLVM_DEBUG");
static bool dbg_dump = !(isq == nullptr);
#else
inline constexpr bool dbg_dump = false;
#endif

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

    template <evmc_revision Rev>
    std::shared_ptr<LLVMState> compile_impl(std::span<uint8_t const> code)
    {
        auto ptr = std::make_shared<LLVMState>();
        LLVMState &llvm = *ptr;

        auto ir = BasicBlocksIR(make_ir<Rev>(code));

        MONAD_VM_DEBUG_ASSERT(ir.is_valid());

        long dbg_pid = 0;

        if (dbg_dump) {
            auto now = std::chrono::system_clock::now();
            auto duration = now.time_since_epoch();
            auto milliseconds =
                std::chrono::duration_cast<std::chrono::milliseconds>(duration)
                    .count();
            dbg_pid = milliseconds;
            auto ir_str = std::format("{}", ir);
            std::ofstream out(std::format("t{}.ir", dbg_pid));
            out << ir_str;
            out.close();
            std::cerr << ir_str << '\n';
        }

        llvm.insert_symbol("rt_EXIT", (void *)&rt_exit);

        Emitter emitter{llvm, ir};
        emitter.emit_contract<Rev>();

        if (dbg_dump) {
            llvm.dump_module(std::format("t{}.ll", dbg_pid));
        }

        llvm.set_contract_addr();
        return ptr;
    }

    void execute(LLVMState &llvm, Context &ctx, uint256_t *evm_stack)
    {
        llvm_runtime_trampoline(
            evm_stack, &ctx, llvm.contract_addr, &ctx.exit_stack_ptr);
    }

    std::shared_ptr<LLVMState>
    compile(evmc_revision rev, std::span<uint8_t const> code)
    {
        switch (rev) {
        case EVMC_FRONTIER:
            return compile_impl<EVMC_FRONTIER>(code);

        case EVMC_HOMESTEAD:
            return compile_impl<EVMC_HOMESTEAD>(code);

        case EVMC_TANGERINE_WHISTLE:
            return compile_impl<EVMC_TANGERINE_WHISTLE>(code);

        case EVMC_SPURIOUS_DRAGON:
            return compile_impl<EVMC_SPURIOUS_DRAGON>(code);

        case EVMC_BYZANTIUM:
            return compile_impl<EVMC_BYZANTIUM>(code);

        case EVMC_CONSTANTINOPLE:
            return compile_impl<EVMC_CONSTANTINOPLE>(code);

        case EVMC_PETERSBURG:
            return compile_impl<EVMC_PETERSBURG>(code);

        case EVMC_ISTANBUL:
            return compile_impl<EVMC_ISTANBUL>(code);

        case EVMC_BERLIN:
            return compile_impl<EVMC_BERLIN>(code);

        case EVMC_LONDON:
            return compile_impl<EVMC_LONDON>(code);

        case EVMC_PARIS:
            return compile_impl<EVMC_PARIS>(code);

        case EVMC_SHANGHAI:
            return compile_impl<EVMC_SHANGHAI>(code);

        case EVMC_CANCUN:
            return compile_impl<EVMC_CANCUN>(code);

        default:
            MONAD_VM_ASSERT(rev == EVMC_PRAGUE);
            return compile_impl<EVMC_PRAGUE>(code);
        }
    }
}

#include <monad/vm/runtime/types.hpp>

extern "C" void monad_vm_runtime_exit [[noreturn]] (void *);

extern "C" void monad_vm_runtime_context_error_exit
    [[noreturn]] (monad::vm::runtime::Context *ctx)
{
    ctx->result.status = monad::vm::runtime::StatusCode::OutOfGas;
    monad_vm_runtime_exit(ctx->exit_stack_ptr);
}

namespace monad::vm::runtime
{
    void Context::exit [[noreturn]] (StatusCode code) noexcept
    {
        result.status = code;
        monad_vm_runtime_exit(exit_stack_ptr);
    }
}

#pragma once

namespace monad::vm::utils
{
#ifdef MONAD_COMPILER_TESTING
    extern bool is_fuzzing_monad_vm;
#else
    static constexpr bool is_fuzzing_monad_vm = false;
#endif
}

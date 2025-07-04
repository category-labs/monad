#ifdef MONAD_COMPILER_TESTING
    #include <cstdlib>
    #include <cstring>

namespace monad::vm::utils
{
    static auto const is_fuzzing_monad_vm_env =
        std::getenv("MONAD_COMPILER_FUZZING");
    bool is_fuzzing_monad_vm = is_fuzzing_monad_vm_env &&
                               std::strcmp(is_fuzzing_monad_vm_env, "1") == 0;
}
#endif

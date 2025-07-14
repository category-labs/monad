enable_language(C)

add_library(monad-vm-utils STATIC)

target_sources(monad-vm-utils PRIVATE
    "src/monad/vm/utils/debug.cpp"
    "src/monad/vm/utils/debug.hpp"
    "src/monad/vm/utils/evmc_utils.cpp"
    "src/monad/vm/utils/evmc_utils.hpp"
    "src/monad/vm/utils/evm-as.hpp"
    "src/monad/vm/utils/evm-as/builder.hpp"
    "src/monad/vm/utils/evm-as/compiler.cpp"
    "src/monad/vm/utils/evm-as/compiler.hpp"
    "src/monad/vm/utils/evm-as/instruction.hpp"
    "src/monad/vm/utils/evm-as/resolver.hpp"
    "src/monad/vm/utils/evm-as/validator.hpp"
    "src/monad/vm/utils/evm-as/utils.hpp"
    "src/monad/vm/utils/load_program.hpp"
    "src/monad/vm/utils/lru_weight_cache.hpp"
    "src/monad/vm/utils/rc_ptr.hpp"
    "src/monad/vm/utils/parser.cpp"
    "src/monad/vm/utils/parser.hpp"
    "src/monad/vm/utils/scope_exit.hpp"
    "src/monad/vm/utils/traits.hpp"
)

monad_compile_options(monad-vm-utils)

target_include_directories(monad-vm-utils
    PUBLIC src/
)

target_link_libraries(monad-vm-utils
    PUBLIC monad-vm::monad-vm-core
    PUBLIC monad-vm::monad-vm-runtime
    PRIVATE monad-vm::monad-vm-evm
)

add_library(monad-vm::monad-vm-utils ALIAS monad-vm-utils)

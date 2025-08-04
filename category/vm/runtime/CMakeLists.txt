enable_language(ASM)

add_library(monad-vm-runtime STATIC)

target_sources(monad-vm-runtime PRIVATE
    "allocator.hpp"
    "allocator.cpp"
    "cached_allocator.hpp"
    "bin.hpp"
    "call.hpp"
    "context.S"
    "context.cpp"
    "create.hpp"
    "data.hpp"
    "detail.hpp"
    "environment.hpp"
    "exit.S"
    "exit.cpp"
    "keccak.hpp"
    "log.hpp"
    "math.S"
    "math.hpp"
    "memory.hpp"
    "runtime.hpp"
    "selfdestruct.hpp"
    "storage.cpp"
    "storage.hpp"
    "storage_costs.hpp"
    "transmute.S"
    "transmute.hpp"
    "types.hpp"
    "uint256.cpp"
    "uint256.hpp"
)

monad_compile_options(monad-vm-runtime)

target_include_directories(monad-vm-runtime
    PUBLIC ${CATEGORY_MAIN_DIR}
)

target_link_libraries(monad-vm-runtime
    PUBLIC evmc::evmc
    PUBLIC ethash::keccak
    PUBLIC intx::intx
    PUBLIC monad-vm::monad-vm-core
    PUBLIC monad-vm::monad-vm-evm
)

add_library(monad-vm::monad-vm-runtime ALIAS monad-vm-runtime)
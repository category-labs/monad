enable_language(ASM)

add_library(monad-vm-runtime STATIC)

target_sources(monad-vm-runtime PRIVATE
    "src/monad/vm/runtime/allocator.hpp"
    "src/monad/vm/runtime/allocator.cpp"
    "src/monad/vm/runtime/cached_allocator.hpp"
    "src/monad/vm/runtime/bin.hpp"
    "src/monad/vm/runtime/call.hpp"
    "src/monad/vm/runtime/context.S"
    "src/monad/vm/runtime/context.cpp"
    "src/monad/vm/runtime/create.hpp"
    "src/monad/vm/runtime/data.hpp"
    "src/monad/vm/runtime/detail.hpp"
    "src/monad/vm/runtime/environment.hpp"
    "src/monad/vm/runtime/exit.S"
    "src/monad/vm/runtime/exit.cpp"
    "src/monad/vm/runtime/keccak.hpp"
    "src/monad/vm/runtime/log.hpp"
    "src/monad/vm/runtime/math.S"
    "src/monad/vm/runtime/math.hpp"
    "src/monad/vm/runtime/memory.hpp"
    "src/monad/vm/runtime/runtime.hpp"
    "src/monad/vm/runtime/selfdestruct.hpp"
    "src/monad/vm/runtime/storage.cpp"
    "src/monad/vm/runtime/storage.hpp"
    "src/monad/vm/runtime/storage_costs.hpp"
    "src/monad/vm/runtime/transmute.S"
    "src/monad/vm/runtime/transmute.hpp"
    "src/monad/vm/runtime/types.hpp"
    "src/monad/vm/runtime/uint256.cpp"
    "src/monad/vm/runtime/uint256.hpp"
)

monad_compile_options(monad-vm-runtime)

target_include_directories(monad-vm-runtime
    PUBLIC src/
)

target_link_libraries(monad-vm-runtime
    PUBLIC evmc::evmc
    PUBLIC ethash::keccak
    PUBLIC intx::intx
    PUBLIC monad-vm::monad-vm-core
    PUBLIC monad-vm::monad-vm-evm
)

add_library(monad-vm::monad-vm-runtime ALIAS monad-vm-runtime)
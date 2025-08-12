# Subcomponents

add_subdirectory(compiler)
add_subdirectory(core)
add_subdirectory(evm)
add_subdirectory(fuzzing)
add_subdirectory(interpreter)
add_subdirectory(runtime)
add_subdirectory(utils)

if(MONAD_COMPILER_LLVM)
    add_subdirectory(llvm)
endif()

# Main VM library (execution's entry point)

add_library(monad-vm)

target_sources(monad-vm PRIVATE
    "code.hpp"
    "compiler.cpp"
    "compiler.hpp"
    "varcode_cache.cpp"
    "varcode_cache.hpp"
    "vm.cpp"
    "vm.hpp"
)

monad_compile_options(monad-vm)

target_include_directories(monad-vm
    PUBLIC ${CATEGORY_MAIN_DIR}
)

target_link_libraries(monad-vm
    PUBLIC TBB::tbb
    PUBLIC intx::intx
    PUBLIC evmc::evmc
    PUBLIC asmjit::asmjit
    PUBLIC monad-vm::monad-vm-compiler
    PUBLIC monad-vm::monad-vm-interpreter
    PRIVATE monad-vm::monad-vm-core
    PRIVATE monad-vm::monad-vm-runtime
    PRIVATE monad-vm::monad-vm-utils
)

add_library(monad-vm::monad-vm ALIAS monad-vm)


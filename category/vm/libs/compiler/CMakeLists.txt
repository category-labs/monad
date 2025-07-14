add_library(monad-vm-compiler STATIC)

target_sources(monad-vm-compiler PRIVATE
    "src/monad/vm/compiler/transactional_unordered_map.hpp"
    "src/monad/vm/compiler/types.hpp"
    # IR
    "src/monad/vm/compiler/ir/basic_blocks.cpp"
    "src/monad/vm/compiler/ir/basic_blocks.hpp"
    "src/monad/vm/compiler/ir/instruction.hpp"
    "src/monad/vm/compiler/ir/local_stacks.cpp"
    "src/monad/vm/compiler/ir/local_stacks.hpp"
    # polymorphic types
    "src/monad/vm/compiler/ir/poly_typed.hpp"
    "src/monad/vm/compiler/ir/poly_typed.cpp"
    "src/monad/vm/compiler/ir/poly_typed/block.hpp"
    "src/monad/vm/compiler/ir/poly_typed/exceptions.hpp"
    "src/monad/vm/compiler/ir/poly_typed/infer.cpp"
    "src/monad/vm/compiler/ir/poly_typed/infer.hpp"
    "src/monad/vm/compiler/ir/poly_typed/infer_state.cpp"
    "src/monad/vm/compiler/ir/poly_typed/infer_state.hpp"
    "src/monad/vm/compiler/ir/poly_typed/kind.cpp"
    "src/monad/vm/compiler/ir/poly_typed/kind.hpp"
    "src/monad/vm/compiler/ir/poly_typed/strongly_connected_components.cpp"
    "src/monad/vm/compiler/ir/poly_typed/strongly_connected_components.hpp"
    "src/monad/vm/compiler/ir/poly_typed/subst_map.cpp"
    "src/monad/vm/compiler/ir/poly_typed/subst_map.hpp"
    "src/monad/vm/compiler/ir/poly_typed/unify.cpp"
    "src/monad/vm/compiler/ir/poly_typed/unify.hpp"
    # x86 backend
    "src/monad/vm/compiler/ir/x86.hpp"
    "src/monad/vm/compiler/ir/x86.cpp"
    "src/monad/vm/compiler/ir/x86/emitter.cpp"
    "src/monad/vm/compiler/ir/x86/emitter.hpp"
    "src/monad/vm/compiler/ir/x86/types.hpp"
    "src/monad/vm/compiler/ir/x86/virtual_stack.cpp"
    "src/monad/vm/compiler/ir/x86/virtual_stack.hpp"
)

monad_compile_options(monad-vm-compiler)

target_include_directories(monad-vm-compiler
    PUBLIC src/
)

target_link_libraries(monad-vm-compiler
    PUBLIC intx::intx
    PUBLIC asmjit::asmjit
    PUBLIC evmc::evmc
    PUBLIC evmone
    PUBLIC monad-vm::monad-vm-core
    PUBLIC monad-vm::monad-vm-evm
    PUBLIC monad-vm::monad-vm-runtime
    PUBLIC monad-vm::monad-vm-utils
)

add_library(monad-vm::monad-vm-compiler ALIAS monad-vm-compiler)
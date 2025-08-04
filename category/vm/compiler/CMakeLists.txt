add_library(monad-vm-compiler STATIC)

target_sources(monad-vm-compiler PRIVATE
    "transactional_unordered_map.hpp"
    "types.hpp"
    # IR
    "ir/basic_blocks.cpp"
    "ir/basic_blocks.hpp"
    "ir/instruction.hpp"
    "ir/local_stacks.cpp"
    "ir/local_stacks.hpp"
    # polymorphic types
    "ir/poly_typed.hpp"
    "ir/poly_typed.cpp"
    "ir/poly_typed/block.hpp"
    "ir/poly_typed/exceptions.hpp"
    "ir/poly_typed/infer.cpp"
    "ir/poly_typed/infer.hpp"
    "ir/poly_typed/infer_state.cpp"
    "ir/poly_typed/infer_state.hpp"
    "ir/poly_typed/kind.cpp"
    "ir/poly_typed/kind.hpp"
    "ir/poly_typed/strongly_connected_components.cpp"
    "ir/poly_typed/strongly_connected_components.hpp"
    "ir/poly_typed/subst_map.cpp"
    "ir/poly_typed/subst_map.hpp"
    "ir/poly_typed/unify.cpp"
    "ir/poly_typed/unify.hpp"
    # x86 backend
    "ir/x86.hpp"
    "ir/x86.cpp"
    "ir/x86/emitter.cpp"
    "ir/x86/emitter.hpp"
    "ir/x86/types.hpp"
    "ir/x86/virtual_stack.cpp"
    "ir/x86/virtual_stack.hpp"
)

monad_compile_options(monad-vm-compiler)

target_include_directories(monad-vm-compiler
    PUBLIC ${CATEGORY_MAIN_DIR}
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
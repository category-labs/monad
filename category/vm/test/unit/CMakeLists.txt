add_executable(unit-tests
    async_compile_tests.cpp
    compiler_tests.cpp
    evm_fixture.cpp
    evm_tests.cpp
    evm-as_tests.cpp
    monad_vm_interface_tests.cpp
    utils_tests.cpp
    uint256_tests.cpp
    rc_ptr_tests.cpp
    strongly_connected_components_tests.cpp
    transactional_unordered_map_tests.cpp
    subst_map_tests.cpp
    kind_tests.cpp
    unify_tests.cpp
    infer_tests.cpp
    type_check_tests.cpp
    stack_tests.cpp
    emitter_tests.cpp
    interpreter_tests.cpp
    lru_weight_cache_tests.cpp
    runtime/fixture.cpp
    runtime/transmute_tests.cpp
    runtime/math_tests.cpp
    runtime/memory_tests.cpp
    runtime/keccak_tests.cpp
    runtime/environment_tests.cpp
    runtime/storage_tests.cpp
    runtime/call_tests.cpp
    runtime/data_tests.cpp
    runtime/create_tests.cpp
)

if(MONAD_COMPILER_COVERAGE)
    target_compile_options(unit-tests PRIVATE -coverage)
    target_link_options(unit-tests PRIVATE -coverage)
endif()

monad_compile_options(unit-tests)
target_link_libraries(unit-tests
    monad-vm::monad-vm
    monad-vm::monad-vm-compiler
    monad-vm::monad-vm-fuzzing
    monad-vm::monad-vm-interpreter
    monad-vm::monad-vm-utils
    GTest::gtest_main
    evmc::mocked_host
)

target_include_directories(unit-tests
    PRIVATE
        "${TOP_CURRENT_BINARY_DIR}/test"
)

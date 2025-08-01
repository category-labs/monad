add_executable(execution-benchmarks)
target_sources(execution-benchmarks
    PRIVATE
        benchmarks.cpp
        benchmarktest.hpp
        benchmarktest_loader.cpp
)
target_include_directories(execution-benchmarks
    PRIVATE "${TOP_CURRENT_BINARY_DIR}/test"
    PRIVATE "${TEST_DATA_DIR}/unit/common/include"
)
monad_compile_options(execution-benchmarks)

target_link_libraries(execution-benchmarks
    PRIVATE benchmark::benchmark
    PRIVATE blockchain-test-vm
    PRIVATE evmone::state
    PRIVATE evmone::statetestutils
    PRIVATE evmone-blockchaintest-lib
    PRIVATE nlohmann_json::nlohmann_json
    PRIVATE monad_execution
    PRIVATE monad_core
)

# TODO(BSC): fix this via evmone
target_include_directories(execution-benchmarks
  PRIVATE "${CATEGORY_MAIN_DIR}/third_party/evmone/test/state"
  PRIVATE "${CATEGORY_MAIN_DIR}/third_party/evmone/test/statetest"
)

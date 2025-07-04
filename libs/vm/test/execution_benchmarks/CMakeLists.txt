add_executable(execution-benchmarks)
target_sources(execution-benchmarks
    PRIVATE
        benchmarks.cpp
        benchmarktest.hpp
        benchmarktest_loader.cpp
)
target_include_directories(execution-benchmarks
    PRIVATE
        "${TOP_CURRENT_BINARY_DIR}/test"
)
monad_compile_options(execution-benchmarks)

target_include_directories(execution-benchmarks
    PRIVATE
        "${TOP_CURRENT_BINARY_DIR}/test"
)

target_link_libraries(execution-benchmarks
    PRIVATE benchmark::benchmark
    PRIVATE blockchain-test-vm
    PRIVATE evmone::state
    PRIVATE evmone::statetestutils
    PRIVATE evmone-blockchaintest-lib
    PRIVATE nlohmann_json::nlohmann_json
)

# TODO(BSC): fix this via evmone
target_include_directories(execution-benchmarks
  PRIVATE "${ROOT_DIRECTORY}/third_party/evmone/test/state"
  PRIVATE "${ROOT_DIRECTORY}/third_party/evmone/test/statetest"
)

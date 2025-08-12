add_executable(long-benchmarks)
target_sources(long-benchmarks
    PRIVATE
        long-benchmarks.cpp
        code_0a743ba7304efcc9e384ece9be7631e2470e401e.hpp
        code_49206861766520746f6f206d7563682074696d65.hpp
        code_c917e98213a05d271adc5d93d2fee6c1f1006f75.hpp
        code_f529c70db0800449ebd81fbc6e4221523a989f05.hpp
        code_snailtracer.hpp
)
target_include_directories(long-benchmarks
    PRIVATE "${TOP_CURRENT_BINARY_DIR}/test"
    PRIVATE "${TEST_DATA_DIR}/unit/common/include"
)
monad_compile_options(long-benchmarks)

target_link_libraries(long-benchmarks
    PRIVATE benchmark::benchmark
    PRIVATE blockchain-test-vm
    PRIVATE evmone::state
    PRIVATE evmone::statetestutils
    PRIVATE evmone-blockchaintest-lib
    PRIVATE nlohmann_json::nlohmann_json
    PRIVATE monad_execution
)

# TODO(BSC): fix this via evmone
target_include_directories(long-benchmarks
  PRIVATE "${ROOT_DIRECTORY}/third_party/evmone/test/state"
  PRIVATE "${ROOT_DIRECTORY}/third_party/evmone/test/statetest"
)

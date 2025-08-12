add_executable(compile-benchmarks)
target_sources(compile-benchmarks
    PRIVATE
        compile_benchmarks.cpp
)
monad_compile_options(compile-benchmarks)

target_link_libraries(compile-benchmarks
    PRIVATE benchmark::benchmark
    PRIVATE monad_execution
)

target_include_directories(compile-benchmarks
    PRIVATE "${TOP_CURRENT_BINARY_DIR}/test"
    PRIVATE "${TEST_DATA_DIR}/unit/common/include"
)

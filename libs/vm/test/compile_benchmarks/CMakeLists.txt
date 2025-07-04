add_executable(compile-benchmarks)
target_sources(compile-benchmarks
    PRIVATE
        compile_benchmarks.cpp
)
monad_compile_options(compile-benchmarks)

target_link_libraries(compile-benchmarks
    benchmark::benchmark
    monad-vm::monad-vm-compiler
)

target_include_directories(compile-benchmarks
    PRIVATE
        "${TOP_CURRENT_BINARY_DIR}/test"
)
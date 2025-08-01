include(GoogleTest)

if(MONAD_COMPILER_TESTING)
    find_package(GTest REQUIRED)
endif()

if(MONAD_COMPILER_BENCHMARKS)
    find_package(benchmark REQUIRED)
endif()

if(MONAD_COMPILER_BENCHMARKS)
  add_subdirectory(compile_benchmarks)
  add_subdirectory(execution_benchmarks)
  add_subdirectory(long_benchmarks)
endif()

if(MONAD_COMPILER_TESTING)
  add_subdirectory(blockchain)
  add_subdirectory(fuzzer)
  add_subdirectory(unit)
  add_subdirectory(utils)
endif()

# The testing VM is shared between both the testing and benchmark setups, so we
# build it in both scenarios.
add_subdirectory(vm)

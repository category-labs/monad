add_executable(monad-compiler-fuzzer)

target_sources(monad-compiler-fuzzer PRIVATE
  assertions.cpp
  assertions.hpp
  compiler_hook.hpp
  fuzzer.cpp)

target_link_libraries(monad-compiler-fuzzer
  PRIVATE evmone::state
  PRIVATE evmone
  PRIVATE monad-vm::monad-vm-utils
  PRIVATE monad-vm::monad-vm-compiler
  PRIVATE monad-vm::monad-vm-fuzzing
  PRIVATE blockchain-test-vm
  PRIVATE CLI11::CLI11
)
monad_compile_options(monad-compiler-fuzzer)

# TODO(BSC): fix this via evmone
target_include_directories(monad-compiler-fuzzer
  PRIVATE "${ROOT_DIRECTORY}/third_party/evmone/test/state"
)
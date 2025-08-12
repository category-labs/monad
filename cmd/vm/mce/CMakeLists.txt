add_executable(mce)

target_sources(mce PRIVATE
  mce.cpp
  "src/instrumentable_decoder.hpp"
  "src/instrumentable_parser.hpp"
  "src/instrumentable_compiler.hpp"
  "src/instrumentable_vm.hpp"
  "src/instrumentation_device.hpp"
  "src/stopwatch.hpp")

target_include_directories(mce
  PUBLIC src/
  PUBLIC "${CATEGORY_MAIN_DIR}/third_party/evmone/test/state"
  PUBLIC "${CATEGORY_MAIN_DIR}/third_party/valgrind/cachegrind"
  PUBLIC "${CATEGORY_MAIN_DIR}/third_party/valgrind/include"
)

target_link_libraries(mce
  PRIVATE monad_execution
  PRIVATE evmone
  PRIVATE evmone::state
  PRIVATE CLI11::CLI11
  PRIVATE nlohmann_json::nlohmann_json
)

monad_compile_options(mce)

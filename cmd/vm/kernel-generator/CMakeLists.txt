add_executable(kernel-generator)

target_sources(kernel-generator PRIVATE
  kernel-generator.cpp)

target_include_directories(kernel-generator
    PRIVATE "${TOP_CURRENT_BINARY_DIR}/test"
    PRIVATE "${TEST_DATA_DIR}/unit/common/include"
)

target_link_libraries(kernel-generator
  PRIVATE monad_execution
  PRIVATE CLI11::CLI11
)

monad_compile_options(kernel-generator)

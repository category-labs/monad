add_library(
  monad_unit_test_common STATIC
  ${PROJECT_SOURCE_DIR}/test/unit/common/include/monad/test/config.hpp
  ${PROJECT_SOURCE_DIR}/test/unit/common/include/monad/test/environment.hpp
  ${PROJECT_SOURCE_DIR}/test/unit/common/include/monad/test/resource_owning_fixture.hpp
)

target_include_directories(
  monad_unit_test_common PUBLIC ${PROJECT_SOURCE_DIR}/test/unit/common/include)
set_target_properties(monad_unit_test_common PROPERTIES LINKER_LANGUAGE CXX)
target_link_libraries(monad_unit_test_common PUBLIC monad_execution monad_async)
monad_compile_options(monad_unit_test_common)

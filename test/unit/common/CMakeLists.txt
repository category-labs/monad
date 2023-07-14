add_library(
    monad_unit_test_common STATIC
    ${PROJECT_SOURCE_DIR}/test/unit/common/include/monad/test/config.hpp
    ${PROJECT_SOURCE_DIR}/test/unit/common/include/monad/test/environment.hpp
    ${PROJECT_SOURCE_DIR}/test/unit/common/include/monad/test/trie_fixture.hpp
    ${PROJECT_SOURCE_DIR}/test/unit/common/include/monad/test/one_hundred_updates.hpp
    ${PROJECT_SOURCE_DIR}/test/unit/common/include/monad/test/make_db.hpp
)

target_include_directories(
    monad_unit_test_common
    PUBLIC ${PROJECT_SOURCE_DIR}/test/unit/common/include
)
target_link_libraries(monad_unit_test_common PUBLIC monad)
monad_compile_options(monad_unit_test_common)

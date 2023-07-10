enable_testing()

find_package(GTest REQUIRED)
include(GoogleTest)

add_executable(monad-fuzztests trie.cpp)

target_link_libraries(monad-fuzztests PRIVATE monad monad_unit_test_common)

fuzztest_setup_fuzzing_flags()

link_fuzztest(monad-fuzztests)
gtest_discover_tests(
    monad-fuzztests PROPERTIES ENVIRONMENT "FUZZTEST_STACK_LIMIT=4194304"
)

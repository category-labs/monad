enable_testing()

find_package(GTest REQUIRED)
include(GoogleTest)

add_executable(
  monad-fuzztests
  trie.cpp
)

# If you have other dependencies than FuzzTest, link them:
target_link_libraries(monad-fuzztests PRIVATE monad)

link_fuzztest(monad-fuzztests)
gtest_discover_tests(monad-fuzztests)

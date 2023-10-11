add_executable(monad-ethereum-test)
target_link_libraries(monad-ethereum-test PRIVATE nlohmann_json::nlohmann_json
                                                  monad GTest::gtest)
target_sources(
  monad-ethereum-test
  PRIVATE include/general_state_test_types.hpp
          include/from_json.hpp
          include/ethereum_test.hpp
          include/general_state_test.hpp
          src/ethereum_test.cpp
          src/general_state_test.cpp
          src/main.cpp)

target_include_directories(
  monad-ethereum-test PUBLIC ${PROJECT_SOURCE_DIR}/test/ethereum_test/include)
target_include_directories(
  monad-ethereum-test PUBLIC ${PROJECT_SOURCE_DIR}/test/unit/common/include)
monad_compile_options(monad-ethereum-test)

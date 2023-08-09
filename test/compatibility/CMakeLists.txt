find_package(CLI11 REQUIRED)
find_package(nlohmann_json REQUIRED)

add_library(from_json from_json.hpp)
target_link_libraries(from_json PUBLIC monad nlohmann_json::nlohmann_json)

add_executable(compatibility compatibility.cpp)

target_link_libraries(compatibility PUBLIC monad evmone CLI11::CLI11 nlohmann_json::nlohmann_json GTest::gtest)
target_include_directories(compatibility PUBLIC nlohmann_json::nlohman_json)
monad_compile_options(compatibility)

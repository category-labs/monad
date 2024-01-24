include_directories(${CMAKE_CURRENT_SOURCE_DIR})

find_package(CLI11 REQUIRED)

add_executable(replay_ethereum replay_ethereum.cpp)
monad_compile_options(replay_ethereum)

target_link_libraries(replay_ethereum PRIVATE monad CLI11::CLI11)

add_executable(replay_ethereum_state_delta replay_ethereum_state_delta.cpp)
monad_compile_options(replay_ethereum_state_delta)

target_link_libraries(replay_ethereum_state_delta PRIVATE monad CLI11::CLI11)

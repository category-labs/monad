include_directories(${CMAKE_CURRENT_SOURCE_DIR})

find_package(CLI11 REQUIRED)

add_executable(replay_ethereum_block_db replay_ethereum_block_db.cpp)
monad_compile_options(replay_ethereum_block_db)

target_link_libraries(replay_ethereum_block_db PRIVATE monad CLI11::CLI11)
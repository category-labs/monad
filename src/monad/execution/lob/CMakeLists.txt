include_directories(${CMAKE_CURRENT_SOURCE_DIR})

find_package(CLI11 REQUIRED)

add_executable(lob lob.cpp)
monad_compile_options(lob)

target_link_libraries(lob PRIVATE monad CLI11::CLI11)

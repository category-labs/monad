find_package(CLI11 REQUIRED)

add_executable(monad_exe monad.cpp)
target_link_libraries(monad_exe PRIVATE monad CLI11::CLI11)

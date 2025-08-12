add_executable(directory-type-check directory_type_check.cpp)
monad_compile_options(directory-type-check)
target_link_libraries(directory-type-check PRIVATE monad_execution)

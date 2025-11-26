add_executable(blockcapd capture_blocks.cpp driver.cpp)

target_compile_features(blockcapd PRIVATE cxx_std_23)
target_compile_options(blockcapd PRIVATE -Wall -Wextra -Wconversion -Werror)
target_link_libraries(blockcapd PRIVATE monad_event zstd::libzstd_static)

set_target_properties(blockcapd PROPERTIES RUNTIME_OUTPUT_NAME monad-blockcapd)

install(TARGETS blockcapd)

set(CMAKE_ASM_FLAGS_INIT "-march=haswell")
set(CMAKE_C_FLAGS_INIT "-march=haswell -fsanitize=address -fsanitize=undefined -fsanitize-address-use-after-scope -fno-omit-frame-pointer -g -DFUZZING_BUILD_MODE_UNSAFE_FOR_PRODUCTION -UNDEBUG -fsanitize-coverage=inline-8bit-counters -fsanitize-coverage=trace-cmp -fsanitize-coverage=pc-table")
set(CMAKE_CXX_FLAGS_INIT "-march=haswell -fsanitize=address -fsanitize=undefined -fsanitize-address-use-after-scope -fno-omit-frame-pointer -g -DFUZZING_BUILD_MODE_UNSAFE_FOR_PRODUCTION -UNDEBUG -fsanitize-coverage=inline-8bit-counters -fsanitize-coverage=trace-cmp -fsanitize-coverage=pc-table")
#set(CMAKE_EXE_LINKER_FLAGS_INIT "-fuse-ld=lld")

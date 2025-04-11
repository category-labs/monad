set(CMAKE_ASM_FLAGS_INIT "-march=haswell")
set(CMAKE_C_FLAGS_INIT "-march=haswell -fsanitize=thread -fno-omit-frame-pointer -g -fsanitize-blacklist=/mnt/raid0/monad/monad-trie/monad-core/toolchains/blacklist.tsan")
set(CMAKE_CXX_FLAGS_INIT "-march=haswell -fsanitize=thread -fno-omit-frame-pointer -g -fsanitize-blacklist=/mnt/raid0/monad/monad-trie/monad-core/toolchains/blacklist.tsan")

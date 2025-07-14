set(CMAKE_ASM_FLAGS_INIT "-march=haswell")
set(CMAKE_C_FLAGS_INIT "-march=haswell -fsanitize=thread -fno-omit-frame-pointer -Wno-error=tsan -g")
set(CMAKE_CXX_FLAGS_INIT "-march=haswell -fsanitize=thread -fno-omit-frame-pointer -Wno-error=tsan -g")

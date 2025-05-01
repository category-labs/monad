set(CMAKE_ASM_FLAGS_INIT "-march=haswell")
set(CMAKE_C_FLAGS_INIT "-march=haswell -fsanitize=address -fsanitize=undefined -fno-omit-frame-pointer -g")
set(CMAKE_CXX_FLAGS_INIT "-march=haswell -fsanitize=address -fsanitize=undefined -fno-omit-frame-pointer -g")
set(CMAKE_EXE_LINKER_FLAGS_INIT "-fsanitize=address -fsanitize=undefined")

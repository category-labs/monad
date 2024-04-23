# This toolchain is good for an AVX2 CPU with arbitrary precision arithmetic extensions
set(CMAKE_ASM_FLAGS_INIT "-march=haswell")
set(CMAKE_C_FLAGS_INIT "-march=haswell")
set(CMAKE_CXX_FLAGS_INIT "-march=haswell")

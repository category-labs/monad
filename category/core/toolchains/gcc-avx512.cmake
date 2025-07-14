# This toolchain is good for a basic AVX512 CPU
set(CMAKE_ASM_FLAGS_INIT "-march=skylake-avx512")
set(CMAKE_C_FLAGS_INIT "-march=skylake-avx512")
set(CMAKE_CXX_FLAGS_INIT "-march=skylake-avx512")

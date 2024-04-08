#if defined(__x86_64__)
    #if defined(__AVX512F__)
        #include <crypto/sha/asm/keccak1600-avx512.S>
    #elif defined(__AVX2__)
        #include <crypto/sha/asm/keccak1600-avx2.S>
    #else
        #error avx2 or avx512 required
    #endif
#else
    #error unsupported arch
#endif

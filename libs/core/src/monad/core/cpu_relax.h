#pragma once

#ifdef __x86_64__
    #define cpu_relax() __builtin_ia32_pause();
#elif __aarch64__
    // Per Linux arch/arm64/include/asm/processor.h
    #define cpu_relax() asm volatile("yield" ::: "memory");
#else
    #error unsupported arch
#endif

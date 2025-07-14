#pragma once

#ifdef __x86_64__
    #define cpu_relax() __builtin_ia32_pause();
#else
    #error unsupported arch
#endif

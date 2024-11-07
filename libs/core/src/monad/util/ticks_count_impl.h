#pragma once

#include "ticks_count.h"

#ifdef __cplusplus
extern "C"
{
#endif
static inline monad_cpu_ticks_count_t
get_ticks_count(MONAD_CPP_STD memory_order rel)
{
    monad_cpu_ticks_count_t ret;
#if defined(__i386__) || defined(_M_IX86) || defined(__x86_64__) ||            \
    defined(_M_X64)
    unsigned lo, hi, aux;
    switch (rel) {
    case MONAD_CPP_STD memory_order_acquire:
        __asm__ __volatile__("rdtsc\nlfence" : "=a"(lo), "=d"(hi));
        break;
    case MONAD_CPP_STD memory_order_release:
        __asm__ __volatile__("mfence\nrdtscp\n"
                             : "=a"(lo), "=d"(hi), "=c"(aux));
        break;
    case MONAD_CPP_STD memory_order_acq_rel:
    case MONAD_CPP_STD memory_order_seq_cst:
        __asm__ __volatile__("mfence\nrdtscp\nlfence"
                             : "=a"(lo), "=d"(hi), "=c"(aux));
        break;
    default:
        __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
        break;
    }
    ret = (uint64_t)lo | ((uint64_t)hi << 32);
#elif defined(__aarch64__) || defined(_M_ARM64)
    uint64_t value = 0;
    switch (rel) {
    case MONAD_CPP_STD memory_order_acquire:
        __asm__ __volatile__("mrs %0, PMCCNTR_EL0; dsb"
                             : "=r"(value)); // NOLINT
        break;
    case MONAD_CPP_STD memory_order_release:
        __asm__ __volatile__("dsb; mrs %0, PMCCNTR_EL0"
                             : "=r"(value)); // NOLINT
        break;
    case MONAD_CPP_STD memory_order_acq_rel:
    case MONAD_CPP_STD memory_order_seq_cst:
        __asm__ __volatile__("dsb; mrs %0, PMCCNTR_EL0; dsb"
                             : "=r"(value)); // NOLINT
        break;
    default:
        __asm__ __volatile__("mrs %0, PMCCNTR_EL0" : "=r"(value)); // NOLINT
        break;
    }
    ret = value;
#else
    #error "Unsupported platform"
#endif
    return ret;
}

#ifdef __cplusplus
}
#endif

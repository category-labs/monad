#pragma once

/**
 * @file
 *
 * This file defines an architecture-dependent macro to accelerate the
 * performance of code containing spin loops. These are used in the spinlock
 * implementation, but should appear in any kind of tight atomic
 * synchronization loop.
 *
 * A surface-level explanation of what these intrinsics do can be found in
 * the description of the PAUSE instruction in the Intel Developers Manual,
 * Volume 2B. A more detailed explanation of why these are needed can be found
 * here:
 *
 *   https://stackoverflow.com/questions/12894078/what-is-the-purpose-of-the-pause-instruction-in-x86
 */

#ifdef __x86_64__
    #define monad_spinloop_hint() __builtin_ia32_pause()
#elif __aarch64__
    // Per Linux arch/arm64/include/asm/processor.h
    #define monad_spinloop_hint() asm volatile("yield" ::: "memory")
#else
    #define monad_spinloop_hint()
    #warning this CPU type should define monad_spinloop_hint()
#endif

#pragma once

#include <monad/config.h>

#include <stddef.h>

#ifdef __cplusplus
extern "C"
{
#endif

//! \brief A type representing the tick count on the CPU
typedef uint64_t monad_cpu_ticks_count_t;

/*! \brief Return the current monotonic CPU tick count.

`rel` affects how the CPU tick count is measured, and it is the same as for
atomics:

- `memory_order_relaxed`: Read the count in the most efficient way possible,
which may be plus or minus two hundred instructions from accurate (i.e. plus
or minus up to 100 nanoseconds, but usually a lot less). Usually costs about
25-45 cycles, but other instructions can execute concurrently.
- `memory_order_acquire`: Do not execute any instructions after reading the
count until the count has been read, but instructions preceding reading the
count may be executed after reading the count.
- `memory_order_release`: Do not execute instructions preceding reading the
count after reading the count, but instructions after reading the count may be
executed before reading the count.
- `memory_order_acq_rel` and `memory_order_seq_cst`: Instructions preceding
reading the count will be completed in full before reading the count, and
instructions after reading the count will not begin executing until the count
has been read. This is perfectly accurate, but comes with a substantial
performance impact as it stalls the CPU and flushes its pipelines. 100-120
cycles would be expected as a minimum, often more as it also disrupts prefetch
and branch prediction.
*/
extern monad_cpu_ticks_count_t
monad_get_ticks_count(MONAD_CPP_STD memory_order rel);

//! \brief Return how many CPU ticks per second there are. The first caller
//! of this will need to wait up to one second for the number to be calculated.
extern monad_cpu_ticks_count_t monad_ticks_per_second();

#ifdef __cplusplus
}
#endif

#pragma once

#include "config.h"

#include <liburing.h>

// Must come after <liburing.h>, otherwise breaks build on clang
#include <stdatomic.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C"
{
#endif

//! \brief Returns a temporary directory in which `O_DIRECT` files definitely
//! work
extern char const *monad_async_working_temporary_directory();

//! \brief Creates a temporary file, writing the path created into the buffer.
//! You will need to unlink this after yourself and close the file descriptor it
//! returns.
extern int monad_async_make_temporary_file(char *buffer, size_t buffer_len);

//! \brief Creates already deleted file so no need to clean it up
//! after. You will need to close the file descriptor it returns.
extern int monad_async_make_temporary_inode();

//! \brief How this Linux accounts for memory
enum monad_async_memory_accounting_kind
{
    monad_async_memory_accounting_kind_unknown,
    //! \brief This Linux has been configured for strict memory accounting
    monad_async_memory_accounting_kind_commit_charge,
    //! \brief This Linux has been configured for over commit memory accounting
    monad_async_memory_accounting_kind_over_commit
};
//! \brief Return how this Linux accounts for memory
extern enum monad_async_memory_accounting_kind monad_async_memory_accounting();

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
extern monad_async_cpu_ticks_count_t
monad_async_get_ticks_count(MONAD_ASYNC_CPP_STD memory_order rel);

//! \brief Return how many CPU ticks per second there are. The first caller
//! of this will need to wait up to one second for the number to be calculated.
extern monad_async_cpu_ticks_count_t monad_async_ticks_per_second();

#ifdef __cplusplus
}
#endif

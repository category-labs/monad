#include <monad/core/tl_tid.h>

#define _GNU_SOURCE
#include <unistd.h>

static_assert(__builtin_types_compatible_p(pid_t, int));

__thread int tl_tid = 0;

void init_tl_tid()
{
    tl_tid = gettid();
}

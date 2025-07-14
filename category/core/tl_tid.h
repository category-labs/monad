#pragma once

#ifdef __cplusplus
extern "C"
{
#endif

#include <category/core/likely.h>

extern __thread int tl_tid;

void init_tl_tid();

static inline int get_tl_tid()
{
    if (MONAD_UNLIKELY(!tl_tid)) {
        init_tl_tid();
    }
    return tl_tid;
}

#ifdef __cplusplus
}
#endif

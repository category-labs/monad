#pragma once

#include <monad/config.h>

#ifndef MONAD_CONTEXT_PUBLIC_CONST
    #if defined(MONAD_ASYNC_SOURCE) || defined(MONAD_CONTEXT_SOURCE)
        #define MONAD_CONTEXT_PUBLIC_CONST
    #else
        #define MONAD_CONTEXT_PUBLIC_CONST const
    #endif
#endif

#ifdef __cplusplus
extern "C"
{
#endif

#define MONAD_CONTEXT_CHECK_RESULT(...) MONAD_CHECK_RESULT(__VA_ARGS__)

#ifdef __cplusplus
}
#endif

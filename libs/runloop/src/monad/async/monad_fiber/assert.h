#pragma once

#include <monad/core/assert.h>
#include <stdlib.h>

#define MONAD_CCALL_ASSERT(Expression)                                         \
    {                                                                          \
        int _return_value_ = Expression;                                       \
        (void)_return_value_;                                                  \
        if (MONAD_LIKELY(!_return_value_)) {                                   \
        }                                                                      \
        else {                                                                 \
            errno = _return_value_;                                            \
            perror(#Expression " failed");                                     \
        }                                                                      \
        MONAD_ASSERT(!_return_value_);                                         \
    }

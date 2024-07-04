#include "context.h"

thread_local monad_fiber_context_t monad_fiber_main_context_ = {
    .fiber = NULL,
#if defined(MONAD_USE_TSAN)
    .tsan_fiber = NULL,
#endif
#if defined(MONAD_USE_ASAN)
    .asan = {.fake_stack = NULL, .stack_bottom = NULL, .stack_size = 0u},
#endif
    .name = NULL};

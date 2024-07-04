#pragma once

#include "fcontext.h"

#include <stdbool.h>

#if MONAD_ASYNC_HAVE_ASAN
    #include <sanitizer/asan_interface.h>
#endif
#if MONAD_ASYNC_HAVE_TSAN
    #include <sanitizer/tsan_interface.h>
#endif
#if MONAD_ASYNC_HAVE_VALGRIND
    #include <valgrind/valgrind.h>
#endif

#if defined(__cplusplus)
extern "C"
{
#endif

#if defined(MONAD_USE_ASAN)
struct monad_fiber_context_asan_fake_stack
{
    void *fake_stack;
    void const *stack_bottom;
    size_t stack_size;
};

static inline void monad_fiber_start_switch(
    struct monad_fiber_context_asan_fake_stack *from,
    struct monad_fiber_context_asan_fake_stack *to)
{
    __sanitizer_start_switch_fiber(
        from != NULL ? &from->fake_stack : NULL,
        to->stack_bottom,
        to->stack_size);
}

static inline void monad_fiber_finish_switch(
    struct monad_fiber_context_asan_fake_stack *from,
    struct monad_fiber_context_asan_fake_stack *to)
{
    __sanitizer_finish_switch_fiber(
        to->fake_stack, &from->stack_bottom, &from->stack_size);
}

#endif

typedef struct monad_fiber_context
{
    fcontext_t fiber;
#if defined(MONAD_USE_TSAN)
    void *tsan_fiber;
#endif

#if defined(MONAD_USE_ASAN)
    struct monad_fiber_context_asan_fake_stack asan;
#endif
    char const *name;
    // potential additions: context_local data, unwind code, tracing (for
    // debugging) and names (which could be used with tsan) and we can add a
    // vtable here

    // there is NO exit function at this moment, but we could add this.
    // it's unspecified what happens if you destroy the main context, as it
    // would always be a leak one would assume.
} monad_fiber_context_t;

// are in this fiber at the moment
#define monad_fiber_is_current(This) (This->fiber != NULL)

monad_fiber_context_t *monad_fiber_main_context();
void monad_fiber_set_name(monad_fiber_context_t *, char const *name);

// the return is the context we're resumed from
monad_fiber_context_t *monad_fiber_context_switch(
    monad_fiber_context_t *from, monad_fiber_context_t *to);
monad_fiber_context_t *monad_fiber_context_switch_with(
    monad_fiber_context_t *from, monad_fiber_context_t *to,
    monad_fiber_context_t *(*func)(monad_fiber_context_t *, void *), void *arg);

static size_t const monad_fiber_default_stack_size = 128 * 1024;
monad_fiber_context_t *monad_fiber_context_callcc(
    monad_fiber_context_t *from, size_t stack_size, bool protected_stack,
    monad_fiber_context_t *(*func)(
        void * /* func_arg */, monad_fiber_context_t * /* fiber */,
        monad_fiber_context_t * /* from */),
    void *func_arg);

#if defined(__cplusplus)
}
#endif

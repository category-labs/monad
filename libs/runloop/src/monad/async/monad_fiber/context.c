#include "context.h"

#include <monad/core/assert.h>

#include <assert.h>
#include <errno.h>
#include <malloc.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

monad_fiber_context_t *monad_fiber_context_switch(
    monad_fiber_context_t *from, monad_fiber_context_t *to)
{
    MONAD_DEBUG_ASSERT(to != NULL);
#if defined(MONAD_USE_ASAN)
    monad_fiber_start_switch(&from->asan, &to->asan);
#endif

#if defined(MONAD_USE_TSAN)
    MONAD_DEBUG_ASSERT(to->tsan_fiber != NULL);
    __tsan_switch_to_fiber(to->tsan_fiber, 0);
#endif

    fcontext_t fiber = to->fiber;
    to->fiber = NULL;

    struct transfer_t t = jump_fcontext(fiber, from);

    // in a chain of resumptions t.fctx might point to another coro!
    // it may also be zero if we're resumed from a destructed fiber
    monad_fiber_context_t *resumed_from = (monad_fiber_context_t *)t.data;

    if (resumed_from) {
#if defined(MONAD_USE_ASAN)
        monad_fiber_finish_switch(&resumed_from->asan, &from->asan);
#endif
        resumed_from->fiber = t.fctx;
    }
    return resumed_from;
}

struct monad_fiber_context_switch_with_impl_t
{
    monad_fiber_context_t *ctx;
    monad_fiber_context_t *(*func)(monad_fiber_context_t *, void *);
    void *data;
};

static struct transfer_t
monad_fiber_context_switch_with_impl(struct transfer_t fn)
{
    struct monad_fiber_context_switch_with_impl_t *tmp =
        (struct monad_fiber_context_switch_with_impl_t *)fn.data;

    tmp->ctx->fiber = fn.fctx;
    monad_fiber_context_t *next = (*tmp->func)(tmp->ctx, tmp->data);

    fn.fctx = next->fiber;
    fn.data = next;
    return fn;
}

monad_fiber_context_t *monad_fiber_context_switch_with(
    monad_fiber_context_t *from, monad_fiber_context_t *to,
    monad_fiber_context_t *(*func)(monad_fiber_context_t *, void *), void *arg)
{
#if defined(MONAD_USE_ASAN)
    monad_fiber_start_switch(&from->asan, &to->asan);
#endif

#if defined(MONAD_USE_TSAN)
    __tsan_switch_to_fiber(to->tsan_fiber, 0);
#endif

    fcontext_t fiber = to->fiber;
    to->fiber = NULL;

    struct monad_fiber_context_switch_with_impl_t tmp = {
        .ctx = from, .func = func, .data = arg};
    MONAD_DEBUG_ASSERT(fiber != NULL);
    struct transfer_t t =
        ontop_fcontext(fiber, &tmp, &monad_fiber_context_switch_with_impl);
    // in a chain of resumptions t.fctx might point to another coro!
    // it may also be zero if we're resumed from a destructed fiber

    monad_fiber_context_t *resumed_from = (monad_fiber_context_t *)t.data;
    if (resumed_from) {
#if defined(MONAD_USE_ASAN)
        monad_fiber_finish_switch(&resumed_from->asan, &from->asan);
#endif
        resumed_from->fiber = t.fctx;
    }
    else {
        assert(
            t.fctx ==
            NULL); // if there's no context the fiber must be destroyed as well!
    }
    return resumed_from;
}

extern thread_local monad_fiber_context_t monad_fiber_main_context_;

monad_fiber_context_t *monad_fiber_main_context()
{
    return &monad_fiber_main_context_;
}

typedef struct monad_fiber
{
    monad_fiber_context_t context;
    size_t allocated_size;
    bool is_protected;
} monad_fiber_t;

struct destroyer
{
    struct monad_fiber *this;
    monad_fiber_context_t *to;
};

static struct transfer_t self_destroy_impl(struct transfer_t t)
{
    // monad_
    struct destroyer d = *(struct destroyer *)t.data;
    struct monad_fiber *this = d.this;
#if defined(MONAD_USE_TSAN)
    __tsan_destroy_fiber(this->context.tsan_fiber);
#endif

#if defined(MONAD_USE_ASAN)
    // asan finish goes here.
    monad_fiber_finish_switch(&this->context.asan, &d.to->asan);
#endif

    free((char *)this + sizeof(monad_fiber_t) - this->allocated_size);
    struct transfer_t n = {d.to->fiber, NULL};
    return n;
}

static struct transfer_t self_destroy_protected_impl(struct transfer_t t)
{
    // monad_
    struct destroyer d = *(struct destroyer *)t.data;
    struct monad_fiber *this = d.this;

#if defined(MONAD_USE_TSAN)
    __tsan_destroy_fiber(this->context.tsan_fiber);
#endif

#if defined(MONAD_USE_ASAN)
    // asan finish goes here.
    monad_fiber_finish_switch(&this->context.asan, &d.to->asan);
#endif

    munmap(
        (char *)this + sizeof(monad_fiber_t) - this->allocated_size,
        this->allocated_size);
    struct transfer_t n = {d.to->fiber, NULL};
    return n;
}

struct callcc_p
{
    monad_fiber_context_t *from;
    monad_fiber_t *fiber;
    monad_fiber_context_t *(*func)(
        void *, monad_fiber_context_t *, monad_fiber_context_t *);
    void *arg;
};

static void __attribute__((noinline)) monad_fiber_impl(struct transfer_t t)
{
    struct callcc_p call = *(struct callcc_p *)t.data;
    monad_fiber_context_t *from = call.from, *to;

#if defined(MONAD_USE_ASAN)
    monad_fiber_finish_switch(&from->asan, &call.fiber->context.asan);
#endif
    from->fiber = t.fctx;
    to = call.func(call.arg, &call.fiber->context, from);

#if defined(MONAD_USE_TSAN)
    __tsan_switch_to_fiber(to->tsan_fiber, 0);
#endif

    if (from->name) {
        free((char *)from->name);
        from->name = NULL;
    }

    struct destroyer d = {.this = call.fiber, .to = to};
    MONAD_DEBUG_ASSERT(to->fiber != NULL);
    fcontext_t fctx = to->fiber;
    to->fiber = NULL;
#if defined(MONAD_USE_ASAN)
    monad_fiber_start_switch(NULL, &d.to->asan);
#endif

    ontop_fcontext(
        fctx,
        &d,
        call.fiber->is_protected ? &self_destroy_protected_impl
                                 : &self_destroy_impl);
    assert("Must never be reached" == NULL);
}

monad_fiber_context_t *monad_fiber_context_callcc(
    monad_fiber_context_t *from, size_t stack_size, bool protected_stack,
    monad_fiber_context_t *(*func)(
        void * /* func_arg */, monad_fiber_context_t * /* fiber */,
        monad_fiber_context_t * /* from */),
    void *func_arg)
{
    void *memory = NULL;
    size_t allocated_size = stack_size;
    if (protected_stack) {
        // taken from boost.context
        size_t const page_size = (size_t)sysconf(_SC_PAGESIZE);
        size_t const pages = (stack_size + page_size - 1) / page_size;
        allocated_size = (pages + 1) * page_size;

#if defined(MAP_ANON)
        memory = mmap(
            0,
            allocated_size,
            PROT_READ | PROT_WRITE,
            MAP_PRIVATE | MAP_ANONYMOUS,
            -1,
            0);
#else
        memory = mmap(
            0,
            allocated_size,
            PROT_READ | PROT_WRITE,
            MAP_PRIVATE | MAP_ANONYMOUS,
            -1,
            0);
#endif
        if (memory != NULL) {
            if (mprotect(memory, page_size, PROT_NONE) != 0) {
                int err = errno;
                (void)munmap(memory, allocated_size);
                fprintf(
                    stderr,
                    "NOTE: if mprotect() fails to set the guard page, and "
                    "there is plenty of memory free, the cause is the Linux "
                    "kernel VMA region limit being hit whereby no process may "
                    "allocate more than 64k mmaps. You can safely raise "
                    "vm.max_map_count = 1048576 if needed.\n");
                errno = err; // reset the error
                return NULL;
            }
        }
    }
    else {
        memory = malloc(stack_size);
    }

    if (memory == NULL) { // errno can still be checked
        if (errno == ENOMEM) {
            int err = errno;
            fprintf(
                stderr,
                "NOTE: if mmap() fails to allocate a stack, and there is "
                "plenty of memory free, the cause is the Linux kernel VMA "
                "region limit being hit whereby no process may allocate more "
                "than 64k mmaps. You can safely raise vm.max_map_count = "
                "1048576 if needed.\n");
            errno = err;
        }
        return NULL;
    }

    void *sp = ((char *)memory + allocated_size) - sizeof(monad_fiber_t);
    monad_fiber_t *fb = (monad_fiber_t *)sp;
    fb->allocated_size = allocated_size;
    fb->context.name = NULL;
    fb->context.fiber = make_fcontext(
        sp, stack_size - sizeof(monad_fiber_t), &monad_fiber_impl);
    fb->is_protected = protected_stack;

#if defined(MONAD_USE_TSAN)
    fb->context.tsan_fiber = __tsan_create_fiber(0);
    __tsan_switch_to_fiber(fb->context.tsan_fiber, 0);
#endif

#if defined(MONAD_USE_ASAN)
    fb->context.asan.fake_stack = NULL;
    fb->context.asan.stack_size = stack_size - sizeof(monad_fiber_t);
    fb->context.asan.stack_bottom = (char *)sp - fb->context.asan.stack_size;
    monad_fiber_start_switch(&from->asan, &fb->context.asan);
#endif
    MONAD_ASSERT(from != NULL);
    struct callcc_p cc = {
        .from = from, .fiber = fb, .func = func, .arg = func_arg};

    fcontext_t ctx = fb->context.fiber;
    fb->context.fiber = NULL;
    struct transfer_t t = jump_fcontext(ctx, &cc);

    monad_fiber_context_t *resumed_from = (monad_fiber_context_t *)t.data;
    if (resumed_from) {
#if defined(MONAD_USE_ASAN)
        monad_fiber_finish_switch(&resumed_from->asan, &from->asan);
#endif
        resumed_from->fiber = t.fctx;
    }
    return resumed_from;
}

void monad_fiber_set_name(monad_fiber_context_t *this, char const *name)
{

    this->name = realloc((void *)this->name, strlen(name) + 1);
    strcpy((char *)this->name, name);
#if defined(MONAD_USE_TSAN)
    __tsan_set_fiber_name(this->tsan_fiber, this->name);
#endif
}

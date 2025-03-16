/**
 * @file
 *
 * This file contains the implementation of the performance-insensitive
 * functions in the fiber library
 */

#include <errno.h>
#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <sys/mman.h>
#include <unistd.h>

#include <monad/core/assert.h>
#include <monad/core/c_result.h>
#include <monad/core/likely.h>
#include <monad/core/spinlock.h>
#include <monad/fiber/fiber.h>

static monad_fiber_attr_t g_default_fiber_attr = {
    .stack_size = 1 << 17, // 128 KiB
    .alloc = nullptr // Default allocator
};

static atomic_uint g_last_fiber_id = 0;

static int
alloc_fiber_stack(struct monad_fiber_stack *stack, size_t *stack_size)
{
    int const stack_protection = PROT_READ | PROT_WRITE;
    int const stack_flags = MAP_ANONYMOUS | MAP_PRIVATE
#if defined(MAP_STACK)
                            | MAP_STACK
#endif
        ;

    size_t const page_size = (size_t)getpagesize();
    if (stack_size == nullptr || stack == nullptr) {
        return EFAULT;
    }
    if (*stack_size - page_size < page_size) {
        return EINVAL;
    }
    stack->stack_base =
        mmap(nullptr, *stack_size, stack_protection, stack_flags, -1, 0);
    if (stack->stack_base == MAP_FAILED) {
        return errno;
    }
    if (mprotect(stack->stack_base, page_size, PROT_NONE) == -1) {
        return errno;
    }
    *stack_size -= page_size;
    stack->stack_bottom = (uint8_t *)stack->stack_base + page_size;
    stack->stack_top = (uint8_t *)stack->stack_bottom + *stack_size;
    return 0;
}

static void dealloc_fiber_stack(struct monad_fiber_stack stack)
{
    size_t const mapped_size = (size_t)((uint8_t const *)stack.stack_top -
                                        (uint8_t const *)stack.stack_base);
    munmap(stack.stack_base, mapped_size);
}

[[noreturn]] static void fiber_entrypoint(struct monad_transfer_t xfer_from)
{
    // Entry point of a "user" fiber. When this function is called, we're
    // running on the fiber's stack for the first time (after the most recent
    // call to monad_fiber_set_function). We cannot directly return from this
    // function, but we can transfer control back to the execution context that
    // jumped here. In our model, that is the context that called the
    // `monad_fiber_run` function, which is typically a regular thread running
    // a lightweight scheduler. The info needed to transfer control back to the
    // suspension point in `monad_fiber_run` is contained within the `xfer_from`
    // argument
    monad_c_result mcr;
    monad_thread_executor_t *thr_exec;
    monad_fiber_t *self;

    _monad_finish_switch_to_fiber(xfer_from);
    thr_exec = xfer_from.data;
    self = thr_exec->cur_fiber;

    // Call the user fiber function
    mcr = self->ffunc(self->fargs);

    // The fiber function returned, which appears as a kind of suspension to
    // the caller
    MONAD_SPINLOCK_LOCK(&self->lock);
    _monad_suspend_fiber(self, MF_STATE_FINISHED, MF_SUSPEND_RETURN, mcr);

    // This should be unreachable (monad_fiber_run should never resume us after
    // a "return" suspension)
    abort();
}

int monad_fiber_create(monad_fiber_attr_t const *attr, monad_fiber_t **fiber)
{
    monad_memblk_t memblk;
    struct monad_fiber_stack fiber_stack;
    monad_fiber_t *f;
    size_t stack_size;
    int rc;

    if (fiber == nullptr) {
        return EFAULT;
    }
    *fiber = nullptr;
    if (attr == nullptr) {
        attr = &g_default_fiber_attr;
    }
    stack_size = attr->stack_size;
    rc = alloc_fiber_stack(&fiber_stack, &stack_size);
    if (rc != 0) {
        return rc;
    }
    rc = monad_cma_alloc(
        attr->alloc, sizeof **fiber, alignof(monad_fiber_t), &memblk);
    if (rc != 0) {
        dealloc_fiber_stack(fiber_stack);
        return rc;
    }
    *fiber = f = memblk.ptr;
    memset(f, 0, sizeof *f);
    monad_spinlock_init(&f->lock);
    f->fiber_id = ++g_last_fiber_id;
    f->state = MF_STATE_INIT;
    f->stack = fiber_stack;
    f->create_attr = *attr;
    f->self_memblk = memblk;

    return 0;
}

void monad_fiber_destroy(monad_fiber_t *fiber)
{
    MONAD_ASSERT(fiber != nullptr);
    dealloc_fiber_stack(fiber->stack);
    monad_cma_dealloc(fiber->create_attr.alloc, fiber->self_memblk);
}

int monad_fiber_set_function(
    monad_fiber_t *fiber, monad_fiber_prio_t priority,
    monad_fiber_ffunc_t *ffunc, monad_fiber_args_t fargs)
{
    size_t stack_size;

    MONAD_SPINLOCK_LOCK(&fiber->lock);
    switch (fiber->state) {
    case MF_STATE_INIT:
        [[fallthrough]];
    case MF_STATE_FINISHED:
        // It is legal to modify the fiber in these states
        break;

    default:
        // It is not legal to modify the fiber in these states
        MONAD_SPINLOCK_UNLOCK(&fiber->lock);
        return EBUSY;
    }
    stack_size = (size_t)(fiber->stack.stack_top - fiber->stack.stack_bottom);
    fiber->state = MF_STATE_CAN_RUN;
    fiber->md_suspended_ctx = monad_make_fcontext(
        fiber->stack.stack_top, stack_size, fiber_entrypoint);
    fiber->priority = priority;
    fiber->ffunc = ffunc;
    fiber->fargs = fargs;
    ++fiber->stats.total_reset;
    MONAD_SPINLOCK_UNLOCK(&fiber->lock);
    return 0;
}

int monad_fiber_get_name(monad_fiber_t *fiber, char *name, size_t size)
{
    int rc;
    if (name == nullptr) {
        return EFAULT;
    }
    MONAD_SPINLOCK_LOCK(&fiber->lock);
    rc = strlcpy(name, fiber->name, size) >= size ? ERANGE : 0;
    MONAD_SPINLOCK_UNLOCK(&fiber->lock);
    return rc;
}

int monad_fiber_set_name(monad_fiber_t *fiber, char const *name)
{
    int rc;
    if (name == nullptr) {
        return EFAULT;
    }
    MONAD_SPINLOCK_LOCK(&fiber->lock);
    rc = strlcpy(fiber->name, name, sizeof fiber->name) > MONAD_FIBER_NAME_LEN
             ? ERANGE
             : 0;
    MONAD_SPINLOCK_UNLOCK(&fiber->lock);
    return rc;
}

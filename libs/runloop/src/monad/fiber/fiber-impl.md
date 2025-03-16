# `monad_fiber` implementation notes

## Basic design

The fiber implementation has two essential objects:

1. `monad_thread_executor_t` - much the same way as a single CPU core
   is an execution resource to run threads, a single thread is an
   execution resource to run fibers. Each thread that wants to call
   `monad_fiber_run` is explicitly represented by a `monad_thread_executor_t`
   object; the first time a thread calls `monad_fiber_run`, one of these
   objects is created to represent it

2. `monad_fiber_t` - this object represents a fiber, which is an execution
   resource for a user defined function that can be voluntarily suspended
   and resumed. It owns an execution stack, and some machinery for scheduling
   and synchronization with other fibers

## Context switching

The context switching logic is deliberately asymmetric: all context switching
takes place between a user-created fiber and an ordinary thread of execution.
In other words, fibers cannot be nested: calling `monad_fiber_run` from inside
a fiber returns `ENOTSUP` ("operation not supported") rather than starting a
nested execution.

The original implementation was symmetric: it was legal to call
`monad_fiber_run` when already running a fiber, and this would start a nested
fiber. This doubled the size of the implementation and the runtime cost of a
context switch, but was never used. For now, this capability has been removed.

The context switching operation is divided into two layers:

1. **Machine-independent layer** - this is shared by
   all architectures and addresses how the execution transfers from an
   ordinary thread context to a fiber conext, and back; this code is mostly
   in `fiber_inline.h`, and is inherently asymmetric (the switch is always
   between one fiber context and one ordinary thread context)

2. **Machine-dependent layer** - this consists of only two functions,
   `monad_make_fcontext` and `monad_jump_fcontext` which were imported
   from the Boost.Context third-party library. These are the original
   names of the functions, but with the `monad_` prefix added. They are
   the low-level context switch functions implemented in assembly
   language for a particular CPU architecture, calling convention, and ABI.

In the machine-independent layer, the execution context of the thread
that calls `monad_fiber_run` is modeled by `monad_thread_executor_t` and
the execution context of a fiber is modeled by `monad_fiber_t`.

The only piece of data needed by the machine-dependent layer is a single
pointer that represents the value of the stack pointer where execution was
suspended, upon its last context switch. In both structures, this field is
called `md_suspended_ctx` (where `md` is "machine-dependent"). The
machine-dependent context switching *is* inherently symmetric: the code
from Boost is mostly unchanged, and does not know any details about
`struct monad_fiber` or `struct monad_thread_executor`.

### Machine-independent switching

#### Context switching into a fiber

The machine-independent part of a context switch into a fiber is
handled in two phases:

1. The switch starts inside of `monad_fiber_run`
2. The switch finishes by calling `_monad_finish_switch_to_fiber`

What distinguishes these two phases is which stack we are running on.
Although both phases take place on the same thread, the `monad_fiber_run`
function executes on the thread's ordinary execution stack, and the
`_monad_finish_switch_to_fiber` function is called once control has
transferred to the fiber, and is running on the fiber's stack.

It is `monad_fiber_run` that calls the machine-dependent context switch
function, which causes the stack switch to happen at the CPU level.
Immediately after the CPU-level switch occurs, we are running on the
stack of the resumed (or newly-started) fiber, and the previously running
thread context is now suspended; this resumption site must immediately call
`_monad_finish_switch_to_fiber` to complete the switch. This performs
critical book-keeping tasks, such as saving the `md_suspended_ctx` of the
calling thread in its `monad_thread_executor_t` structure.

`_monad_finish_switch_to_fiber` is called in two places: at the start of
the fiber (see `fiber_entrypoint`), or immediately after a fiber resumes
after being suspended. It takes a single `struct monad_transfer_t` parameter,
a small structure that passes information between the "switched from" and
"switched to" stacks by the machine-dependent layer. It contains the
`monad_thread_executor_t` of the thread that started the context switch,
and the `md_suspended_ctx` of the suspension point inside `monad_fiber_run`
when the switch occurred.

Typically a fiber will *migrate* between threads, as each worker thread
selects the highest priority fiber that is ready to run; this is why the
`monad_thread_executor_t` is passed between the low-level jump routines:
a fiber can be resumed on a different thread than it was originally
suspended on.

#### Context switching out of a fiber

Fibers run until they voluntarily suspend themselves. This happens via an
explicit call to `monad_fiber_yield`, going to sleep on a synchronization
primitive (which calls `_monad_fiber_sleep`), or when the fiber function
returns (which returns control back to `fiber_entrypoint`). These all call
the same low-level suspension function, `_monad_suspend_fiber`, which
performs a context switch back to the thread that originally called
`monad_fiber_run`.

Because fibers are always suspended inside of `_monad_suspend_fiber`, this
function is also the point where fibers are resumed.

### Machine-dependent context switching

The tricky part of understanding how this works is becoming familiar with
the following interesting pattern: when we perform a `monad_jump_fcontext`,
we are suspended and control is transferred away from us. When control
transfers back to us, it has the appearance of *returning* from the original
jump function, which had jumped away. To understand this code at a deep
level, I suggest working through how the lowest-level machine-dependent
assembly jump functions work between two execution contexts. It may take
a few hours to understand all the details and internalize them, but this
will demystify the essential pattern: when we *return* from a jump, we've
been resumed and are on the original stack, but are potentially on a
different host thread than when we were suspended on.

# `monad_fiber` implementation notes

## Basic design

The fiber implementation has three essential objects:

1. `monad_thread_executor_t` - much the same way as a single CPU core
   is an execution resource to run threads, a single thread is an
   execution resource to run fibers. Each thread that wants to call
   `monad_fiber_run` is explicitly represented by a `monad_thread_executor_t`
   object; the first time a thread calls `monad_fiber_run`, one of these
   objects is created to represent it

2. `monad_context` - this object represents an execution context (i.e.,
   what is actually running on a thread) which can be suspended before
   context switching into something else, on that same thread. This
   type comes from the `monad_context_c` library, and is shared with the
   I/O framework

3. `monad_fiber_t` - this object represents a fiber, which is an execution
   resource for a user defined function that can be voluntarily suspended
   and resumed; from an implementation perspective, this is a `monad_context`
   augmented with the additional fields needed to be a proper user fiber,
   e.g., a scheduling priority, the fiber function that the user wishes to
   run, etc.

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

A single context switch is divided across three layers:

1. **Fiber layer** - this defines the interface for how execution transfers
   from an ordinary thread context to a fiber context, and back; this code is
   mostly in `fiber_inline.h`, and is inherently asymmetric (the switch is
   always between one fiber context and one ordinary thread context)

2. **Context layer** - the actual switch operation is delegated to the
   `monad_context_c` library. This library is able to perform a context
   switch using various context-switching implementations, e.g.,
   `setjmp(3)/longjmp(3)`-based, `Boost.Context`-based, or C++
   coroutines. Each context switching backend has different advantages
   and drawbacks: some integrate better with debuggers, others are faster,
   etc. This layer presents a low-level generic interface that works
   with all of them, but does not itself perform the switch at the hardware
   level

3. **Machine-dependent layer** - these are lowest-level functions called
   by a specific context switching backend in `monad_context_c`; they
   actually cause the  stack switch to happen at the CPU level. These
   functions directly manipulate stack frames, and are implemented in
   assembly language for a particular CPU architecture, calling convention,
   and ABI. For example, the `setjmp(3)` and `longjmp(3)` routines that
   are part of libc

### Running a fiber

#### Context switching into a fiber

At the fiber layer, a context switch _into_ a fiber is handled in three
phases:

1. The context switch starts inside of `monad_fiber_run`
2. `monad_context_c` requires the context switch to trampoline through a
   helper function, called `_monad_start_switch_to_fiber`
3. The context switch finishes by calling `_monad_finish_switch_to_fiber`

What distinguishes phases 1 & 2 from phase 3 is which stack we are running
on. Although all phases take place on the same thread, both `monad_fiber_run`
and `_monad_start_switch_to_fiber` execute on the thread's ordinary execution
stack. By contrast, the `_monad_finish_switch_to_fiber` function is called
once CPU control has transferred to the fiber: it is running on the fiber's
stack.

It is `_monad_start_switch_to_fiber` that (indirectly) invokes the
machine-dependent context switch function, which causes the stack switch to
happen at the CPU level. This happens by calling the
`suspend_and_call_resume` function in `monad_context_c` library, which
will call the machine-dependent switch function for the current switching
backend implementation. The concrete switching implementation is stored
in an object called a "switcher", which is unique to each particular thread
and is owned by the `monad_thread_executor_t` object.

Immediately after the CPU-level switch occurs, we are running on the
stack of the resumed (or newly-started) fiber, and the previously running
thread context is now suspended; this resumption site must immediately call
`_monad_finish_switch_to_fiber` to complete the switch.

`_monad_finish_switch_to_fiber` is called in two places: at the start of
the fiber (see `fiber_entrypoint`), or immediately after a fiber resumes
after being suspended.

Typically a fiber will *migrate* between threads, as each worker thread
selects the highest priority fiber that is ready to run; for a given
fiber, two successive calls to `_monad_finish_switch_to_fiber` might occur
on two different threads.

#### Context switching out of a fiber

Fibers run until they voluntarily suspend themselves or return. Suspension
happens via an explicit call to `monad_fiber_yield`, or going to sleep on a
synchronization primitive (which calls `_monad_fiber_sleep`). Both operations
call the same internal suspension function, `_monad_suspend_fiber`, which
performs a context switch back to the thread that originally called
`monad_fiber_run`. The switch itself is again performed using the switcher's
`suspend_and_call_resume` function.

Because fibers are always suspended inside of `_monad_suspend_fiber`, this
function is also the point where fibers are resumed, which appears as the
`suspend_and_call_resume` call returning.

Returning from the fiber function is handled differently: in that case,
control returns back to the `monad_context_c` library, which in turn
calls `fiber_detach` to perform the return book-keeping at the fiber layer.
`monad_context_c` will switch back to the `monad_fiber_run` function: there
is no `suspend_and_call_resume` call visible in the `monad_fiber` code.

### Context switching

The tricky part of understanding how this works is becoming familiar with
the following interesting pattern: when we perform a
`suspend_and_call_resume`, we are suspended and control is transferred away
from us. When control transfers back to us, it has the appearance of
*returning* from the `suspend_and_call_resume` function call, which had
jumped away. Notably, we might be on a different host thread when resumed.

To understand this code at a deep level, I suggest working through how the
lowest-level machine-dependent assembly jump functions work between two
execution contexts, e.g., the `monad_make_fcontext` and
`monad_jump_fcontext` functions. It may take a few hours to understand all
the details and internalize them, but this will demystify the essential
pattern: when we *return* from a jump, we've been resumed and are on the
original stack, but are potentially on a different host thread than when
we were suspended.

The higher-level interface we directly use (`monad_context_c`) retains
this property.

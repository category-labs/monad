# `monad_fiber` design notes

## Goals and overview

### An analogy to threads

The design goal of the `monad_fiber` library can be explained via an
analogy to the UNIX threading model. UNIX threads involve the following:

- **Thread objects** - the POSIX `pthread` library allows an application
  to explicitly create, start, and stop threads
- **Synchronization objects (explicit coordination)** - `pthread` offers
  synchronization primitives, such as `pthread_mutex_t`, that allow threads
  to *explicitly* coordinate with each other
- **I/O operations (implicit coordination)** - the kernel offers blocking
  I/O routines such as `read(2)` and `write(2)`. These routines may start
  long-running operations which cause a thread to yield the CPU and go to
  sleep, allowing other threads to run. This allows threads to *implicitly*
  coordinate
- **Scheduling** - the kernel offers a thread scheduler, which is
  responsible for deciding which threads will run on which CPUs; it also
  communicates with the coordination mechanisms (the synchronization
  primitives and the I/O subsystem) to know when it is time to "wake up"
  a sleeping thread

Needless to say, such a system is complex.

### Simplicity: the goal of `monad_fiber`

Fiber libraries are often full-fledged "frameworks", because they try to
capture all the sophistication and features that an OS-level threading
system has. The `monad_fiber` code makes an effort to be much simpler, and
decidedly does not have many features. It is designed to do only what the
downstream code needs at the current moment. It sacrifices being generic
and extensible in favor of being simple, and thus (hopefully) easy to
change as our internal needs change.

`monad_fiber` offers three things:

1. A fiber object, `monad_fiber_t`, that allows the creation and running
   of fibers
2. A small number of synchronization primitives; these are added (and
   removed) as needed
3. A trivial scheduling model, based on a thread-safe priority queue

The coupling between the three parts is minimal, and occurs in only a few
lines of code.

There is no support for I/O operations. I/O-based voluntary context
switching does exist within the monad codebase, but its scheduling needs
and cooperation mechanism are completely different, so it is handled in a
different part of the system.

The implementation is meant to be clear; ideally a programmer can
understand it fully without much trouble. Take this with a grain of salt
though: context-switching code can be tricky, so understanding all the
implementation details will require some time investment!

### "Hello, world!" using fibers

The following listing shows a "Hello, World!" example written in C that
only uses a fiber object. This example contains no synchronization
primitives and thus does not need any scheduling code (the fiber is
run "manually"). The fiber prints a "Hello, World!" style message three
times, suspending itself after each message is printed. After the last
message, the fiber finishes.

```.c
#include <assert.h>
#include <err.h>
#include <errno.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sysexits.h>

#include <monad/core/c_result.h>
#include <monad/fiber/fiber.h>

// This is the function that will run on the fiber
monad_c_result say_hello_fiber_function(monad_fiber_args_t mfa)
{
    // The fiber greets you by your name, which is passed in as the fiber's
    // first function argument
    char const *const name = (char const *)mfa.arg[0];

    // Say hello, then suspend the fiber
    printf("Hello, %s!\n", name);
    monad_fiber_yield(monad_c_make_success(0));

    // When we reach here, we've been run again; we resume from the
    // suspension point of the yield immediately above. We'll say hello
    // again, then suspend again
    printf("Welcome back, %s!\n", name);
    monad_fiber_yield(monad_c_make_success(0));

    // Resumed for the final time; say goodbye, then return. Returning from
    // the fiber function suspends the fiber until it is given a new function
    // to run
    printf("Farewell, %s!\n", name);
    return monad_c_make_success(0);
}

int main(int argc, char **argv)
{
    int rc;
    monad_fiber_t *hello_fiber;
    char const *name;
    monad_allocator_t *const alloc = nullptr; // Use default allocator
    monad_fiber_attr_t const fiber_attr = {
        .stack_size = 1UL << 17, // 128 KiB stack
        .alloc = alloc
    };

    // This application says hello to you using a fiber; it expects your name
    // as the first (and only) positional argument
    if (argc != 2) {
        errx(EX_USAGE, "usage: %s <your-name>", argv[0]);
    }
    name = argv[1];

    // Create the fiber, passing in our creation attributes
    rc = monad_fiber_create(&fiber_attr, &hello_fiber);
    if (rc != 0) {
        errno = rc;
        err(1, "monad_fiber_create failed");
    }

    // Tell the fiber what function to run; the second argument is
    // the scheduling priority, which doesn't matter in this example;
    // the last parameter is passed into the fiber function, as the
    // argument. We pass a pointer to our name
    rc = monad_fiber_set_function(
        hello_fiber,
        MONAD_FIBER_PRIO_HIGHEST,
        say_hello_fiber_function,
        (monad_fiber_args_t){.arg = {(uintptr_t)name}});
    assert(rc == 0);

    // Run the fiber until the first suspension point; this will print
    // "Hello, <name>!", suspend the fiber function, and then our call to
    // monad_fiber_run will return. If nothing goes wrong, the return code
    // will be 0. The second parameter (which is nullptr here) allows us to
    // obtain information about why the fiber suspended; in this example we
    // don't care, so we pass nullptr
    rc = monad_fiber_run(hello_fiber, nullptr);
    assert(rc == 0);

    // Run the fiber again, until it yields again; this will print
    // "Welcome back, <name>!" and then yield back to us once more
    rc = monad_fiber_run(hello_fiber, nullptr);
    assert(rc == 0);

    // Run the fiber a final time. This will print "Farewell, <name>!" and then
    // the fiber function will return. The return won't look much different to
    // us than the yields above: the fiber will suspend and monad_fiber_run will
    // return 0 to us, as before. The difference is, we can't run the fiber
    // again. If, instead of passing nullptr as the second argument, we instead
    // passed a pointer to a `monad_fiber_suspend_info_t`, we could get more
    // information about the suspension. Namely, that it was a return and not a
    // yield, and we could also read the `monad_c_result` return code. However,
    // we don't care in this example.
    rc = monad_fiber_run(hello_fiber, nullptr);
    assert(rc == 0);

    // Try to run the fiber one more time; we can't do it since the fiber
    // function returned, so this will fail and return the errno-domain error
    // code ENXIO
    rc = monad_fiber_run(hello_fiber, nullptr);
    assert(rc == ENXIO);

    // At this point, we could reuse the fiber's resources to run the function
    // a second time. To prepare for a second run, we would reset the function:
    rc = monad_fiber_set_function(
        hello_fiber,
        MONAD_FIBER_PRIO_HIGHEST,
        say_hello_fiber_function,
        (monad_fiber_args_t){.arg = {(uintptr_t)name}});
    assert(rc == 0);

    // However, that's enough for today; destroy the fiber and exit.
    monad_fiber_destroy(hello_fiber);
    return 0;
}
```

## Where is the code?

1. For the fibers themselves:
   - `fiber.h` - defines the interface for fibers, i.e., the public
     functions and the central `monad_fiber_t` structure
   - `fiber_inline.h` - most of the implementation is here, so it can be
     inlined for performance reasons
   - `fiber.c` - implementation file for fiber functions whose performance
     is not critical
   - `fiber_thr.c` - an implementation file which contains the `thread_local`
     state for the `monad_thread_executor_t` objects

2. For the synchronization primitives:
   - `fiber_channel.h` - implements a "channel" synchronization primitive
     for fiber objects; for a description of channels see
     [here](https://en.wikipedia.org/wiki/Channel_(programming))
   - `fiber_semaphore.h` - implements a semaphore synchronization
     primitive for fibers

3. The "scheduler"
   - `monad_run_queue.h` - defines the interface for a simple thread-safe
     priority queue of `monad_fiber_t*` objects
   - `monad_run_queue.c` - implementation file for `monad_run_queue.h`

### Why is "scheduler" in quotes above?

To keep the design simple and less monolithic, the `monad_fiber` library does
not have a full-fledged scheduler, or any higher-level abstractions such as a
task pool, run-loop, worker threads, etc.

The intention is for the user code to solve its problem directly, creating
complex objects only if it needs them, and using `monad_fiber` as a bare-bones
helper module. The only point of coupling between the three parts of a fiber
system is the priority queue, `monad_run_queue_t`.

A `monad_fiber_t` keeps track of an associated `monad_run_queue_t*`, and when
the fiber is signaled for wakeup by a synchronization primitive, the fiber
"wakes up" by re-enqueueing itself back on this associated priority queue.

The library does not run anything by itself. Instead it offers a single
function (`monad_fiber_run`) to start or resume a fiber, which runs the fiber's
function until that function reaches a suspension point -- at which point
`monad_fiber_run` just returns. The library does little beyond that.

The only other "automatic" thing it does is re-enqueue the fiber on a priority
queue if a synchronization primitive wakes the fiber. The user of the library
must create their own concepts like worker threads, pools, etc. to
enqueue/dequeue fibers from a `monad_run_queue_t`. The exact topology and way
of doing this is not specified by the library.

## `monad_fiber_t` basic design

### How to use `monad_fiber_t`

A fiber is an execution resource for an ordinary function having this
signature type:

```.h
typedef monad_c_result (monad_fiber_ffunc_t)(monad_fiber_args_t);
```

The fiber runs this function until the function decides to suspend itself,
either by yielding, returning, or going to sleep on some synchronization
condition that is not met yet (e.g., waiting for a semaphore to signal).
When the fiber suspends, the current thread will begin executing the code
for a different fiber. The suspended fiber may later be resumed, at which
point execution continues at the point where it left off.

#### Why `monad_fiber_args_t`?

In conventional C programming, a user-provided function takes a single
opaque argument for the user's private data. This usually has type
`void *`, e.g., as in `pthread_create(3)`. Instead of doing this, fibers
take an instance of this structure:

```.h
struct monad_fiber_args
{
    uintptr_t arg[MONAD_FIBER_MAX_ARGS];
};
```

This design is meant to be friendlier to C++ clients of the C library.
C++ has stronger idiomatic use of value types than C does, e.g., types
like `std::string_view` or `std::span<double>`. Because C programs use
value semantics more sparsely, the natural number of function parameters
is usually just one: you either have a fundamental type, or you pass a
pointer to a more complex type.

For C++, there are many useful, value-like types that are the size of two
or three pointers. Forcing these to be located at a stable memory address
just so a memory reference to them can be passed around can be burdensome.
For example, even though a `std::string_view` points to stable,
externally-managed memory, the `std::string_view` object itself is usually
a stack-allocated value type. It is an ephemeral object without a stable
address.

The solution chosen here is to wrap a small set of opaque arguments into
a C value type, which is nonetheless small enough to be passed in registers
after it is disaggregated into scalars during optimization.

#### Running and suspending fibers

Most of the implementation can be understood by thinking about exactly
how and when a fiber performs a context switch. The model we follow is:

- A fiber is started or resumed by calling the `monad_fiber_run`
  function, passing in the `monad_fiber_t*` describing the fiber that the
  user wants to run; that is, the context that _calls_ `monad_fiber_run`
  will switch into the given fiber and begin (or resume) running its
  associated function

- When a fiber suspends or returns, it jumps back to the context that
  was executing previously. This is the context that was running the code
  for `monad_fiber_run` in the first place, so the suspension of a fiber
  appears to the caller of `monad_fiber_run` as the `monad_fiber_run`
  function call returning back to them

- Consequently, the function that calls `monad_fiber_run` is always
  a lightweight scheduler: it decides to run fibers somehow, and typically
  calls `monad_fiber_run` in a loop, with the sequence of fibers it
  wishes to run

- The most obvious design is to use a single global priority queue
  (a `monad_run_queue_t` object). Each worker takes the
  next-highest-priority fiber and runs it until it suspends

- Returning and suspension are different: a fiber whose function has
  suspended can be resumed by another call to `monad_fiber_run`. If a
  fiber function has returned however, it cannot be run again. Once a
  a fiber's function has returned, the fiber's resources (i.e., its stack)
  can be reused to run a new function. A fiber that is only suspended
  cannot be changed to run a different function, however. This is
  because the fiber holds the suspended state for the function: its
  active stack frames. These are potentially holding stack-local C++
  objects which should be destroyed first. Attempting to change the
  function when the fiber is suspended will return `EBUSY`

Here is an example of how you might build such a worker thread (this
is just an API example, the current implementation is more complex):

```c
int rc;
monad_fiber_t *fiber;
monad_fiber_suspend_info_t suspend_info;
monad_run_queue_t *const run_queue = /* initialize a fiber priority queue*/

while (!atomic_load(&done)) {
    // Poll the priority queue for the highest priority fiber that's ready
    // to run
    fiber = monad_run_queue_try_pop(run_queue);

    if (fiber == nullptr) {
        continue; // Nothing is ready to run, poll again
    }

    // Run the fiber until it suspends
    rc = monad_fiber_run(fiber, &suspend_info);

    if (rc != 0) {
        /* something went wrong */
    }
    if (suspend_info.suspend_type == MONAD_FIBER_SUSPEND_RETURN) {
        /* fiber function returned; can't run it anymore */
    }
}
```

## Synchronization primitives

The primary synchronization primitives offered are *channels*
(`monad_fiber_channel_t`) and *semaphores* (`monad_fiber_semaphore_t`).
Although semaphores can be implemented in terms of channels, they simplify
memory management for the end user if the full power of a channel is not
needed.

### Channel memory management (or "what is `monad_fiber_msghdr_t`?)

At any given time, a `monad_fiber_channel_t` is in one of three states:

   1. Completely empty: no available messages and no waiting fibers
   2. Has no available messages, but has one or more fibers waiting for
      a message to be be published
   3. Has no waiting fibers, but has enqueued messages waiting for a
      fiber to dequeue them

Conceptually, a fiber channel is just two FIFO queues. At least one queue
is always empty, and potentially both are empty. If one of the queues is
*not* empty, it is potentially arbitrarily long: the API imposes no
limit on the number of messages that can be enqueued, or the number of
fibers that can be waiting.

Fiber channel performance is important, so we do not want the channel
itself to dynamically allocate memory during the `push` or `pop`
operations. There is an easy, zero-overhead solution for the queue of
waiting fibers: because a `monad_fiber_t` can only wait on one
synchronization primitive at a time, the `monad_fiber_t` structure itself
contains a linkage object for an intrusive list of all fibers waiting
on a condition. This is the `TAILQ_ENTRY(monad_fiber) wait_link` field.
When a fiber needs to wait on a condition, it links itself to the end
of an intrusive list representing the wait queue, requiring no additional
memory.

The situation for messages is different, since there is not already an
existing object representing the message to store the list linkage inside of.

The API solution is to offer such an object, and let the client decide how
to manage the memory for it. There are two different blocks of memory that
need to be managed for a channel message:

   - The memory that stores the message payload itself

   - The memory for a structure called `monad_fiber_msghdr_t`. This "message
     header" object has two fields: the location of the message payload
     buffer mentioned above (stored in a `struct iovec`) and a linkage object
     so it can be linked into an intrusive list of all waiting messages on the
     same wait queue

A typical approach it to create a message structure like this, where the
message header and the payload buffer are part of a single object:

```c
struct my_message
{
    monad_fiber_msghdr_t hdr;
    char payload[256];
};
```

A convenience method called `monad_fiber_msghdr_init_trailing` can be used
to initialize the payload buffer to a fixed size occurring after the header
member, e.g.,

```c
my_message msg;

monad_fiber_msghdr_init_trailing(&msg.hdr, sizeof msg.payload);
assert(msg.msg_buf.iov_base == msg.my_buf);
```

Using the `msghdr` object, messages can be enqueued on a
`monad_fiber_channel_t` without any dynamic memory allocation. The memory
management for the message objects themselves is an issue left entirely to
the user.

### Why are semaphores offered as a primitive?

A semaphore is like a channel whose message is empty, and serves only
as a "wakeup ticket," i.e., a dummy message whose meaning is that one
fiber should wake up. Since the messages have no content, there is no
need for any of the complex external memory management that exists with
channels. If a semaphore can be used instead of a channel, it is a
significant win for the end user.

### Notes on the `monad_fiber_semaphore_thread_acquire_one` function

This function is a simple, limited hack to solve the following problem:
synchronization primitives are only designed to work between fibers, but
in limited circumstances, the "sleeping" side can be an ordinary thread.
This is not a general purpose facility; it can only be used in a limited
way.

#### Why ordinary threads sleep on semaphores

In the current db implementation, an ordinary thread of execution is
sometimes treated as though it is running on a fiber. This is an API
idiom that Boost.Fiber allowed, thus the existing db code grew to rely
on it. This also happens in the `libs/execution` code. Eventually, all
of these places should be removed, and then the
`monad_fiber_semaphore_thread_acquire_one` function should be removed.

#### Why are sleeping threads a problem?

If `monad_fiber_semaphore_acquire` finds there are no wakeup tokens
available, it goes to sleep until a token is released. To "sleep" means
to be added to a fiber wait queue, which is an intrusive list of
`monad_fiber_t` objects. Not only does an ordinary thread of execution
not have a `monad_fiber_t` object modeling it, but the wakeup behavior
is intimately tied to the scheduling model: to "wake up" means "call
`monad_run_queue_try_push`", an idiom that does not make sense for an
ordinary thread. An ordinary thread is scheduled by the operating system,
not by our fiber scheduler.

Note that this does not apply to an ordinary thread calling
`monad_fiber_semaphore_release`: that is a common idiom that makes sense.
A wakeup token typically represents an external event that has occurred.
It is perfectly normal for the "signaler" of that event to be an ordinary
thread. For example, a non-fiber I/O worker thread might signal that an
I/O event has occurred.

Thus, it is "normal" for ordinary threads to wake up fibers, but it is
unusual (and probably a design mistake) for ordinary threads to sleep on
(and be woken up by) synchronization primitives that were designed for
fibers.

#### When and how to use `monad_fiber_semaphore_thread_acquire_one`

To support the existing code, a limited form of threads sleeping on
semaphores is allowed. The semantics are:

- The thread is not tracked on a wait queue like the waiting fibers
  are, which may affect debuggability

- No matter when a thread starts sleeping, it is always woken up
  last: the wakeup is edge triggered by the wakeup token counter
  being CMPXCHG'd from 1 to 0 (this is the "one" in "acquire one")

- The acquiring thread does not actually sleep, but busy-waits in an
  atomic spin loop. This unusual design choice was made because the
  places where these waits happen can be performance sensitive

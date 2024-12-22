# The execution event recorder

## Preliminaries

You should have a rough idea of how the event system is designed before
reading this. The main introductory document is the `event.md` file in
the client library directory, `libs/event`. It explains the basic
concepts and data structures from the consumers perspective. This file
explains the specific objects `monad` uses to record the events, and the
rationale for their design.

### Ring and payload diagram

`event.md` contains an ASCII art picture that depicts the two main
shared memory objects, which is reproduced below. First, recall the
definition of an "event":

> Events are made up of two components:
>
> 1. The *event descriptor* is a fixed-size (currently 32 byte) object
>    describing an event that has happened. It contains the event's type,
>    a sequence number, and a timestamp.
> 2. The *event payload* is a variably-sized piece of extra data about
>    the event, which is specific to the event type. For example,
>    a "start of transaction" event contains the transaction header as its
>    payload. Some events have an empty payload, such as the heartbeat event.
>    Some of the fields in the event descriptor not already mentioned are
>    used to communicate where in shared memory the payload bytes are located,
>    and the payload's length.

This is shown as follows:

```
Event  .---------.---------.---------------.---------.---------.----
Ring   | Event 1 | Event 2 |     ...       | Event N | (empty) | ...
       .---------.---------.---------------.---------.---------.----
        |         |                         |
        |         |                         |
        |         |    .-----------------.  |   .-----------------.
        |         |    | Payload Page 1  |  |   | Payload Page 2  |
        |         |    .-----------------.  |   .-----------------.
        \---------.--> | Event 1 payload |  \-> | Event N payload |
                  |    .-----------------.      .-----------------.
                  \--> | Event 2 payload |      |       ...       |
                       | (note that this |
                       |  one is larger) |
                       .-----------------.
                       |       ...       |


Event ring, containing descriptors which point at variably-sized payloads
allocated on "payload pages"
```

In C code, the "Event 1", "Event 2", etc. objects are instances of
`struct monad_event_descriptor`. The payload pages are large slabs of
memory that hold payload contents. At the base address of a payload
page is a header object called `struct monad_event_payload_page`. Some
of its fields are read by the reader, but most of them are internal
linear allocator state used by the writer.

Both objects are defined in `event.h`, which is part of the
`monad_event_core` library, in `libs/event`.

In the code, the ring buffer array is called the _"descriptor table"_
because it has type `struct monad_event_descriptor[]`. The atomic
"next index" register is mapped in a shared memory page by itself,
called the control page. The objects are currently defined this way:

```c
/// Control register of the event ring, mapped in a shared memory page
struct monad_event_ring_control
{
    alignas(64) _Atomic(uint64_t) prod_next;
};

/// An IPC-style ring used to implement a lock-free MPMC queue for passing
/// event descriptors between threads, potentially in different processes.
/// This object is not directly present in shared memory, but the control page
/// and descriptor table are.
struct monad_event_ring
{
    struct monad_event_ring_control *control;
    struct monad_event_descriptor *descriptor_table;
    size_t capacity_mask;
    size_t capacity;
};
```

#### Important aside: what is `monad_event_core`?

Because the reader and writer both understand the shared memory objects,
their definition is _not_ here alongside the recorder, but in a separate
library that defines only those objects, called `monad_event_core`.

`monad_event_core` is a more "fundamental" library than `libmonad_core`:
`libmonad_core.a` links to `libmonad_event_core.a`, rather than the other
way around. Also, `monad_event_core` does not use any of our internal
CMake functions, such as `monad_compile_options`.

The rationale is that both the Rust build system and any third-party
trading system integrators are also meant to compile against
`libmonad_event_core.a`. Because it depends on nothing else in our
repository (and also on no third-party libraries), a third-party user
can just copy the `libs/event` directory into their source tree. The
isolation this provides has already proven useful in the Rust case: it
avoids any the hard-to-debug brittleness of the integration of the two
build systems, because `libmonad_event_core.a` is trivial to build by
itself.

The event recorder is in `monad_core` rather than `monad_execution`
because the event system can be reused by the performance tracer, and
performance trace points can be placed anywhere (e.g., in `libs/db`).
The performance tracer is described in a different document.

### "Why payload pages?": a comparison with network processing

The design inspiration comes from network drivers: a typical Ethernet
NIC reassembles packets within a FIFO bit buffer (to be DMA'ed upon
completion) and the arrival of a DMA packet is described by a small,
fixed-size packet descriptor, containing some metadata about the packet
and the DMA location where the packet contents were transferred to. The
communication of the device driver and the NIC hardware happens via a
shared memory SPSC descriptor queue.

#### Aside: why not large, fixed-sized events and no "payload page" scheme?

High performance user-space networking generally works with "packet"-oriented
memory pools, which hand out fixed-size packet buffers that are either
near-MTU sized or rounded up to 2048. Doing this isn't even that wasteful,
given that on average, half the buffer is full. As an example, in the HFT
world we were typically dealing with UDP multicast packets. A typical CME
exchange market data packet is between 300-1400 bytes, with the average about
squarely in the middle.

In the execution event case, the size distribution is more "power law"-like:
most events carry tiny payloads, but a few are much larger. The larger ones
are:

  - Outlier `TXN_LOG` events that log an unusually large `data` field
  - Outlier `TXN_START` events where there is a lot of transaction data
    (typically contract definitions)

The average event payload size is ~350 bytes, but the median is only 82
bytes. The largest items are dozens of kilobytes. I considered a scheme
where the event descriptors are larger: either 128 or 256 bytes and most
payloads can be stored "in line". There might be a reason to add this
optimization later, but because of the existence of rare large events,
we will need some kind of "off ring" storage.

This is because AFAIK we cannot get the elegant properties of the
"broadcast ring buffer" design without a fixed-size array where the
sequence number is related to the array index, and 1 sequence number == 1
event. The items in the fixed-size array can't possibly be as large as the
largest possible payload: it's not even clear what the upper-bound payload
would be, and the waste would be unacceptable.

### Multiple event rings

The performance tracer can reuse the event ring infrastructure. For this
reason, there are currently two different event rings: the "normal" ring
records execution events, and the performance ring records many more kinds
of events that are only interesting for performance research. Likely the
latter will be turned off in most settings, as it requires more resources
than normal validators would want to operate.

When importing an event ring, a client specifies which event ring they
want:

```c
/// Describes which event ring an event is recorded to; different categories
/// of events are recorded to different rings
enum monad_event_ring_type : uint8_t
{
    MONAD_EVENT_RING_EXEC,  ///< Core execution events
    MONAD_EVENT_RING_TRACE, ///< Performance tracing events
    MONAD_EVENT_RING_COUNT, ///< Number of recognized ring types
};
```

## Recording library fundamentals

### Where does recording happen?

The public interface of the recorder -- what you have to include to
actually record an event -- is in `event_recorder.h`. All the
performance sensitive functions are defined as inline functions in
`event_recorder_inline.h`, and all recording start in one of two
central inlined functions:

1. `monad_event_record` - records events whose payloads are in a single
   buffer (or that have empty payloads)

2. `monad_event_recordv` - provides "vectored gather I/O" (as in UNIX
   `writev(2)` or `sendmsg(2)`) to record events whose payload is split over
   several buffers described by a `struct iovec` array. This is common in
   execution, e.g., for a transaction log, the header information, topics,
   and data are not stored in one contiguous buffer, but are combined into
   one upon write

These functions are not usually called directly, but through the `MONAD_EVENT_`
family of macros, which writes to the "main" execution event ring,
`MONAD_EVENT_RING_EXEC`. The performance tracer ring is written to using
the (equivalent) `MONAD_TRACE_` family of macros, which are defined in a
different header.

A core requirement is that the recorder operate in under 100 nanoseconds
for events will modest payload sizes. To that end it has a few fancier
features:

- The record functions can be called by any number of `monad` threads
  simultaneously. The event descriptor allocation is always lock-and-wait
  free. The payload page allocation _usually_ does not lock (but see the
  next point)
- The record functions make use of a thread-local object to make their
  payload-page allocation strategy trivially thread-safe (they allocate
  from a cached thread-local payload page most of the time). On rare
  occasional locking does occur: a spinlock is taken (on the pool of
  payload pages) when a full page has to be swapped out for a free one

The general flow of recording is:

- Reserve a slot in the descriptor table to hold the next event
  with `_monad_event_alloc_ring_descriptor`. This gives back an
  "empty" slot in the descriptor table (pointing to an older event
  whose contents will be overwritten)
- Allocate space from the cached thread-local payload page, possibly
  swapping the page for fresh one if it is full
- Record all the details into the descriptor
- When finished, atomically write the sequence number with
  `memory_order_release` ordering, ensuring all other associated
  writes are visible. This is why the client must atomically acquire
  the sequence number after finishing its calculations using the
  zero-copy API -- to prove it did not see an event changing
  "mid-write"

### Important objects in the library

#### `struct monad_event_recorder`

This object owns most of the state for recording to an event ring. Because
there is more than one event ring, there is a global array of these:

```c
extern struct monad_event_recorder
    g_monad_event_recorders[MONAD_EVENT_RING_COUNT];
```

The recorder:

- Is the owner of the actual `monad_event_ring` for a given
  `monad_event_ring_type`.
- Owns the payload page memory pool that supplies its thread-local
  counterpart with fresh payload pages
- Uses an amount of memory that can be configured before it is enabled,
  but a reasonable default will be used otherwise
- Can be run-time disabled, in which case no events will be recorded to
  the associated ring (calls to a `MONAD_EVENT_` or `MONAD_TRACE_` macro
  will execute a single `if` statement, then exit)

#### `struct monad_event_thread_state`

A relevant code comment reads:

```c
// To make recording as fast as possible, some of the recorder state is cached
// in this thread-local object; namely, each thread has its own active payload
// page that it can allocate event payloads from without locking the page pool
struct monad_event_thread_state
{
    // ...
```

Despite the centrality of the recorder object, the main object that
`monad_event_record()` interacts with is this one, which caches various
attributes for the recording thread.

#### `struct monad_event_recorder_shared_state`

A few bits of internal machinery are shared by all recorders. These
are mostly related to the thread and block header metadata tables,
which are described in `event.md`, and the proper cleanup of the
thread-local objects.

## `monad_event_server`

As in the client library, there is a clean separation between code
that works with the shared memory objects, and the IPC code which
exports the associated shared memory segments to other processes.

`event_server.c` is a simple "library-like" component that allows
its user to act an exporter of event rings that are owned by a
`monad_event_recorder`. A UNIX domain socket is used to transfer
`memfd_create(2)` file descriptors into other processes. However,
most of the server code is not aware of the recorder details or even
the objects that store the shared memory layout: `event_server.c` does
not even include `event_recorder.h`.

This is a deliberate choice, to allow `event_server.c` to be reused
to create an in-process "fake" event server, for use in test cases that
export known static shared memory segments using the same protocol as
the real `monad` process does. The scheme works as follows:

- `event_server.c` handles the ceremony of "being a server": managing
  client objects, running the event loop, doing I/O, etc
- `event_server_internal.h` defines a generic interface for exporting
  shared memory segments using the export protocol defined in
  `event_protocol.h` (from `libs/event`)
- `event_server_export.c` implements the export interface for recorder
   rings
- `event_server_test.c` (which is part of the `libs/event`) implements
  the export interface to export shared memory segments from a static,
  on-disk file format. This is mostly used by Rust, so that it doesn't
  require an external process to act as the server
- `cmd/exportshm.cpp` is a utility that generates the shared memory
  snapshots used by `event_server_test.c`

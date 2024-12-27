# The execution event recorder

## Preliminaries

You should have a rough idea of how the event system is designed before
reading this. The introductory document is the `event.md` file in the
client library directory, `libs/event`. It explains the basic concepts
and data structures from the consumers perspective.

The file you are reading now explains the specific objects `monad` uses
to record the events, and the rationale for their design.

### Ring and payload diagram

`event.md` contains a UTF-8 diagram that depicts the two main shared
memory objects, which is reproduced below. First, recall the definition
of an "event":

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
  ╔═Event ring══════════════════════════...═════════════════════════╗
  ║ ┌─────────┐ ┌─────────┐ ┌─────────┐     ┌─────────┐ ┌─────────┐ ║
  ║ │         │ │         │ │         │     │         │ │░░░░░░░░░│ ║
  ║ │ Event 1 │ │ Event 2 │ │ Event 3 │     │ Event N │ │░ empty ░│ ║
  ║ │         │ │         │ │         │     │         │ │░░░░░░░░░│ ║
  ║ └────┬────┘ └────┬────┘ └─────────┘     └────┬────┘ └─────────┘ ║
  ╚══════╬═══════════╬══════════════════...══════╬══════════════════╝
         │           │                           │
         │           │                           │
         │           │                           │
         │           │                           │
         │           │    ┌─Payload Page──┐      │   ┌─Payload page──┐
         │           │    │┌─────────────┐│      │   │┌─────────────┐│
         │           │    ││ Page header ││      │   ││ Page header ││
         │           │    │├─────────────┤│      │   │├─────────────┤│
         │           │    ││   Event 1   ││      │   ││             ││
         └───────────┼────▶│   payload   ││      │   ││   Event N   ││
                     │    │├─────────────┤│      └───▶│   payload   ││
                     │    ││             ││          ││             ││
                     │    ││             ││          │├─────────────┤│
                     │    ││   Event 2   ││          ││░░░░░░░░░░░░░││
                     └────▶│   payload   ││          ││░░░░░░░░░░░░░││
                          ││             ││          ││░░░░░░░░░░░░░││
                          ││             ││          ││░░░░free░░░░░││
                          │├─────────────┤│          ││░░░░space░░░░││
                          ││░░░░░░░░░░░░░││          ││░░░░░░░░░░░░░││
                          ││░░░░free░░░░░││          ││░░░░░░░░░░░░░││
                          ││░░░░space░░░░││          ││░░░░░░░░░░░░░││
                          ││░░░░░░░░░░░░░││          ││░░░░░░░░░░░░░││
                          │└─────────────┘│          │└─────────────┘│
                          └───────────────┘          └───────────────┘
```

In C code, the "Event 1", "Event 2", etc. objects are instances of
`struct monad_event_descriptor`. The payload pages are large slabs of
memory that hold payload contents. At the base address of a payload
page is a header object called `struct monad_event_payload_page`. Some
of its fields are read by the reader, but most of them are internal
linear allocator state used by the writer.

The design inspiration comes from network drivers: a typical Ethernet
NIC reassembles packets within a FIFO bit buffer (to be DMA'ed upon
completion) and the arrival of a DMA packet is described by a small,
fixed-size packet descriptor, containing some metadata about the packet
and the DMA location where the packet contents were transferred to. The
communication of the device driver and the NIC hardware happens via a
shared memory SPSC descriptor queue.

`struct monad_event_descriptor` and `struct monad_event_payload_page`
are defined in `event.h`, which is part of the `monad_event_core`
library, in `libs/event`.

The ring buffer array has type `struct monad_event_descriptor[]` and is
called the _"descriptor table"_. The atomic "next index" register is
mapped in a shared memory page by itself, called the control page. These
objects are currently defined this way:

```c
/// Control register of the event ring, mapped in a shared memory page
struct monad_event_ring_control
{
    alignas(64) _Atomic(uint64_t) prod_next;
};

/// An IPC-style ring used to implement a lock-free MPMC ring for passing event
/// descriptors between threads, potentially in different processes. This
/// object is not directly present in shared memory, but the control page and
/// descriptor table are.
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
The performance tracer is described in a separate document.

### Why not large, fixed-sized events and no "payload page" scheme?

One might imagine a design like this could work:

```c
struct monad_event
{
    struct monad_event_header header;
    uint8_t payload[MAX_PAYLOAD_SIZE];
};
```

Unfortunately there is no obvious choice for `MAX_PAYLOAD_SIZE`, because of
the event size distribution. The distribution appears to follow a power law:
the vast majority of events carry tiny payloads, but a few are _much_
larger. The larger ones are:

  - Outlier `TXN_LOG` events that log an unusually large `data` field
  - Outlier `TXN_START` events where there is a lot of transaction data
    (typically but not always contract definitions)

The average event payload size is ~350 bytes, but the median is only 82
bytes. The largest items are dozens or even hundreds of kilobytes. The
following histogram shows the distribution of 7 million events (resulting
from 4000 blocks replayed from historical Ethereum block 15,000,000).

The X axis (the histogram bins) are event size bins, in powers of 2. For
example, the bin labeled `128/256` contains events whose sizes are in the
range `[128, 256)`. The Y axis shows the percentage of events in each
bin. Because of the power-law nature of the data, the Y axis must be
log10 scaled to be able to visualize the height of large event size bins.

```
                               Histogram of event payload sizes
   % of events               4000 blocks at 15m, 7 million events
  (log10 scale)
            ┌──┐
            │██│  ┌──┐  ┌──┐
            │██│  │██│  │██│
         15%│██│  │██│  │██│
            │██│  │██│  │██│
            │██│  │██│  │██│  ┌──┐
            │██│  │██│  │██│  │██│
            │██│  │██│  │██│  │██│
        1.5%│██│  │██│  │██│  │██│  ┌──┐
            │██│  │██│  │██│  │██│  │██│
            │██│  │██│  │██│  │██│  │██│  ┌──┐
            │██│  │██│  │██│  │██│  │██│  │██│
            │██│  │██│  │██│  │██│  │██│  │██│
            │██│  │██│  │██│  │██│  │██│  │██│
        0.1%│██│  │██│  │██│  │██│  │██│  │██│  ┌──┐
            │██│  │██│  │██│  │██│  │██│  │██│  │██│
            │██│  │██│  │██│  │██│  │██│  │██│  │██│
            │██│  │██│  │██│  │██│  │██│  │██│  │██│  ┌──┐
            │██│  │██│  │██│  │██│  │██│  │██│  │██│  │██│
            │██│  │██│  │██│  │██│  │██│  │██│  │██│  │██│
       0.01%│██│  │██│  │██│  │██│  │██│  │██│  │██│  │██│  ┌──┐  ┌──┐
            │██│  │██│  │██│  │██│  │██│  │██│  │██│  │██│  │██│  │██│        ┌──┐
            │██│  │██│  │██│  │██│  │██│  │██│  │██│  │██│  │██│  │██│        │██│
            │██│  │██│  │██│  │██│  │██│  │██│  │██│  │██│  │██│  │██│  ┌──┐  │██│
            │██│  │██│  │██│  │██│  │██│  │██│  │██│  │██│  │██│  │██│  │██│  │██│
            └──┘  └──┘  └──┘  └──┘  └──┘  └──┘  └──┘  └──┘  └──┘  └──┘  └──┘  └──┘
             0    64    128   256   512   1KiB  2KiB  4KiB  8KiB  16KiB 32KiB 64KiB
             63   127   255   511   1023  2KiB  4KiB  8KiB  16KiB 32KiB 64KiB 128KiB

                                    Size (log2 bin sizes)
```

The percentages do not appear to sum to 100% because of the quantization
of the log10 scale when turning the real image into UTF-8 art. In terms of
raw numbers, the first few bins each contain a few million events. The last
few bins contain between a few hundred and a few thousand events. Because of
the existence of rare large events, there isn't a clear choice for a fixed
size buffer, and we need a more sophisticated scheme.

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
`event_recorder_inline.h`. Recording an event starts in one of two
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
- Initialize all the fields of the descriptor
- When finished, atomically write the sequence number with
  `memory_order_release` ordering, ensuring all other associated
  writes are visible. This is why the client must atomically acquire
  the sequence number after finishing its calculations using the
  zero-copy API -- to prove it did not see an event changing
  "mid-write"

## Important objects in the recorder library

### Diagram of recorder objects

This diagram shows how all the fundamental objects are related to each
other. All arrows represent C pointers, so it illustrates how objects
are actually arranged in memory. Because there are a lot of relationships,
you will likely need to read the description of each object in subsequent
sections to understand it completely.

```
                                                          ┌────────▶┌─Free page 1 (◎)───────────────┐
  ┌─Recorder (◆)──────────────────────────────────┐       │         │                               │
  │                                               │       │         │┌─Payload page header─────────┐│
  │ ■   monad_event_descriptor descriptor_table[] │       │         ││ uint8_t *heap_begin         ││
  │ │ ■ monad_event_payload_page *all_pages[]     │       │         ││ uint8_t *heap_next          ││
  │ │ │                                           │       │         ││ uint8_t *heap_end           ││
  │ │ │ ┌─Payload page pool────────────────────┐  │       │         ││ TAILQ_ENTRY(...) next ■─────┼┼────────┐
  │ │ │ │                                      │  │       │         │├─────────────────────────────┤│        │
  │ │ │ │ ■ TAILQ_HEAD(...) active_pages       │  │       │         ││▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓││        │
  │ │ │ │ │                                    │  │       │         ││▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓││        │
  │ │ │ │ │ TAILQ_HEAD(...) free_pages ■───────┼──┼───────┘         ││▓▓ Old events, alive until ▓▓││        │
  │ │ │ └─┼────────────────────────────────────┘  │                 ││▓▓▓ this page is recycled ▓▓▓││        │
  │ │ │   │                                       │                 ││▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓││        │
  └─┼─┼───┼───────────────────────────────────────┘                 ││▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓││        │
    │ │   │                                                         │└─────────────────────────────┘│        │
    │ │   │                                                         └───────────────────────────────┘        │
    │ │   │                                                                                                  │
    │ │   │    ╔═Event descriptor ring═══════════════...══════════════╗    ┌─Free page 2 (◎)────────────┐◀───┘
    │ │   │    ║ ┌─────────┐ ┌─────────┐ ┌─────────┐      ┌─────────┐ ║    │┌──────────────────────────┐│
    │ │   │    ║ │         │ │         │ │         │      │         │ ║    ││  details not shown, but  ││
    └─┼───┼───▶║ │ Event 1 │ │ Event 2 │ │ Event 3 │      │ Event N │ ║    ││ same as other free page  ││
      │   │    ║ │         │ │         │ │         │      │         │ ║    │└──────────────────────────┘│
      │   │    ║ └─────────┘ └─────────┘ └─────────┘      └─────────┘ ║    └────────────────────────────┘
      │   │    ╚═════════════════════════════════════...══════════════╝
      │   │
      │   │
      │   │   ┌─Recorder thread cache - thread 1 (◊)────┐           ┌─Recorder thread cache - thread 2 (◊)────┐
      │   │   │                                         │           │                                         │
      │   │   │ ■ monad_event_payload_page *active_page │         ┌─┼─■ monad_event_payload_page *active_page │
      │   │   │ │                                       │         │ │                                         │
      │   │   └─┼───────────────────────────────────────┘         │ └─────────────────────────────────────────┘
      │   │     │                                                 │
      │   │     │                                                 │
      │   │     │                                                 │
      │   └─────┴─▶───────────▶┌─Active page, thread 1 (◎)─────┐  └────▶┌─Active page, thread 2 (◎)───┐
      │                        │                               │  ┌────▶│┌──────────────────────────┐ │
      │                        │┌─Payload page header─────────┐│  │     ││  details not shown, but  │ │
      │               ┌────────┼┼■    uint8_t *heap_begin     ││  │     ││same as other active page │ │
      │               │  ┌─────┼┼──■  uint8_t *heap_next      ││  │     │└──────────────────────────┘ │
      │               │  │  ┌──┼┼────■uint8_t *heap_end       ││  │     └─────────────────────────────┘
      │               │  │  │  ││     TAILQ_ENTRY(...) next ■─┼┼──┘
      │               │  │  │  │├─────────────────────────────┤│
      │               └──┼──┼──┼▶▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓││
      │                  │  │  ││▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓││
      │                  │  │  ││▓▓▓ Newly recorded events ▓▓▓││
      │                  │  │  ││▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓││
      │                  │  │  ││▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓││
      │                  │  │  │├─────────────────────────────┤│
      │                  └──┼──┼▶░░░░░░░░░░░░░░░░░░░░░░░░░░░░░││    ┌─Legend───────────────────────────────┐
      │                     │  ││░░░░░░░░░░░░░░░░░░░░░░░░░░░░░││    │                                      │
      │                     │  ││░░░░░░░░░░░ empty ░░░░░░░░░░░││    │ ◆ - struct monad_event_recorder      │
      │                     │  ││░░░░░░░░░░░░░░░░░░░░░░░░░░░░░││    │ ◊ - struct monad_event_recorder_thr  │
      │                     │  ││░░░░░░░░░░░░░░░░░░░░░░░░░░░░░││    │ ◎ - struct monad_event_payload_page  │
      │                     └──┼▶─────────────────────────────┘│    └──────────────────────────────────────┘
      │                        └───────────────────────────────┘
      │
    ╔═▼═════════════════════════════...════════════╗
    ║ ┌───────┐ ┌───────┐ ┌───────┐      ┌───────┐ ║
    ║ │page * │ │page * │ │page * │      │page * │ ║
    ║ └───────┘ └───────┘ └───────┘      └───────┘ ║
    ╚═Payload page array════════════...════════════╝
```

### `struct monad_event_recorder`

This object owns most of the state for recording to an event ring. Because
there is more than one event ring, there is a global array of recorders:

```c
extern struct monad_event_recorder
    g_monad_event_recorders[MONAD_EVENT_RING_COUNT];
```

The recorder:

- Is the owner of the actual `monad_event_ring` for a given
  `monad_event_ring_type`.
- Owns the payload page memory pool; this supplies the payload pages
  the store the event payloads in a given ring
- Uses an amount of memory that can be configured before it is enabled,
  but a reasonable default will be used otherwise
- Can be run-time disabled, in which case no events will be recorded to
  the associated ring (the `MONAD_EVENT_` or `MONAD_TRACE_` macros
  will execute a single `if` statement, then exit)

### `monad_event_payload_page` and `monad_event_payload_page_pool`

All event payloads are allocated from a payload page, which is a large
contiguous slab of shared memory (currently 16 MiB by default) with this
header object placed at offset zero:

```c
struct monad_event_payload_page
{
    // Cache line read by readers, modified by writers
    alignas(64) _Atomic(uint64_t) overwrite_seqno;
    // Cache line *only* used by writer (except for the exportshm utility). The
    // pointers here point into the writer's address space
    alignas(64) uint8_t *page_base;
    uint8_t *heap_begin;
    uint8_t *heap_next;
    uint8_t *heap_end;
    uint64_t event_count;
    uint64_t alloc_count;
    TAILQ_ENTRY(monad_event_payload_page) page_link;
    // Cache line holding lifetime-constant values
    alignas(64) struct monad_event_payload_page_pool *page_pool;
    int memfd;
    uint16_t page_id;
    char page_name[26];
};
```

The payload allocation strategy is simple: all memory on the page that is
not used by this header is described as the region between `heap_begin`
and `heap_end`, and allocation just increments `heap_next` until it reaches
`heap_end`. When `heap_next + next_allocation_size > heap_end`, the page is
considered full, and is swapped out for a new one.

The lifecycle of a page is as follows:

- The payload page pool (owned by the recorder) creates a fixed number
  of payload page objects when it is first configured (when
  `monad_event_recorder_configure` is called)
- This fixed number of pages is _permanent_, unless the recorder is
  disabled and then reconfigured: no new payload pages are `mmap`'ed
  into our address space while a recorder is running
- At any given time, each payload page is placed on one of two lists:
  the list of "active" pages and the list of "free" pages
- Active pages are those that are currently being used for recording.
  "Free" pages are pages that are full, and are waiting to be recycled
  in the future. Until they are recycled, it is safe to read old payload
  data from them
- There is one active page per ring, per thread. When an event occurs,
  its payload buffer is allocated by bumping the `heap_next` of the
  active page. If the page fills up, that page is "deactivated": removed
  from the active list and is placed at the _end_ of the free list. The
  oldest free page is then made active

The comment in the deactivation function explains the rationale:

```c
static void deactivate_payload_page(
    struct monad_event_payload_page_pool *page_pool,
    struct monad_event_payload_page *page)
{
    MONAD_DEBUG_ASSERT(monad_spinlock_is_self_owned(&page_pool->lock));

    // Deactivate the given page by placing it at the end of the free list.
    // The FIFO nature of the free list is critical to how our shared memory
    // strategy works. Note that it is still safe for the event consumer to
    // read from payload pages while they sit on the free list, and it will
    // remain safe until the page is recycled, once it reaches the head of the
    // free list. After it is recycled, the page will be marked as not safe to
    // read by recording in the header the sequence number when it was recycled.
    TAILQ_REMOVE(&page_pool->active_pages, page, page_link);
    TAILQ_INSERT_TAIL(&page_pool->free_pages, page, page_link);
    --page_pool->active_page_count;
    ++page_pool->free_page_count;
}
```

### `struct monad_event_recorder_thr`

A relevant code comment reads:

```c
// To make recording as fast as possible, some of the recorder state is cached
// in this thread-local object; namely, each thread has its own active payload
// page that it can allocate event payloads from without locking the page pool
struct monad_event_recorder_thr {
    // ...
```

Despite the centrality of the recorder object, the main object that
`monad_event_record()` interacts with is this one, which caches various
attributes for the recording thread. Among other things, this objects
stores the active payload page for each enabled event ring, for each
thread.

### `struct monad_event_recorder_shared_state`

A few bits of internal machinery are shared by all recorders. These
are mostly related to the thread and block header metadata tables,
which are described in `event.md`, and the proper cleanup of the
thread-local objects. It is not shown in the diagram.

## Exporting shared memory: `monad_event_server`

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

This choice makes things a bit more complex, but allows `event_server.c`
to be reused to create an in-process "fake" event server, for use in
test cases that export known static shared memory segments using the
same protocol as the real `monad` process does. The scheme works as
follows:

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

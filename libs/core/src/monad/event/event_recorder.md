# The execution event recorder

## Preliminaries

You should have a rough idea of how the event system works before reading
this. The introductory document is the `event.md` file in the client library
directory, `libs/event`. It explains the basic concepts and data structures
from the reader's perspective.

The file you are reading now explains the specific objects `monad` uses
to record the events, and the rationale for their design.

### Simple ring and payload diagram

`event.md` contains a UTF-8 diagram that depicts the two main shared
memory objects, which is reproduced below. First, recall the definition
of an "event":

> Events are made up of two components:
>
> 1. The *event descriptor* is a fixed-size (currently 64 byte) object
>   describing an event that has happened. It contains the event's type,
>   a sequence number, and a timestamp.
> 2. The *event payload* is a variably-sized piece of extra data about
>   the event, which is specific to the event type. For example,
>   a "start of transaction" event contains the transaction header as its
>   payload. Some events have an empty payload, such as the heartbeat event.
>   Some of the fields in the event descriptor not already mentioned are
>   used to communicate where in shared memory the payload bytes are located,
>   and the payload's length.

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
         │           └──────┐                    └────┐
         │                  │                         │
   ╔═════▼══════════════════▼══════════════...════════▼════════════════════════╗
   ║ ┌───────┐ ┌─────────────────────────┐     ┌─────────────┐ ┌─────────────┐ ║
   ║ │Event 1│ │         Event 2         │     │   Event N   │ │░░░░free░░░░░│ ║
   ║ │payload│ │         payload         │     │   payload   │ │░░░░space░░░░│ ║
   ║ └───────┘ └─────────────────────────┘     └─────────────┘ └─────────────┘ ║
   ╚═Payload buffer════════════════════════...═════════════════════════════════╝
```

In C code, the "Event 1", "Event 2", etc. objects are instances of
`struct monad_event_descriptor`. The payload buffer is a large byte
array.

The design inspiration comes from network drivers: a typical Ethernet
NIC reassembles packets within a FIFO bit buffer (to be DMA'ed upon
completion) and the arrival of a DMA packet is described by a small,
fixed-size packet descriptor, containing some metadata about the packet
and the DMA location where the packet contents were transferred to. The
communication of the device driver and the NIC hardware happens via a
shared memory SPSC descriptor queue.

The above structure is represented in code as `struct monad_event_ring`,
defined in `event.h` (which is part of the `libmonad_event` library,
in `libs/event`). It is defined this way:

```c
/// Describes a shared memory event ring that has been mapped into the address
/// space of the current process
struct monad_event_ring
{
    struct monad_event_descriptor *descriptors; ///< Event descriptor ring array
    uint8_t *payload_buf;                       ///< Payload buffer base address
    struct monad_event_ring_control *control;   ///< Tracks ring's state/status
    size_t capacity;                            ///< Size of descriptors array
    size_t payload_buf_size;                    ///< Bytes in payload_buf
    void *ring_db_map_base;                     ///< API convenience (see impl)
};
```

The "control" object stores the ring's writer state: it keeps track of the
last sequence number allocated, the next payload buffer byte to allocate,
and a few other parameters. This state is sometimes examined by the reader,
e.g., to find the most recently produced event when initializing a new
iterator, or to check if the event ring is enabled.

The "buffer window" field is used to detect when event payloads have
been overwritten by subsequent events. It is described in detail in
the "Sliding Buffer Window" section of this document.

The `ring_db_map_base` field is used to make the API less error-prone,
and is described in a source code comment in the `libmonad_event` source
code.

#### Aside: `libmonad_event` vs. `libmonad_core`

Because the reader and writer both understand the shared memory objects,
their definition is _not_ here alongside the recorder, but in a separate
library that defines only those objects, called `libmonad_event`.
`libmonad_event` is a more "fundamental" library than `libmonad_core`:
`libmonad_core.a` links to `libmonad_event.a`, rather than the other
way around. Also, `libmonad_event` does not use any of our internal
CMake functions, such as `monad_compile_options`.

The rationale is that both the Rust build system and any third-party
trading system integrators are also meant to compile against
`libmonad_event.a`. Because it depends on nothing else in our repository
(and also on no third-party libraries), a third-party user can just copy
the `libs/event` directory into their source tree.

The writer is a different story: it is only designed to record execution
events, and is not meant to be extracted from the `monad` source tree.
The event recorder is in `monad_core` rather than `monad_execution`
because the event system can be reused by the performance tracer, and
performance trace points can be placed anywhere (e.g., in `libs/db`). The
performance tracer is described in a separate document.

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
   a single event payload upon write

These functions are not usually called directly. In C, they are called
using the `MONAD_EVENT_` family of macros. In C++, the inline functions
`monad::record_event_expr` and `monad::record_event_iov` provides a more
idiomatic C++ interface.

The record functions can be called by any number of `monad` threads
simultaneously. Both event descriptor allocation and payload allocation
are always lock-and-wait free.

The general flow of recording is:

1. **Reserve resources** - reserve all resources needed to record the
  event by calling `_monad_event_ring_reserve`. This allocates a slot in
  the descriptor array to hold the descriptor, a sequence number for the
  event, and space in the payload buffer to hold the payload
2. **Initialize descriptor** - initialize all the fields of the event
  descriptor object, _except_ for the sequence number field. The sequence
  number for this event was reserved in step 1, but it is not written into
  the descriptor until the final step
3. **Copy payload** - `memcpy(3)` the payload into the space allocated by
  `_monad_event_ring_reserve`
4. **Store sequence number** - atomically store the sequence number into
   the `seqno` field of the event descriptor, with `memory_order_release`
   ordering

As described in `event.md`, the atomic updates to the sequence number
field are how the writer communicates to the reader that the event is
ready. The compiler and CPU memory barriers emitted by the atomic stores
ensure that all the memory operations related to event recording become
visible in other threads by the time the sequence number changes.

There are actually two changes to the descriptor's sequence number field.
The first happens in step 1, the "Reserve resources" step. Immediately
after a descriptor slot is reserved for the event, the `seqno` field of the
descriptor is set to zero with `memory_order_release` ordering. Zero is
not a valid sequence number, so readers can detect that this descriptor
slot is no longer valid. Because this slot belonged to an earlier event,
it's possible that a reader is still working with it. Zeroing the sequence
number indicates that the slot is in the process of being overwritten.
The second write to the `seqno` field announces that the write is complete. 

## Important objects in the recorder library

### Diagram of recorder objects

This diagram shows how all the important objects in the event recorder are
related to each other. The arrows either represent C pointers, or how an
array index field points to the indicated item in the associated array.
Thus, this diagram illustrates how objects are actually arranged in memory.

Objects surrounded by a double-line border (`═`) are resident in a shared
memory segment. Objects with a single-line border are resident only in the
address space of the recording process.

The diagram shows the state of memory immediately after recording
"Event 2":

```
  ┌─Recorder (◆)─────────────────────────────┐        ┌─Shared recorder state (◎)───────────┐
  │                                          │        │                                     │
  │ ■   monad_event_descriptor descriptors[] │        │ monad_event_ring_db_data *db_data ■ │
  │ │ ■ uint8_t *payload_buf                 │        └───────────────────────────────────┼─┘
  │ │ │ monad_event_ring_db_entry *entry ■───┼────────────┐                               ▼
  └─┼─┼──────────────────────────────────────┘            │       ╔═Ring database (▼)════════════════════════════╗
    │ │                                                   │       ║                                              ║
    │ │                                                   │   ┌───╬─■ monad_event_ring_db_entry rings[]          ║
    │ │                                                   │   │   ║   monad_event_thread_info threads[] ■────────╬──┐
    │ │                                                   │   │   ║   monad_event_block_header block_headers[] ■ ║  │
    │ │       ╔═Ring control (◮)════════════════╗         │   │   ╚════════════════════════════════════════════╬═╝  │
    │ │       ║                                 ║         │   │                                                │    │
    │ │       ║ ■ uint64_t last_seqno           ║         │   │                                                │    │
    │ │       ║ │ uint64_t next_payload_byte ■──╬───────┐ └──▶└──▶╔═Ring database entry (◺)═════════════╗      │    │
    │ │       ║ │ uint64_t buffer_window_start  ║       │         ║                                     ║      │    │
    │ │       ╚═╬═══════════════════════════════╝◀──────┼─────────╬─■ monad_event_ring_control *control ║      │    │
    │ │         └─────────┐                             │         ║   int ring_data_fd (◘)              ║      │    │
    │ │                   │                             │         ╚═════════════════════════════════════╝      │    │
    │ │    ╔══════════════╬══════════════════════...═╗  │                                                      │    │
    │ │    ║ ┌─────────┐ ┌▼────────┐ ┌─────────┐     ║  │                                                      │    │
    │ │    ║ │         │ │░░░░░░░░░│ │         │     ║  │                                                      │    │
    └─┼───▶║ │ Event 1 │ │░Event 2░│ │ (free)  │     ║  │           ╔═Thread metadata table══╗◀────────────────┼────┘
      │    ║ │         │ │░░░░░░░░░│ │         │     ║  │           ║ ┌────────────────────┐ ║                 │
      │    ║ └─────────┘ └─────────┘ └─────────┘     ║  │           ║ │ Thread 1 metadata  │ ║                 │
      │    ╚═Event descriptor ring═══════════════...═╝  │           ║ └────────────────────┘ ║                 │
      │                 ╱           ╲                   │           ║ ┌────────────────────┐ ║                 │
      │                ╱             ╲                  │    ┌──────╬─▶ Thread 2 metadata  │ ║                 │
      │               ╱               ╲                 │    │      ║ └────────────────────┘ ║                 │
      │              ╱                 ╲                │    │      ║ ┌────────────────────┐ ║                 │
      │             ╱                   ╲               │    │      ║ │        ...         │ ║                 │
      │            ╱                     ╲              │    │      ║ └────────────────────┘ ║                 │
      │           ╱                       ╲             │    │      ╚════════════════════════╝                 │
      │         ╔═Event descriptor (◊)══════════╗       │    │                                                 │
      │         ║                               ║       │    │                                                 │
      │         ║ ■ uint64_t payload_buf_offset ║       │    │      ╔═Block metadata table═══╗◀────────────────┘
      │         ║ │ uint8_t source_id ■─────────╬───────┼────┘      ║ ┌────────────────────┐ ║
      │         ║ │ uint16_t block_flow_id ■────╬───────┼───────────╬─▶  Block 1 metadata  │ ║
      │         ╚═╬═════════════════════════════╝       │           ║ └────────────────────┘ ║
      │           │                                     │           ║ ┌────────────────────┐ ║
      │           │                                     │           ║ │  Block 2 metadata  │ ║
      │           │                                     │           ║ └────────────────────┘ ║
      │           │                                     │           ║ ┌────────────────────┐ ║
      │           │                                     │           ║ │        ...         │ ║
      │           │                                     │           ║ └────────────────────┘ ║
      │           │                                     │           ╚════════════════════════╝
      ▼           │                                     │
      ╔═══════════╬═════════════════════════════════════╬═════════════════════════╗
      ║ ┌───────┐ ▼───────────────────────────────────┐ ▼───────────────────────┐ ║
      ║ │Event 1│ │              Event 2              │ │░░░░░░░░░free░░░░░░░░░░│ ║
      ║ │payload│ │              payload              │ │░░░░░░░░░space░░░░░░░░░│ ║
      ║ └───────┘ └───────────────────────────────────┘ └───────────────────────┘ ║
      ╚═Payload buffer════════════════════════════════════════════════════════════╝


     ┌─Legend─────────────────────────────────────────┐
     │                                                │
     │ ◆ - struct monad_event_recorder                │
     │ ◎ - struct monad_event_recorder_shared_state   │
     │ ▼ - struct monad_event_ring_db_data            │
     │ ◺ - struct monad_event_ring_db_entry           │
     │ ◊ - struct monad_event_descriptor              │
     │ ◮ - struct monad_event_ring_control            │
     │ ◘ - memfd_create(2) file descriptor containing │
     │     the descriptor ring and payload buffer     │
     └────────────────────────────────────────────────┘
```

The diagram contains some minor inaccuracies to make the basic ideas easy
to display visually, but which are technically wrong. There are two such
simplifications:

#### Simplification #1: sequence number indexing

The last sequence number does not point *directly* to the array slot of
the last produced event. This is because the array indices start a 0, but
sequence numbers start at 1. In the code that deals with mapping sequence
numbers to array slots, you will see a +1/-1 factor being applied.

#### Simplification #2: collapsed view of structures

In the diagram, some structure fields are shown as being part of a
parent structure instead of the structure they are really declared in,
to avoid cluttering the diagram with too many small objects.

For example, the C structure that holds a memory-mapped event ring is
`struct monad_event_ring`, yet this critically important structure is not
shown in the diagram. That is because it is a sub-object of the larger
`struct monad_event_recorder`; its important fields such as `descriptors`
and `payload_buf` are shown as being inside the `struct monad_event_recorder`
box.

### Most important object: `struct monad_event_recorder`

This object owns most of the state for recording to an event ring. Because
there is more than one event ring, there is a global array of recorders:

```c
extern struct monad_event_recorder
    g_monad_event_recorders[MONAD_EVENT_RING_COUNT];
```

An event recorder:

- Is the owner of the ring's shared memory resources for a given
  `monad_event_ring_type`
- Uses an amount of memory that can be configured before it is enabled
- Can be disabled at runtime, in which case no events will be recorded to
  the associated ring (the `MONAD_EVENT_` or `MONAD_TRACE_` macros
  will execute a single `if` statement, then exit)

Note that the definition of the event recorder is quite small:

```c
struct monad_event_recorder
{
    struct monad_event_ring_db_entry *db_entry;
    struct monad_event_ring event_ring;
    alignas(64) pthread_mutex_t config_mtx;
};
```

Most the state for an event recorder is actually stored in the
associated event ring's "ring db" entry. This is because that state needs
to live in shared memory and be examined other processes. For example, even
though the recorder owns the `memfd_create(2)` file descriptor for its event
ring, other processes must discover this file descriptor in shared memory and
open it themselves, to `mmap(2)` it into place (see the implementation of the
`monad_event_ring_db_import` function).

We say the recorder "owns" its resources to mean that recorder functions are
solely responsible for allocating and freeing them; be aware that they are
mostly resident in ring db shared memory and not in the structure itself.

### `struct monad_event_recorder_shared_state`

This singleton structure stores the bits of internal machinery shared by all
recorders. The main important object here is the event ring database, which
holds the metadata, enablement state, file descriptors, and control structure
for all event rings. This object also manages the end-of-process graceful
cleanup of all resources in the event system.

## Sliding buffer window

Both the event descriptor array and payload buffer are *ring buffers*:
once all array slots have been used, subsequent writes wrap around to the
beginning of the array. For event descriptors, the detection mechanism for
slow consumers observing an overwrite relies on the sequence number, as
described in the `event.md` documentation. For the payload buffer, a
similar idea is used, except using the byte offset in the payload buffer
(similar to the byte sequence number in the TCP protocol).

Conceptually, we think of a ring buffer as storing an infinite number
of items, but there is only enough space to keep the most recent items.
As with event sequence numbers, byte offsets within the payload buffer
increase monotonically forever: payload offsets are stored in event
descriptors _before_ modular arithmetic is applied. For example, given
a payload buffer of total size `S`, an event payload might be recorded
as starting at "offset" `4 * S + 100`. This is a virtual offset that
assumes an infinite-sized payload buffer; it corresponds to physical
offset `payload_buf[100]`. When reading or writing payload memory, the
library performs the virtual to physical calculation via modular
arithmetic.

Once the buffer is initially filled, we can think of the
`uint8_t payload_buf[]` array of size `S` as a sliding window across
the infinitely-sized virtual payload buffer: at any given time, the
most recent `S` bytes are still valid, whereas earlier offsets in
the `░` region are no longer valid.

```
   ...───────────────────────────────────────────────────────────────...
                                    S
                         ◀──────────────────────▶
       ┌────────────────┬────────────────────────┬─────────────────┐
       │░░░░░░░░░░░░░░░░│▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓│.................│
       │░░░░░░░░░░░░░░░░│▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓│.................│
       │░░░░░░░░░░░░░░░░│▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓│.................│
       └────────────────┴────────────────────────┴─────────────────┘

   ...──Virtual payload buffer (of infinite size)────────────────────...


  ┌─Legend────────────────────────────────────────────────┐
  │                                                       │
  │ ░ older payloads, overwritten in payload buffer       │
  │ ▓ currently active payloads, stored in payload buffer │
  │ . future payloads, not recorded yet                   │
  │                                                       │
  └───────────────────────────────────────────────────────┘
```

The code refers to this concept as the "buffer window": the sliding
window of virtual offsets that have not expired. Conceptually, this is
a window the same size as payload buffer, given by
`[buffer_window_start, buffer_window_start + S)`. Once more than `S`
bytes have been allocated, `buffer_window_start` slides forward,
and any event whose virtual offset is less than `buffer_window_start`
is known to be expired. `buffer_window_start` is stored in the ring
control structure, which is mapped in a shared memory segment and
shared with the reader. This is how the reader detects if an event
payload has expired.

Although this is the _concept_ of the algorithm, the recorder applies a
small optimization. The sliding window is slightly smaller than the
size of the payload buffer: a relatively small chunk of size
`WINDOW_INCR` ("window increment") is cut out of the total payload buffer
size. Thus the sliding window actually has size `S - WINDOW_INCR`. The
name "window increment" refers to the fact that sliding window is only
updated in even multiples of `WINDOW_INCR`. The following diagram shows
what this looks like:

```
                                 WINDOW_INCR
                                  ◀───────▶
  ┌───────────────────────────────────────────────────────────────┐
  │┌────────────────────────┬─────┬───────┬──────────────────────┐│
  ││▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓│.....│░░░░░░░│▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒││
  ││▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓│.....│░░░░░░░│▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒││
  ││▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓│.....│░░░░░░░│▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒││
  │└────────────────────────┴▲────▲───────┴▲─────────────────────┘│
  └─Payload buffer───────────┼────┼────────┼──────────────────────┘
                             │    │        │
                             │    │        buffer_window_start
                             │    │
                             │    buffer_window_end
                             │
                             next_payload_byte

  ┌─Legend───────────────────────────────────────┐
  │                                              │
  │ ░ oldest events, no longer valid             │
  │ ▒ older events, before buffer wrapped around │
  │ ▓ newer events, after buffer wrapped around  │
  │ . next event will be allocated from here     │
  └──────────────────────────────────────────────┘
```

Keep in mind when looking at this diagram, that all values are
stored _before_ modular arithmetic is applied, but for the purpose
of showing them on the diagram, modular arithmetic has been applied
to show the position in the array where they point. The ordering
prior to modular arithmetic is `buffer_window_start <
next_payload_byte < buffer_window_end`.

Once the allocator needs to take bytes from the `WINDOW_INCR`
region, the entire window shifts forward by `WINDOW_INCR`.
The rationale for doing this is that readers must check the value
of `buffer_window_start` on every single read. If the writer also
modified it on every single write, the cache coherency protocol would
create a lot of cache synchronization traffic for this cache line.
By updating it only occasionally, the shared cache line is only
updated after approximately `WINDOW_INCR` new bytes have been
allocated (currently around 16 MiB). Given the distribution of
event sizes, this is approximately once every 100,000 events.

## Considered design alternatives

### Why not large, fixed-sized events and no "payload buffer" scheme?

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

# The execution event recorder

## Preliminaries

You should have a rough idea of how the event system is designed before
reading this. The introductory document is the `event.md` file in the
client library directory, `libs/event`. It explains the basic concepts
and data structures from the reader's perspective.

The file you are reading now explains the specific objects `monad` uses
to record the events, and the rationale for their design.

### Ring and payload diagram

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
defined in `event.h` (which is part of the `monad_event_core` library,
in `libs/event`). It is defined this way:

```c
/// An IPC-style ring used to implement a lock-free MPMC ring for passing event
/// descriptors between threads, potentially in different processes. This
/// object is not directly present in shared memory, but the control page,
/// descriptor table, and payload buffer are.
struct monad_event_ring
{
    struct monad_event_ring_control *control;
    struct monad_event_descriptor *descriptor_table;
    size_t capacity;
    uint8_t *payload_buf;
    size_t payload_buf_size;
};
```

The event descriptor array is called the _descriptor table_ in code, and
its total size is stored in `capacity` field. The `payload_buf` and
`payload_buf_size` fields describe the payload buffer.

The "control" object stores the ring's "writer state": it keeps track
of the last sequence number allocated, the next payload buffer byte to
allocate. This is mapped in a shared page by itself, because this state
is sometimes read by the reader. For example, by default when a read
iterator is initialized it will be set to read the latest event produced.

There is one other piece of data in the control page: the "buffer window".
This is used to detect when event payloads have been overwritten by
subsequent events. This is described in a later section.

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

### Sliding buffer window

Both the event descriptor table and payload buffer are *ring buffers*:
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

The record functions can be called by any number of `monad` threads
simultaneously. Both event descriptor allocation and payload allocation
are always lock-and-wait free.

The general flow of recording is:

1. **Reserve resources** - reserve all resources needed to record the
  event by calling `_monad_event_ring_reserve`. This allocates a slot in
  the descriptor table to hold the descriptor, a sequence number for the
  event, and space in the payload buffer to hold the payload [^1]
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

[^1]: All resources are allocated using a single 16 byte compare-and-swap
instruction. This appears to have better performance than two separate
atomic fetch add instructions. In rare cases, `buffer_window_start` may be
updated as described earlier.

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
    ┌─Recorder (◆)──────────────────────────────────┐ ┌─Shared recorder state (◎)──────────────────┐
    │                                               │ │                                            │
    │ ■   monad_event_descriptor descriptor_table[] │ │ monad_event_thread_info threads[] ■────────┼───┐
    │ │ ■ uint8_t *payload_buf                      │ │ monad_event_block_header block_headers[] ■─┼─┐ │
    │ │ │ monad_event_ring_control *control ■─┐     │ │                                            │ │ │
    └─┼─┼─────────────────────────────────────┼─────┘ └────────────────────────────────────────────┘ │ │
      │ │                                     │                                                      │ │
      │ │                                     ▼                                                      │ │
      │ │                 ╔═Ring control (◮)════════════════╗           ╔═Thread metadata table══╗◀──┼─┘
      │ │                 ║                                 ║           ║ ┌────────────────────┐ ║   │
      │ │                 ║ ■ uint64_t last_seqno           ║           ║ │ Thread 1 metadata  │ ║   │
      │ │                 ║ │ uint64_t next_payload_byte  ■ ║           ║ └────────────────────┘ ║   │
      │ │                 ║ │ uint64_t buffer_window_start│ ║           ║ ┌────────────────────┐ ║   │
      │ │                 ╚═╬═════════════════════════════╬═╝   ┌───────╬─▶ Thread 2 metadata  │ ║   │
      │ │                   │                             │     │       ║ └────────────────────┘ ║   │
      │ │                   │                             │     │       ║ ┌────────────────────┐ ║   │
      │ │                   │                             │     │       ║ │        ...         │ ║   │
      │ │    ╔══════════════╬══════════════════════...═╗  │     │       ║ └────────────────────┘ ║   │
      │ │    ║ ┌─────────┐ ┌▼────────┐ ┌─────────┐     ║  │     │       ╚════════════════════════╝   │
      │ │    ║ │         │ │░░░░░░░░░│ │         │     ║  │     │                                    │
      └─┼───▶║ │ Event 1 │ │░Event 2░│ │ (free)  │     ║  │     │       ╔═Block metadata table═══╗◀──┘
        │    ║ │         │ │░░░░░░░░░│ │         │     ║  │     │       ║ ┌────────────────────┐ ║
        │    ║ └─────────┘ └─────────┘ └─────────┘     ║  │     │   ┌───╬─▶  Block 1 metadata  │ ║
        │    ╚═Event descriptor ring═══════════════...═╝  │     │   │   ║ └────────────────────┘ ║
        │                   ╱         ╲                   │     │   │   ║ ┌────────────────────┐ ║
        │                  ╱           ╲                  │     │   │   ║ │  Block 2 metadata  │ ║
        │                 ╱             ╲                 │     │   │   ║ └────────────────────┘ ║
        │                ╱               ╲                │     │   │   ║ ┌────────────────────┐ ║
        │               ╱                 ╲               │     │   │   ║ │        ...         │ ║
        │                                                 │     │   │   ║ └────────────────────┘ ║
        │            ╔═Event descriptor (◊)══════════╗    │     │   │   ╚════════════════════════╝
        │            ║                               ║    │     │   │
        │            ║ ■ uint64_t payload_buf_offset ║    │     │   │
        │            ║ │ uint8_t source_id ■─────────╬────┼─────┘   │
        │            ║ │ uint16_t block_flow_id ■────╬────┼─────────┘
        │            ╚═╬═════════════════════════════╝    │
        │              │                                  │
        │              │                                  │
        └─▶╔═══════════╬══════════════════════════════════╬════════════════════════════╗
           ║ ┌───────┐ ▼────────────────────────────────┐ ▼──────────────────────────┐ ║
           ║ │Event 1│ │            Event 2             │ │░░░░░░░░░░░free░░░░░░░░░░░│ ║
           ║ │payload│ │            payload             │ │░░░░░░░░░░space░░░░░░░░░░░│ ║
           ║ └───────┘ └────────────────────────────────┘ └──────────────────────────┘ ║
           ╚═Payload buffer════════════════════════════════════════════════════════════╝



       ┌─Legend───────────────────────────────────────┐
       │                                              │
       │ ◆ - struct monad_event_recorder              │
       │ ◎ - struct monad_event_recorder_shared_state │
       │ ◊ - struct monad_event_descriptor            │
       │ ◮ - struct monad_event_ring_control          │
       └──────────────────────────────────────────────┘
```

The diagram contains a minor inaccuracy to make the basic idea easy
to display visually, but which is technically wrong: the last sequence
number does not point *directly* to the array slot of the last produced
event. This is because the array indices start a 0, but sequence numbers
start at 1. In the code that deals with mapping sequence numbers to
array slots, you will see a +1/-1 factor being applied.

### `struct monad_event_recorder`

This object owns most of the state for recording to an event ring. Because
there is more than one event ring, there is a global array of recorders:

```c
extern struct monad_event_recorder
    g_monad_event_recorders[MONAD_EVENT_RING_COUNT];
```

The recorder:

- Is the owner of the ring's shared memory resources for a given
  `monad_event_ring_type`
- Uses an amount of memory that can be configured before it is enabled
  (a reasonable default will be used if not explicitly configured)
- Can be disabled at runtime, in which case no events will be recorded to
  the associated ring (the `MONAD_EVENT_` or `MONAD_TRACE_` macros
  will execute a single `if` statement, then exit)

The two central fields shown in the diagram (`descriptor_table` and
`payload_buf`) which point into shared memory are actually part of
the `struct monad_event_ring` sub-object, not direct fields of
`struct monad_event_recorder` itself. `struct monad_event_ring` is
also used by reader, to hold the memory addresses of the imported
shared memory segments. Only the recorder holds the original
`memfd_create(2)` file descriptors for these regions, however.

### `struct monad_event_recorder_shared_state`

A few bits of internal machinery are shared by all recorders. These
are mostly related to the thread and block header metadata tables,
which are described in `event.md`, and the proper cleanup of the
thread-local objects.

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

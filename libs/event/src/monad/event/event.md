# The `monad` event system

The `monad` execution agent contains a system for recording events that
occur during transaction processing. An event is something such as "an
account balance has been updated" or "a new block has started executing."
`monad` events can be observed by external third-party applications,
using a high-performance inter-process communication channel.

## Overview of events

There are a few parts to the event system:

1. The `monad` execution agent is the *writer* of all events
2. An external application can become a *reader* of events
   using the C library `libmonad_event_queue`, whose implementation
   is in the same directory as this file. Because it is designed for
   third party integration, it does not depend on anything else in the
   `monad` repository and this entire directory's contents may be copied
   into the reader's own codebase. A Rust client library is also available,
   in another repository
3. Some files, such as `event.h` and `event_protocol.h`, are shared by
   both the writer and reader; these are collected into the
  `libmonad_event_core` library, which `libmonad_event_queue` links to

### Basic operation

#### What is an event?

Events are made up two components:

1. The *event descriptor* is a fixed-size (currently 32 byte) object
   describing an event that has happened. It contains the event's type,
   a sequence number, and a timestamp.
2. The *event payload* is a variably-sized piece of extra data about
   the event, which is specific to the event type. For example,
   a "start of transaction" event contains the transaction header as its
   payload. Some events have an empty payload, such as the heartbeat event.
   Some of the fields in the event descriptor not already mentioned are
   used to communicate where in shared memory the payload bytes are located,
   and the payload's length.

#### Where do events live?

When an event occurs, `monad` inserts an event descriptor into a ring
buffer that lives in a shared memory segment. Event payloads live in
large, fixed-size slabs of shared memory called "payload pages". The
diagram below illustrates the memory layout:

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

A few properties about the style of communication chosen:

- Multiple readers may read from the event ring simultaneously, and each
  reader maintains its own iterator position within the ring

- The writer is not aware of the readers -- events are written regardless
  of whether anyone is reading them or not. This implies that the writer
  cannot wait for a reader if it is slow. Thus, readers must iterate through
  events quickly or they will be lost, as queue slots are overwritten by
  later events. Conceptually the event series is a *queue* (it has FIFO
  semantics) but is usually called a *ring* to emphasize these
  overwrite-upon-overflow semantics

- This is why a sequence number is included in the event descriptor. It
  is used both to detect gaps (missing events due to slow readers) and to
  detect whether the data is still valid, when using the zero copy interface

#### An example event and payload

Each kind of event is identified by a unique numerical value, which
corresponds to a C enumeration constant in the `enum monad_event_type` type,
defined in `event_types.h`.

One particularly important event is `MONAD_EVENT_TXN_START`, which is written
by `monad` as soon as a new transaction begins executing within the EVM. It
contains the transaction header, encoded as a C structure, as its event
payload. This structure is also defined in `event_types.h` and its definition
appears below:

```c
/// Event payload for MONAD_EVENT_TXN_START
struct monad_event_txn_header
{
    uint64_t nonce;
    uint64_t gas_limit;
    monad_event_uint256_ne max_fee_per_gas;
    monad_event_uint256_ne value;
    monad_event_address to;
    uint8_t txn_type;
    monad_event_uint256_ne r;
    monad_event_uint256_ne s;
    uint8_t y_parity;
    monad_event_uint256_ne chain_id;
    uint32_t data_length;
};
```

Note that the transaction number is not included in the payload structure.
Because of their importance in the monad blockchain protocol, block and
transaction numbers are encoded directly in the event descriptor (this is
described later in the documentation).

All the C enumeration constants start with a `MONAD_EVENT_` prefix, but
typically the documentation and code comments refer to event types without
the prefix, e.g., `TXN_START` or `THREAD_CREATE`. In other language
bindings, e.g., Rust, these may be named using the languages scoping rules
instead, e.g., `monad_event_type::TXN_START`.

### Event lifetimes, gap detection, and zero copy APIs

#### Sequence numbers

All event descriptors are tagged with an incrementing sequence number
starting at 1. Sequence numbers are 64-bit unsigned integers which never
repeat. Zero is not valid sequence number.

Also note that the sequence number modulo the ring buffer size equals the
ring buffer index where the *next* event wil be located. This is shown
below with a concrete example where the ring buffer size is 64. Note that
the last valid index in the array is 63, then access wraps around to the
beginning of the array at index 0.

```

          idx 61        idx  62       idx  63       idx 0
------.-------------.-------------.-------------.-------------.-----
      | Event       | Event       | Event       | Event       |
 ...  |  seqno 318  |  seqno 319  |  seqno 320  |  seqno 256  |  ...
      |             |             |             |             |
------.-------------.-------------.-------------.-------------.-----
                         ^
                         Next event

last seen sequence number (last_seqno) is initially 318
```

In this example:

- We keep track of the "last seen sequence number" (`last_seqno`) which has
  value `318` to start; being the "last" sequence number means we have already
  finished reading the event with this sequence number, which lives at array
  index `61`

- `318 % 64` is `62`, so we will find the potential next event at that index
  *if* it has been produced

- Observe that the sequence number of the item at index `62` is `319`, which
  is the last seen sequence number plus 1 (`319 == 318 + 1`). This means that
  event `319` has been produced, and its data can be safely read from that
  slot

- When we're ready to advance to the next event, the last seen sequence
  number will be incremented to `319`. As before, we can find the *next*
  event (if it has been produced) at `319 % 64 == 63`. The event at this
  index bears the sequence number `320`, which is again the last seen
  sequence number + 1, therefore this event is also valid

- When advancing a second time, we increment the last seen sequence number
  to `320`. This time, the event at index `320 % 64 == 0` is *not* `321`,
  but is a smaller number, `256`. This means the next event has not been
  written yet, and we are seeing an older event in the same slot. We will
  need to check for a new event later

- Alternatively we might have seen a much larger sequence number, like
  `384` (`320 + 64`). This would mean that we consumed events too slowly, so
  slowly that (at least) the 63 events in the range `[321, 384)` were produced
  in the meantime. These were subsequently overwritten, and are now lost.
  There is no way to recover or replay them

#### Lifetime of an event, zero copy vs. memcpy style

Because of the overwrite behavior, an event descriptor might be overwritten
by the `monad` process while a reader is still reading its data. To prevent
this, the reader needs to do one of two things:

1. Check that the sequence number of the event descriptor matches the value it
   originally had when the reader first saw it, once they are done processing
   the event. Both reads of the sequence number must use atomic memory loads,
   with `memory_order_acquire` (or stronger) ordering. The provided zero copy
   API does this automatically

2. Use one of the provided `memcpy`-style APIs. This effectively
   does the same thing as option 1, but inside the library: event data is
   copied to a user-provided buffer, and before returning we check if the
   lifetime remained valid as the copy finished; the return value indicates
   whether the copy is valid

The reason to prefer zero-copy APIs is that they do not make a copy of the
data, and thus do less work. The reason to prefer memcpy APIs is that it is
not always easy (or possible) to "undo" the work you did if you find out
later that the event was corrupted by an overwrite while you were working
with it. The most logical thing to do in that case is start by copying the
data to stable location, and if the copy isn't valid, to never start the
operation.

An example user of the zero-copy API is the `eventcap` sample program, which
can turn events into printed strings that are sent to `stdout`. The expensive
work of string formatting is performed using the original memory for the
descriptor and payload. Once formatting is complete, `eventcap` checks if an
overwrite happened and if so, does not write the prepared buffer to `stdout`.

Whether you should copy or not depends on the characteristics of the reader,
namely how easily it can deal with "aborting" processing.

#### Event payloads and event lifetime

Recall that events are comprised of both a fixed-size event descriptor and
a variably-sized event payload, and both parts live in separate shared memory
segments. There are a fixed number of event payload pages available, which is
configurable when the `monad` process starts. Once all payload pages have
been used, the oldest page is recycled and its data is overwritten.

Consequently, just as it is possible for event descriptors to be lost if a
reader is too slow, it is also possible for payloads to expire if they are
not read quickly enough. The detection mechanism is simple: each payload page
header bears the sequence number in effect at the time the page was last
recycled. Therefore, if this "overwrite sequence number" is larger than the
sequence number in the event descriptor, it is no longer safe to read the
event payload.

This means that the "zero copy vs. memcpy" decision applies to both the
descriptors and payloads, and the reader could potentially make different
decisions for each.

The user is free to manage the reading and gap recovery logic themselves
by directly manipulating the `struct monad_event_reader` object, but a few
APIs provide some reasonable default behavior for both the zero-copy and
memcpy styles.

#### Zero-copy style APIs

API | Purpose
--- |--------
`monad_event_reader_peek` | Get a zero-copy pointer to an event descriptor, if one is ready
`monad_event_reader_advance` | Advance over the last `monad_event_reader_peek` descriptor, returning `true` if lifetime was active
`monad_event_payload_peek` | Get a zero-copy pointer to an event payload; also returns a pointer to the seqno overwrite indicator

#### Memcpy style APIs

API | Purpose
--- | -------
`monad_event_reader_copy_next` | Copy both the event descriptor and payload as one atomic operation; easiest API to use, but see remark below
`monad_event_reader_bulk_copy` | Bulk memcpy as many event descriptors as will fit in a user-provided array
`monad_event_payload_memcpy` | `memcpy` the event payload to a buffer, succeeding only if the payload copy is valid

The simplest API is `monad_event_reader_copy_next`, which copies both the
descriptor and payload, performs all validity checking, and advances the
iterator if successful. However, the user must take care to provide a large
enough buffer to hold any possible payload or the copied payload may be
truncated. Here is an example of some code which will eventually call
`abort(3)`:

```.c
void read_events(struct monad_event_reader *reader) {
    struct monad_event_descriptor event;
    uint8_t tiny_buf[64]; // This payload buffer is too small for most events

    switch (monad_event_reader_copy_next(reader, &event, tiny_buf, sizeof tiny_buf)) {
    case MONAD_EVENT_READY:
        if (event.length > sizeof tiny_buf) {
            // Event payload has more data than could fit in our buffer, so we're
            // missing part of it. A size of 64 is far too small for many event
            // payloads (e.g., BLOCK_START) so this is guaranteed to happen almost
            // immediately.
            fprintf(stderr, "truncated event! saw large event with size: %u\n",
                    event.length);
            abort();
        } else {
            do_something_with_event(&event, tiny_buf);
        }
        break;

    case MONAD_EVENT_PAYLOAD_EXPIRED:
        [[fallthrough]];
    case MONAD_EVENT_GAP:
        /* ... gap or expired payload, handle it */

    case MONAD_EVENT_NOT_READY:
        break; // Nothing ready, we're done
    }
}
```

### Event descriptors in detail

#### Binary format

The event descriptor is defined this way:

```c
struct monad_event_descriptor
{
    _Atomic(uint64_t) seqno;     ///< Sequence number, for gap/liveness check
    enum monad_event_type type;  ///< What kind of event this is
    uint16_t payload_page;       ///< Shared memory page containing payload
    uint32_t offset;             ///< Offset in page where payload starts
    uint32_t pop_scope : 1;      ///< Ends the trace scope of an event
    uint32_t length : 23;        ///< Size of event payload
    uint32_t source_id : 8;      ///< ID representing origin thread
    uint32_t block_flow_id : 12; ///< ID representing block exec header
    uint32_t txn_num : 20;       ///< Transaction number within block
    uint64_t epoch_nanos;        ///< Time event was recorded
};
```

#### Other fields in `struct monad_event_descriptor`

The fields which have not been described yet are `pop_scope`, `source_id`,
`block_flow_id`, and `txn_num`.

`pop_scope` is used by the performance tracer to express that the
nearest-enclosing tracing scope is terminated by this event. It has no
meaning outside the performance tracer, see the `tracer.md` document for
more information.

The `source_id` field is used to represent which thread recorded an event,
which is needed for the performance tracer. `block_flow_id` does something
similar, associating all events that are part of block execution with that
block. The two IDs have similar properties:

1. They are both a kind of compression strategy. A Linux system thread ID
   is 32 bits, but in practice only a very small number of values occur
   over and over again. It is critical that `struct monad_event_descriptor`
   remain as small as possible for performance reasons, so a system thread ID
   is mapped to a smaller range and that is used instead. The situation for
   a block is similar: although a single block number requires 64 bits,
   `monad` executes *proposed* blocks, so there isn't just one linear block
   number, but a block header whose size is much larger than the event
   descriptor itself. The only way to efficiently represent it in the event
   is to use the same trick. Since there are obviously more than 4095
   blocks in a typical `monad` run, the IDs are recycled. In both cases,
   zero is not valid ID.

2. The maximum values of `source_id` and `block_flow_id` are relatively small
   (255 and 4095, respectively), so it is cheap to look up extra data 
   associated with threads or blocks by using the ID as an array index.

3. The "cheap array index" property is used by the event system itself.
   Source IDs and block flow IDs are defined by the `THREAD_CREATE` and 
   `BLOCK_START` events, respectively. The payloads for these events are
   kept on a special payload page which is never recycled, and those
   payloads live in an array which is indexed by the ID. The address of
   this shared memory array is directly returned to the caller by the
   `monad_event_queue_connect` function. See the `eventcap` sample program
   for an example of how these are used.

The `txn_num` field is self-explanatory. For events related to transactions,
it gives the associated transaction number. This allows the reader to easily
filter the large number of transaction events. For example, upon seeing the
transaction header (the `TXN_START` event payload), a reader decides whether
a transaction is interesting. Keeping the `txn_num` directly in the descriptor
makes it easier to filter through only the interesting `TXN_LOG` events, as
there is no need to look at the event payload (which if memcpy'd, can be
somewhat large) if their ID is not an interesting one.

### Reader and writer communication channels

There are two communication channels between the `monad` writer
and its readers:

1. **Socket-based** - a client connects to a `monad` event queue via a
  UNIX domain socket. A simple protocol running over this socket exports
  the queue's shared memory regions to the consumer, using the ability
  to pass file descriptors over a UNIX socket. Each event queue accessed
  by the client is associated with a unique socket connection, and
  creates a separate `struct monad_event_queue *` handle
2. **Shared-memory-based** - as described, most of the communication
  happens via lock-free shared memory data structures. Once a
  `struct monad_event_queue *` is obtained, the client can create an
  arbitrary number of `struct monad_event_reader` objects to read from
  the queue, with each reader maintaining its own iterator position. This
  communication is one-way: `monad` writes events but the readers do not
  communicate with `monad`

The communication system is based almost entirely on shared memory: the
socket exists only for the initial setup and to detect (via the socket
being closed by the operating system) if either peer process has died.

There is more than one kind of event queue: the standard execution events
are recorded to one queue, and the performance tracer (which has more
overhead, and can be turned off) is a separate queue. When calling
`monad_event_queue_connect`, the client chooses which queue to connect to.
Once the queue is "opened" (all ring buffer and payload page shared memory
segments exported), as many parallel readers as desired can be created.
The reader's iterator state is single threaded.

## Library organization

### `libmonad_event_queue` vs `libmonad_event_core`

The `libmonad_event_queue` library knows how to speak the socket protocol
and set up the shared memory mappings, abstracting away all the low-level
setup details. The `libmonad_event_core` library contains the structure
definitions and inline functions shared between the reader and writer code.
You can use either library directly, or you can use them as an example of
how to write your own low-level consumer machinery.

The files in `libmonad_event_core` are:

File | Contains
---- | ----
`event.h` | Definitions of core shared memory structures and constants
`event_metadata.h` | Structures that describe event and domain metadata (string names, etc.)
`event_metadata.c` | Static data definition of all event metadata; generated code
`event_protocol.h` | Structure types passed over the UNIX domain socket
`event_reader.h` | Defines the basic event reader object and its API; also used directly by `monad` for in-process readers e.g., the tracer
`event_reader_inlines.h` | Definitions of the `event_reader.h` functions, all of which are inlined for performance reasons
`event_types.h` | Definition of the `monad_event_type` enumeration and all payload structures; generated code

The files in `libmonad_event_queue` are:

File | Contains
---- | ----
event_queue.h | API for connecting to an event queue from an external process and exporting its shared memory segments
event_queue.c | Implementation of the `event_queue.h` interface

### Reading events outside of C/C++

As can be seen above, the event reading code is split into a "core" library
(`libmonad_event_core`) and an IPC rendezvous library for remotely accessing
an event queue (`libmonad_event_queue`). When working with execution events
in other programming languages, the "core" library should be natively
reimplemented in that language, while the IPC rendezvous logic of the C
library can be directly reused via a C FFI strategy.

Consider that there are four parts to the event reader:

1. Core definitions of shared memory data structures (`event.h`)

2. Generated code for the event enum, the event payload types,
   and the static metadata (`event_types.h`, `event_metadata.c`)

3. Inline code for polling the event ring (`event_reader.h` and
   `event_read_inline.h`)

4. Code for connecting to the event server and exporting the shared
   memory segments, and initializing event readers (`event_queue.h`,
   `event_queue.c`)

It makes most sense for #1 to be implemented using the native idioms
of the language, using its C layout-compatibility primitives (e.g.,
`#[repr(C)]` in Rust) rather than clunky glue code wrappers. #2 is
generated code anyway, and can just be generated natively for each target
language. The code for #3 is very simple, extremely performance sensitive,
and the ABI stability guarantee is strong (it will likely change only a
few times in development history, and perhaps never). It makes sense to
reimplement natively -- in C, the `reader` interface is entirely inlined,
we don't want to call these functions through a dynamically-linked GOT
entry (and possibly some translation layer) when they are so trivial to
just reimplement.

By contrast, #4 (`event_queue.c`) is slow, verbose, wraps a custom
protocol, could be error prone to reimplement, as is full of exotic
Linux-specific behavior (MAP_HUGETLB stuff, etc.). It's a good candidate
for direct reuse.

This is why items #1, #2, and #3 are collected into one "core" reader
library, while item #4 is separate. For Rust, we provide a native
implementation of the core library, along with bindings that reuse the
C `libmonad_event_queue` to open the shared memory mappings.

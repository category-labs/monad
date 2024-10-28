# The `monad` event system

The `monad` execution agent contains a system for capturing events that
occur during transaction processing. An event is something such as "an
account balance has been updated" or "a new block has started." `monad`
events can be consumed by external third-party applications, using a
high-performance inter-process communication channel.

## Overview of events

There are a few parts to the event system:

1. The `monad` execution agent is the *producer* of all events
2. An external application can become a *consumer* of events
   using the C library `libmonad_event_consumer`, whose implementation
   is in the same directory as this file. Because it is designed for
   third party integration, it does not depend on anything else in the
   `monad` repository and this entire directory's contents may be copied
   into the consumer's own codebase (but see the note below)
3. Some files, such as `event.h`, `event_protocol.h`, and `event_shmem.h`,
   are shared by both the producer and consumer; these are collected into
   a CMake interface library called `monad_event_core`

### How to integrate with the client library

The client library is mostly written in pure C23 with no third-party
dependencies, with one exception: it requires access to the KECCAK-256
hash function. In order to ensure the client and the server have the same
definition of the events, the library computes a (per-domain) hash of the
static event metadata in `event_metadata.c` when it connects to the
server. If this does not match the server's view of the event metadata,
the connection is terminated.

#### Where can I get KECCAK-256?

KECCAK is a cryptographically secure hash function. It won a competition
to become the NIST encryption standard known as SHA-3 (Secure Hash Algorithm
version 3). There are subtle differences between the original KECCAK
algorithm and the standardized SHA-3 version. The original is sometimes
called the "pre-NIST" or "pre-standard" KECCAK hash.

Ethereum uses the pre-NIST KECCAK with 256 bit digests, typically called
KECCAK-256. There are two easy places to get KECCAK-256:

1. OpenSSL, which is available almost everywhere, supports it via the
   EVP_MD API in `libcrypto.so`. However, the "keccak-256" flavor was not
   supported until OpenSSL 3.2, which is not deployed by most systems yet.
2. The directory containing this documentation contains (a symlink to) the
   file `keccak1600.c`, a C source file taken from OpenSSL, and licensed
   accordingly.

`event_consumer.c` currently uses an in-tree `keccak1600.c` but may
switch to requiring `libcrypto.so` in the future.

### Basic operation

#### What is an event?

Events are made up two components:

1. The *event descriptor* is a fixed-size (currently 32 byte) object
   describing an event that has happened. It contains the event's type,
   a sequence number, and a timestamp.
2. The *event payload* is a variably-sized piece of extra data about
   the event, which is specific to the event type. For example,
   a "start of block" event contains the RLP-encoded block header
   as its payload. Some events have an empty payload, such as the
   heartbeat event. The other fields in the event descriptor not already
   mentioned are used to communicate where in shared memory the payload
   bytes are located, and the payload's length.

#### Where do events live?

When an event occurs, an event descriptor is inserted into a lock-free
queue that lives in a shared memory segment. Event payloads live in large,
fixed-size slabs of shared memory called "payload pages". The diagram
below illustrates the memory layout:

```
Event  .---------.---------.---------------.---------.---------.----
Queue  | Event 1 | Event 2 |     ...       | Event N | (empty) | ...
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

                       
Event queue, containing descriptors which point at variably-sized payloads
allocated on "payload pages"
```

Multiple consumers are allowed, and each consumer is given its own event
queue. There is only one set of payload pages, shared by all consumers.

The producer never waits when recording events. If a consumer's event
descriptor queue is full, the producer will wrap around and over-write
older, unconsumed descriptors with newer ones. This is why a sequence
number is included in the event descriptor.

There are a fixed number of event payload pages available, which is
configurable when the `monad` binary starts. Once all payload pages have
been used, the oldest page is recycled and its data is overwritten. Thus,
just as it is possible for event descriptors to be lost (i.e.,
over-written) if a consumer is too slow, it is also possible for payloads
to expire if they are not read quickly enough.

As with sequence numbers, there is a mechanism to detect this: each page
bears a "generation number" and when a page is recycled, this number
increases. The page's generation number at the time of recording an event
is also included in the event descriptor. If it does not match the
generation number the page currently has, then the event payload is gone:
it was part of an earlier instance using the same chunk of memory.

#### Event descriptors

The event descriptor is defined this way:

```c
struct monad_event_descriptor
{
    enum monad_event_type type;  ///< What kind of event this is
    uint16_t payload_page;       ///< Shared memory page containing payload
    uint32_t offset;             ///< Offset in page where payload starts
    uint32_t pop_scope : 1;      ///< Ends the trace scope of an event
    uint32_t length : 23;        ///< Size of event payload
    uint32_t source_id : 8;      ///< ID describing origin thread
    uint32_t page_generation;    ///< Page generation number
    uint64_t seqno;              ///< Sequence number, for gap detection
    uint64_t epoch_nanos;        ///< Time event was recorded
};
```

The only fields which have not been described yet are `pop_scope` and
`source_id`. `pop_scope` is used the performance tracer to express that the
nearest-enclosing tracing scope is terminated by this event.

Te `source_id` field is used to access some information about the thread
which recorded an event. It is used primarily by the performance tracer. The
ID is an index into an array of these structures, which live in a fixed
(never recycled) payload page:

```c
struct monad_event_thread_info
{
    uint64_t seqno;
    uint64_t epoch_nanos;
    uint64_t thread_id;
    uint8_t source_id;
    char thread_name[31];
};
```

See the `cmd/eventcap` example program for an example of how to use this.

#### Event types and domains

Each kind of event is assigned an enumeration constant in the C enumeration
type `enum monad_event_type`. For example, the "start of block" event
has the C identifier `MONAD_EVENT_BLOCK_START`, which has numeric code
`768`.

Event enumeration values are not assigned in a strictly sequential manner:
instead, they are organized into numerical ranges called "domains". An
event domain behaves like a category of events, and event capture can
be enabled or disabled at the domain level. The first four domains are:

 Domain name | Domain code | Description
 ----------- |-------------| -------
 internal | 1           | Events occurring inside the event recorder
 perf | 2           | Events needed for the performance tracer
 block | 3           | Block-related events
 txn | 4           | Transaction-related events

An event's enumeration constant is a 16-bit unsigned value: the most
significant 8 bits are the domain, and the least significant 8 bits are
assigned sequentially within the domain ("domain relative code").

```
LSB                                        MSB
.----------------------.----------------------.
| Domain Relative Code |      Domain Code     |
.----------------------.----------------------.
 0                    7 8                   15
```

For example, the `block` domain has code `3`, so `enum monad_event_type`
values in the range `[768, 1024)` are block-related events.
`MONAD_EVENT_BLOCK_START` is the first block-related event, so its code is
`768`, or `(3 << 8) | 0`. The second block-related event is
`MONAD_EVENT_BLOCK_END`, and it has code `769`. The C preprocessor macros
`MONAD_EVENT_DOMAIN` and `MONAD_EVENT_DRCODE` can be used to extract
the two 8-bit components from a single event enumeration value.

#### Why domains?

Certain domains are always interesting, whereas others (particularly the
tracing-and-performance-related domains) emit huge amounts of data that are
impractical to enable at all times. Not only would most consumers not be
interested in these, but performance would degrade if everything were enabled
at all times.

An event is only recorded to a consumer's event queue if they have *enabled*
recording events for that domain. The enabling mechanism is simple: a bitmask
(currently limits to 64 bits) determines whether an event domain is enabled
or not. The least significant bit is considered to be domain 1, so the mask
`0b1111` enables the first four domains that are listed above.

#### Producer and consumer communication channels

There are two communication channels between the producer and consumer:

1. **Socket-based** - a consumer connects to `monad` via a UNIX domain
  socket. A simple protocol running over this socket exports the shared
  memory regions from `monad` to the consumer, using the ability to pass
  file descriptors over a UNIX socket. This socket is also used by the
  consumer, to change the domain enable mask. The domain enable mask is
  initially `0`, to prevent the queue from overflowing while the consumer
  is still initializing. Each consumer event queue is associated with
  a unique socket connection.
2. **Shared-memory-based** - as described, most of the communication
  happens via high-performance lock-free shared memory data structures.
  This communication is one-way: the producer writes events and the
  consumer reads them.

The communication system is based almost entirely on shared memory: the
socket exists only for the initial setup, to change the domain mask, and
to detect (via the socket being closed by the operating system) if either
peer process has died.

#### `monad_event_consumer` vs `monad_event_core`

The `monad_event_consumer` library knows how to speak the socket protocol
and set up the shared memory mappings, abstracting away all the low-level
setup details. You can use it directly, or you can use it as an example of
how to write your own low-level consumer machinery. The (header-only)
`monad_event_core` library contains the structure definitions of the various
objects shared between the producer and consumer. These are:

File | Contains
---- | ----
`event.h` | Core definitions of event enumeration types and structures 
`event_protocol.h` | Structure types passed over the UNIX domain socket
`event_shmem.h` | Shared memory data structures mapped into both producer and consumer processes

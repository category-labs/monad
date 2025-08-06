# Event recorder implementation details

This file contains documentation for programmers that work on the event
ring code itself.

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
payload has expired, in the `monad_event_ring_payload_check` function.

Although this is the _concept_ of the algorithm, the recorder applies a
small optimization. The sliding window is slightly smaller than the
real size of the payload buffer: a relatively small chunk of size
`WINDOW_INCR` ("window increment") is effectively cut out of the total
payload buffer size -- not literally, but for the purpose of detecting
overflow.

Thus the sliding window actually has size `S - WINDOW_INCR`. The
"increment" in the name "window increment" refers to the fact that
sliding window is only updated in multiples of `WINDOW_INCR`. The
following diagram shows what this looks like:

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

Once the allocator needs to take bytes from the `WINDOW_INCR` region,
the entire window shifts forward by to the end of the payload, rounded
up to the nearest multiple of `WINDOW_INCR`.

The rationale for doing this is that readers must check the value of
`buffer_window_start` on every single read. If the writer also modified
`buffer_window_start` on every single write, the cache coherency
protocol would create a lot of cache synchronization traffic for this
cache line.

By updating it only occasionally, the shared cache line is only updated
after approximately `WINDOW_INCR` new bytes have been allocated
(currently around 16 MiB). Given the distribution of event sizes, this
happens approximately once every few seconds. This means that the
readers (which are _always_ reading this cache line) are usually seeing
it in a shared but unmodified state: either the 'S' state in the MOESI
protocol, or the 'S' or 'F' states in the MESIF protocol.

The window increment is large enough to greatly reduce cache
synchronization traffic, but not large enough to take too many bytes
away from the payload buffer.

# Event recorder interface and implementation details

This file contains documentation for programmers that want to record events.
It also describes some of the recorder implementation details.

## Recording events in C and C++

There are two interfaces for event ring recording:

- The C recording API (`event_recorder.h`) implements the lowest-level
  recording functionality; it is only ~100 lines of code

- The C++ recording API (`event_recorder.hpp`) is a wrapper around the C API
  that is more idomatic in C++ code; it also detects payload overflow errors
  and automatically records the special event `RECORD_ERROR_EVENT` if such an
  error occurs

### How do I record an event?

In both the C and C++ APIs, the process takes three steps. The C API will
be described first.

1. **Reserve resources for recording** -- first, the caller allocates an
   event descriptor and enough buffer space to hold the event payload; both
   are allocated by the C API `monad_event_recorder_reserve`

2. **Initialize the event descriptor fields and copy the event payload** --
   next, the caller sets the `event_type` and `content_ext` fields in the
   event descriptor to their desired values, and copies the event payload
   into the buffer returned in the reservation step

3. **Commit the event** -- finally, the caller marks the event as "ready"
   by calling the `monad_event_recorder_commit` function, passing in the
   sequence number that was originally returned in the reservation step

In the C++ API, the three step "reserve-initialize-commit" process is the same,
but it comes with a few idiomatic features and cleaner error handling. The three
steps are connected by this simple aggregate type:

```
template <typename T>
struct ReservedEvent
{
    monad_event_descriptor *event;
    T *payload;
    uint64_t seqno;
};
```

The template type `T` is an event payload type, e.g., `struct monad_exec_txn_log`
in the execution events schema.

1. A call to `EventRecorder::reserve_event<T>` returns a `ReservedEvent<T>`

2. The caller initializes the descriptor and the payload as before, but having
   a typed `payload` allows for clean aggregate initalization without type casts

3. A call to `EventRecorder::commit` accepts the earlier `ReservedEvent<T>`
   instance, and performs the commit

To understand how the reserve/commit protocol works, read the execution events
SDK documentation that describes how sequence numbers and event lifetimes work.
This can be found in the
[advanced topics](https://docs.monad.xyz/execution-events/advanced)
section of the SDK. Then read the comments in the `monad_event_recorder_reserve`
function implementation.

### The C++ `EventRecorder::reserve_event` function in detail

The full signature of this function is:

```cpp
template <
    typename T, typename EventEnum,
    std::same_as<std::span<std::byte const>>... U>
    requires std::is_enum_v<EventEnum>
[[nodiscard]] ReservedEvent<T> EventRecorder::reserve_event(EventEnum, U...);
```

Below is an example of how it is typically called (from the unit test suite,
but with some comments added):

```cpp
// Step 1: allocate event resources
ReservedEvent const vlt_event =
    recorder->reserve_event<monad_test_event_vlt>(
        MONAD_TEST_EVENT_VLT,
        as_bytes(std::span{VLT_ARRAY_1}).subspan(0),
        as_bytes(std::span{VLT_ARRAY_2}).subspan(0));

// Step 2: initialize event payload
*vlt_event.payload = monad_test_event_vlt{
    .vlt_1_length = static_cast<uint32_t>(std::size(VLT_ARRAY_1)),
    .vlt_2_length = static_cast<uint32_t>(std::size(VLT_ARRAY_2))};

// In the C++ API we don't need to set the `event_type` in the event descriptor,
// the reserve step does it (thus why we passed `MONAD_TEST_EVENT_VLT` above)
// but we can still set any needed `context_ext` parameters
vlt_event.event->content_ext[0] = CONTENT_EXT_0;

// Step 3: commit event
recorder->commit(vlt_event);
```

A few things to note here:

- `T`, the event payload type template argument, is explicitly specified when
  the function is called, e.g.,
  `reserve_event<monad_test_event_vlt>(MONAD_TEST_EVENT_VLT, ...)`

- We usually _don't_ have to specify the template argument in the return
  type, e.g., it's just `ReservedEvent const vlt_event` and not the more
  verbose `ReservedEvent<monad_test_event_vlt> const vlt_event` because the
  template argument is deduced by
  [CTAD](https://en.cppreference.com/cpp/language/class_template_argument_deduction)

- `EventEnum` is the specific enumeration type used by event ring's content
   type, e.g., `enum monad_test_event` for the test suite events; the actual
   type is deduced from the argument, which above is `MONAD_TEST_EVENT_VLT`;
   unlike in the C API, the reserve step also sets the `event_type` in the
   event descriptor

- The two `as_bytes(...)` arguments are variadic template arguments described
  below (note: events that do not have variable-length data also call
  `reserve_event`, with an empty `U...` parameter pack)

Many event types have variable length payloads. For example, in the execution
events schema, an EVM log event records a variable number of log topics and an
arbitrary `data` field. These are called "variable length trailing" (VLT)
arrays. In the test event schema, `MONAD_TEST_EVENT_VLT` is a dummy event that
has two variable length trailing arrays.

`reserve_event` takes a variadic list of arguments, where each argument in the
variadic list must be a `std::span<std::byte const>` describing the bytes in a
variable length trailing array.

The reservation step allocates a single payload buffer large enough to hold
the "main" event payload data type (of type `T`), plus all the optional VLT
byte arrays.

One possibly surprising wrinkle is that the "reserve" step not only allocates
buffer space for variable-length arrays that follow the `T` object in the
payload, but will also `memcpy(3)` the VLT contents to the buffer at reservation
time.

The reason variable-length data is memcpy'd immediately but the fixed
sized part of the event payload (of type `T`) is not, is simple: the "core"
part of the event payload usually does not already exist in the program. It's
an "event payload type" that we create on demand, _just to record the event_.
To avoid copying it immediately after creating it, we want to create it directly
in event buffer memory.

The VLT data, in actual usage, is never like that. It is _not_ constructed for
the purpose of recording the event, but already exists somewhere in the program
for some "business logic" reason not related to event recording. So it must be
copied, because the place where it naturally lives is not already in the event
ring buffer.

Consider this C++ type that models an Ethereum log:

```cpp
struct Log
{
    byte_string data{};
    std::vector<bytes32_t> topics{};
    Address address{};
}
```

Suppose we want to record a `TXN_LOG` event using the data in one of these `Log`
objects.

The corresponding event payload type describing the log is
`struct monad_exec_txn_log`. An instance of it does _not_ already exist prior
to us wanting to record a `TXN_LOG` event. It is an artifact of the recording
process. Thus, it has to be manually initialized by us, so `reserve_event`
returns a `monad_exec_txn_log *` pointing to the payload buffer space for us to
perform zero-copy initialization.

The two VLTs -- the `topics` and `data` arrays -- are different. They exist
already, and just need to be copied into event ring shared memory.

`reserve_event` needs to know the total size of the VLTs at reservation time,
in order to reserve enough space for them. It might as well just copy the
contents too, to save the caller from having to do the `memcpy` boilerplate.

Doing it this way also simplifies the handling of the `RECORD_ERROR` type,
which is described in the next section.

### C++ recording behavior is always defined

The C reservation step can fail if the payload size exceeds `UINT32_MAX`.
In that case, it returns a `nullptr` event descriptor pointer. The caller
must check the pointer value every time, to avoid dereferencing `nullptr`.

In the C++ recording interface, recording never fails. If the event you tried
to record would cause an error, it just records an event of a different type,
which reports that recording error.

Because event rings are based on circular buffers, there is no dynamic
resource allocation. The only kind of recording errors that can happen are
related to event payloads that are too large to be recorded without truncation.

There are two different flavors of these, depending on whether the payload was
strictly too big (exceeded `UINT32_MAX`) or whether it was just too big for the
current event ring. As an example of the latter, a 500 megabyte payload is
legal, but won't fit in an event ring with a 256 megabyte payload buffer.[^1]

In these cases, a special event is recorded to report the error, and it includes
a truncated version of the original event. This is to help with production
debugging, because enormous events are expected to never happen at reasonable
gas expenditure, and so probably represent some kind of protocol exploit.

Recall that each content type of an event ring uses its own enumeration for its
`event_type` encoding. To be compatible with this feature, the value `1` in
every event content schema must be reserved for the `RECORD_ERROR` event type.
It has payload type `struct monad_event_record_error`, defined in
`event_ring.h`.

[^1]: In the C API, only exceeding `UINT32_MAX` will cause `nullptr` to be
returned. If you try to record a 500 MiB event to a 256-MiB-sized payload
buffer, recording will _succeed_ but will appear to be expired immediately
when read. The C++ API refers to this as an "expiry on creation" error, which
has recording error type `MONAD_EVENT_RECORD_ERROR_OVERFLOW_EXPIRE`.

## Sliding buffer window

Both the event descriptor array and payload buffer are *ring buffers*:
once all array slots have been used, subsequent writes wrap around to the
beginning of the array. For event descriptors, the detection mechanism for
slow consumers observing an overwrite relies on the sequence number, as
described in the SDK documentation. For the payload buffer, a similar idea
is used, except using the byte offset in the payload buffer (similar to the
byte sequence number in the TCP protocol).

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

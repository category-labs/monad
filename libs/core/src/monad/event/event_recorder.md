# Event recorder internals

This document is about the `monad` event recording internals, not the event
system in general. For that, see the `event.md` file in the `libs/event`
folder.

## Overview

### Basic design

In the general event overview documentation (the `event.md` file mentioned
above) the terms "producer" and "consumer" are used. This directory
contains the implementation of the "producer", which is divided into a few
layers.

The important objects are:

- `struct monad_event_recorder_queue` - a multi-producer, single-consumer
  lock-free queue, where all event descriptors are initially recorded
- `struct monad_event_recorder` - this global singleton object owns
  the MPSC recorder queue, the payload page pool, and the global domain
  enablement mask
- `struct monad_event_thread_state` - for the fastest possible lock-free
  recording, some thread-local data is cached in this object
- `struct monad_event_session` - this object represents an event
  producer/consumer pair; it contains an event descriptor single-producer,
  single-consumer queue and the consumer's own domain enable mask
- `void *session_sync_thread_main(void*)` - the main function of the
  "session sync thread"; this thread drains the recorder's event queue
  of all new events, and copies them to active session event queues
- `struct monad_event_server` - this represents the UNIX domain socket
  server, which allows external processes to start remote event sessions
- `struct monad_event_client` - this object (which is defined locally
  in `event_server.c`), represents a single logged-in client of the
  UNIX domain server

Note that this system is a pipeline: events are recorded to a global
multi-producer "recorder queue," and a dedicated thread copies them to
consumer-facing queues, after performing domain filtering.

A simple diagram shows the main actors:

```
  Execution           Recording layer                       Session layer
   Worker          (monad_event_recorder)                (monad_event_session)
   Threads
              write                      reads                   writes
              events                     events                  events
 .----------.   to   .----------------.  from    .-------------.   to.  .------------.
 | Thread 1 | --.--> | MSPC recorder  | <------- | Sync Thread | --.--> | Session 1  |
 .----------.   |    |    queue and   |          .-------------.   |    | SPSC queue |
                |    |    page pool   |                            |    .------------.
 .----------.   |    .----------------.                            |
 | Thread 2 | --/                                                  |
 .----------.   |                                                  |    .------------.
                .                                                  \--- | Session 2  |
     ...        .                                                  |    | SPSC queue |
                .                                                  |    .------------.
                |                                                  .
 .----------.   |                                                  .         ...
 | Thread N | --/                                                  .
 .----------.                                                      |    .------------.
                                                                   \--- | Session M  |
                                                                        | SPSC queue |
                                                                        .------------.
```

The reason for this additional complexity is performance-related, and was
added only after simpler designs proved to be too slow.

The sessions don't always exist: they are created later (usually by external
processes connecting via an IPC mechanism) and they can be destroyed
early, e.g., if a process exits.

Meanwhile, it is critical that the initial recording of the events be as fast
as possible. This is easiest to do if the place they are recording to
always exists, regardless of whether or not anyone is listening. This design
decouples the initial recording path from the needs of the consumers and their
dynamic nature. This made the recording stage faster, and also easier to
understand: there is almost no coupling between the recorder and session
layers, isolating the complexity of each.

### Clarification of concepts

#### "Session" vs. "producer"

Although the generic documentation talks about the "producer" and
"consumer", there is no such object as "the producer", at least in the
sense that there is not a `struct monad_event_producer` defined in the
code.

From the perspective an IPC consumer, the "producer" is just the
"sync thread", which copies event descriptors from the recorder into the
SPSC queues owned by the sessions. The `struct monad_event_session` can be
thought of as the shared state of a "producer/consumer queue pair".

#### "Sessions" vs "clients"

There is a clean separation between an event recording "session" and a
socket client: there are no socket-related API calls in
`event_session.{h,c}`, and there are no event-related API calls in
`event_server.{h,c}`.

This implies that you could easily make a local event consumer within the
`monad` process itself. The steps would be:

1. Spawn a thread to drain an event descriptor queue
2. Call `monad_event_open_session` to create the producer/consumer resources
   for your consumer
3. Call `monad_event_set_session_domain_mask` to set the domain enable
   mask
4. Directly drain the event descriptor queue using `struct monad_event_ring`
   object inside the `struct monad_event_session`
5. Call `monad_event_close_session` when done

You would not need to start (or even create) the server object. Currently,
this approach is used by the test suite.

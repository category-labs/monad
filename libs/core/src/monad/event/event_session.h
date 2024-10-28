#pragma once

#include <stddef.h>
#include <stdint.h>

#include <monad/event/event.h>
#include <monad/event/event_shmem.h>

#define MONAD_EVENT_MAX_SESSIONS 8U

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_event_ring;
struct monad_event_session;

/// Open an event recording session, i.e., the shared state of a single
/// producer/consumer pair
extern int
monad_event_session_open(uint8_t ring_shift, struct monad_event_session **);

/// Close an event recording session previously opened via a call to
/// monad_event_open_session
extern void monad_event_session_close(struct monad_event_session *);

/// Set the session-level domain mask
extern void monad_event_session_set_domain_mask(
    struct monad_event_session *, uint64_t domain_mask);

/// Return a description of the last session error that occurred on this thread
extern char const *monad_event_session_get_last_error();

/// Event payload of the internal:SYNC_EVENT_GAP
struct monad_event_sync_gap
{
    uint64_t last_seqno;
    struct monad_event_descriptor event;
};

/// Each event consumer needs its own event descriptor queue and domain
/// enablement mask; these are tracked by an object called an "event session"
struct monad_event_session
{
    alignas(64) _Atomic(uint64_t) domain_mask;
    TAILQ_ENTRY(monad_event_session) next;
    uint32_t session_id;
    struct monad_event_ring event_ring;
    alignas(64) atomic_bool busy;
};

#define MONAD_EVENT_SESSION_CTOR_PRIO (MONAD_EVENT_RECORDER_CTOR_PRIO + 1)

#ifdef __cplusplus
} // extern "C"
#endif

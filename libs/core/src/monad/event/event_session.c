#include <errno.h>
#include <stdbit.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include <pthread.h>
#include <sched.h>
#include <sys/mman.h>
#include <sys/queue.h>
#include <unistd.h>

#include <monad/core/assert.h>
#include <monad/core/spinlock.h>
#include <monad/core/spinloop.h>
#include <monad/core/srcloc.h>
#include <monad/event/event.h>
#include <monad/event/event_recorder.h>
#include <monad/event/event_session.h>
#include <monad/event/event_shared.h>
#include <monad/event/event_shmem.h>

static thread_local char g_error_buf[1024];

__attribute__((format(printf, 3, 4))) static int format_errc(
    monad_source_location_t const *srcloc, int err, char const *format, ...)
{
    int rc;
    va_list ap;
    va_start(ap, format);
    rc = _monad_event_vformat_err(
        g_error_buf, sizeof g_error_buf, srcloc, err, format, ap);
    va_end(ap);
    return rc;
}

#define FORMAT_ERRC(...)                                                       \
    format_errc(&MONAD_SOURCE_LOCATION_CURRENT(), __VA_ARGS__)

TAILQ_HEAD(monad_event_session_list, monad_event_session);

static struct monad_event_session_global
{
    alignas(64) monad_spinlock_t lock;
    struct monad_event_session_list active_sessions;
    struct monad_event_session_list free_sessions;
    struct monad_event_session all_sessions[MONAD_EVENT_MAX_SESSIONS];
    unsigned last_session_id;
    pthread_t sync_thread;
    alignas(64) atomic_bool run_sync_thread;
} g_sessions;

static void __attribute__((constructor(MONAD_EVENT_SESSION_CTOR_PRIO)))
event_sessions_ctor()
{
    struct monad_event_session *session;
    monad_spinlock_init(&g_sessions.lock);
    TAILQ_INIT(&g_sessions.active_sessions);
    TAILQ_INIT(&g_sessions.free_sessions);

    for (uint8_t s = 0; s < MONAD_EVENT_MAX_SESSIONS; ++s) {
        session = &g_sessions.all_sessions[s];
        session->session_id = s;
        TAILQ_INSERT_TAIL(&g_sessions.free_sessions, session, next);
    }
}

static void __attribute__((destructor(MONAD_EVENT_SESSION_CTOR_PRIO)))
event_sessions_dtor()
{
    // Stop the producer side from creating more data, and wait for the sync
    // thread to catch up
    monad_event_recorder_halt();

    // Signal the sync thread to exit and then join with it; then force all the
    // open sessions to close
    atomic_store_explicit(
        &g_sessions.run_sync_thread, false, memory_order_release);
    pthread_join(g_sessions.sync_thread, nullptr);
    while (!TAILQ_EMPTY(&g_sessions.active_sessions)) {
        monad_event_session_close(TAILQ_FIRST(&g_sessions.active_sessions));
    }
}

static int mmap_event_ring(
    struct monad_event_ring *ring, uint8_t ring_shift, char const *ring_id)
{
    int rc;
    size_t mmap_page_size;
    char name[32];

    // Map the ring control structure (a single, minimum-sized VM page)
    mmap_page_size = (size_t)getpagesize();
    snprintf(name, sizeof name, "evt_rc:%s", ring_id);
    ring->control_fd = memfd_create(name, MFD_CLOEXEC);
    if (ring->control_fd == -1) {
        return FORMAT_ERRC(errno, "memfd_create(2) failed for %s", name);
    }
    if (ftruncate(ring->control_fd, (off_t)mmap_page_size) == -1) {
        return FORMAT_ERRC(errno, "ftruncate(2) failed for %s", name);
    }
    ring->control = mmap(
        nullptr,
        mmap_page_size,
        PROT_READ | PROT_WRITE,
        MAP_SHARED,
        ring->control_fd,
        0);
    if (ring->control == MAP_FAILED) {
        return FORMAT_ERRC(errno, "mmap(2) unable to map %s", name);
    }

    rc = _monad_event_mmap_descriptor_table(
        MONAD_EVENT_RING_TYPE_SHARED,
        ring_shift,
        ring_id,
        format_errc,
        &ring->descriptor_table,
        &ring->capacity,
        &ring->descriptor_table_fd);
    if (rc != 0) {
        return rc;
    }
    MONAD_ASSERT(stdc_has_single_bit(ring->capacity));
    ring->capacity_mask = ring->capacity - 1;
    return 0;
}

void unmap_event_ring(struct monad_event_ring *ring)
{
    (void)close(ring->control_fd);
    munmap(ring->control, (size_t)getpagesize());
    (void)close(ring->descriptor_table_fd);
    _monad_event_unmap_descriptor_table(ring->descriptor_table, ring->capacity);
}

static void write_sync_gap_event(
    struct monad_event_session **sessions, size_t num_sessions,
    uint64_t last_seqno, struct monad_event_descriptor const *event)
{
    struct monad_event_descriptor thr_gap_event;
    struct monad_event_sync_gap sync_gap_info;
    struct monad_event_thread_state *sync_thread_state;
    void *dst;

    sync_thread_state = _monad_event_get_thread_state();
    thr_gap_event.epoch_nanos = monad_event_get_epoch_nanos();
    thr_gap_event.type = MONAD_EVENT_SYNC_EVENT_GAP;
    thr_gap_event.pop_scope = 0;
    sync_gap_info.last_seqno = last_seqno;
    sync_gap_info.event = *event;
    dst = _monad_event_alloc_payload(
        &sync_thread_state->payload_page,
        &thr_gap_event,
        sizeof sync_gap_info,
        sync_thread_state->source_id);
    memcpy(dst, &sync_gap_info, sizeof sync_gap_info);
    for (size_t s = 0; s < num_sessions; ++s) {
        monad_event_ring_write_descriptor(
            &sessions[s]->event_ring, &thr_gap_event);
    }
}

static void write_initial_session_events(struct monad_event_session *session)
{
    struct monad_event_descriptor event;
    struct monad_event_thread_info *thread_info;
    struct monad_event_thread_state *sync_thread_state;
    uint64_t thread_source_ids;
    unsigned source_id;
    void *dst;

    // When a session starts, we write one THREAD_CREATE for every thread that
    // already exists so the client can understand the source_id -> thread map
    MONAD_SPINLOCK_LOCK(&g_monad_event_recorder.lock);
    thread_source_ids = g_monad_event_recorder.thread_source_ids;
    while (thread_source_ids != 0) {
        source_id = stdc_first_trailing_one(thread_source_ids);
        thread_info = &g_monad_event_recorder.thread_info[source_id];
        event.type = MONAD_EVENT_THREAD_CREATE;
        event.epoch_nanos = thread_info->epoch_nanos;
        event.pop_scope = 0;
        event.source_id = thread_info->source_id;
        _monad_event_set_metadata_descriptor_payload(
            thread_info, sizeof *thread_info, &event);
        monad_event_ring_write_descriptor(&session->event_ring, &event);
        thread_source_ids &= ~(uint64_t)(1UL << (source_id - 1));
    }
    MONAD_SPINLOCK_UNLOCK(&g_monad_event_recorder.lock);

    // We also write SESSION_START to announce the session is beginning, along
    // with a mapping between the global and local sequence numbers
    sync_thread_state = _monad_event_get_thread_state();
    event.epoch_nanos = monad_event_get_epoch_nanos();
    event.type = MONAD_EVENT_SESSION_START;
    event.pop_scope = 0;
    dst = _monad_event_alloc_payload(
        &sync_thread_state->payload_page,
        &event,
        sizeof(uint64_t),
        sync_thread_state->source_id);
    memcpy(
        dst,
        &g_monad_event_recorder.recorder_queue.consume_next,
        sizeof(uint64_t));
    monad_event_ring_write_descriptor(&session->event_ring, &event);
}

static uint64_t copy_recorder_events_to_sessions(
    struct monad_event_recorder_queue *rq,
    struct monad_event_session **sessions, size_t num_sessions,
    uint64_t last_seqno)
{
    size_t const EVENT_BUFS = 64;
    uint64_t domain_enable_bit;
    uint64_t domain_mask;
    struct monad_event_descriptor events[EVENT_BUFS];
    struct monad_event_session *session;
    size_t num_events;

    // Bulk dequeue all events from the recorder, then loop over each one and
    // offer to it each session
    uint64_t const consume_next =
        atomic_load_explicit(&rq->consume_next, memory_order_relaxed);
    uint64_t const prod_tail =
        atomic_load_explicit(&rq->prod_tail, memory_order_acquire);
    MONAD_ASSERT(prod_tail >= consume_next);
    size_t const available_events = prod_tail - consume_next;
    num_events = available_events > EVENT_BUFS ? EVENT_BUFS : available_events;
    memcpy(
        events,
        &rq->descriptor_table[consume_next & rq->capacity_mask],
        sizeof events[0] * num_events);
    atomic_store_explicit(
        &rq->consume_next, consume_next + num_events, memory_order_relaxed);
    for (size_t e = 0; e < num_events; ++e) {
        if (MONAD_UNLIKELY(events[e].seqno != last_seqno + 1)) {
            write_sync_gap_event(
                sessions, num_sessions, last_seqno, &events[e]);
        }
        last_seqno = events[e].seqno;
        domain_enable_bit =
            MONAD_EVENT_DOMAIN_MASK(MONAD_EVENT_DOMAIN(events[e].type));
        for (size_t s = 0; s < num_sessions; ++s) {
            session = sessions[s];
            domain_mask = atomic_load_explicit(
                &session->domain_mask, memory_order_acquire);
            if (MONAD_UNLIKELY((domain_mask & domain_enable_bit) == 0)) {
                // Session is not interested in this event
                continue;
            }
            monad_event_ring_write_descriptor(&session->event_ring, &events[e]);
        }
    }
    return last_seqno;
}

static void *session_sync_thread_main(void *arg0)
{
    size_t const CHECK_STATE_SHIFT_MASK = (1UL << 4) - 1;
    struct monad_event_session *session;
    struct monad_event_session *pinned_sessions[MONAD_EVENT_MAX_SESSIONS];
    uint64_t last_seqno = 0;
    size_t num_sessions = 0;
    size_t sync_iterations = 0;
    pthread_barrier_t *const sync_ready_barrier = arg0;

    // Set our name, then poke the thread state so that our THREAD_CREATE event
    // gets injected now
    pthread_setname_np(pthread_self(), "event_sync");
    (void)_monad_event_get_thread_state();

    // The recorder is held until we're ready to drain the queue; release it
    pthread_barrier_wait(sync_ready_barrier);
    while (atomic_load_explicit(
        &g_sessions.run_sync_thread, memory_order_acquire)) {
        if (MONAD_UNLIKELY((sync_iterations++ & CHECK_STATE_SHIFT_MASK) == 0)) {
            // On occasion, we lock the active session list to rebuild the
            // pinned sessions

            // First unbusy all the pinned sessions, in case any of them wants
            // to close; then rescan for new sessions
            for (size_t s = 0; s < num_sessions; ++s) {
                atomic_store_explicit(
                    &pinned_sessions[s]->busy, false, memory_order_release);
            }
            num_sessions = 0;
            MONAD_SPINLOCK_LOCK(&g_sessions.lock);
            TAILQ_FOREACH(session, &g_sessions.active_sessions, next)
            {
                atomic_store_explicit(
                    &session->busy, true, memory_order_release);
                pinned_sessions[num_sessions++] = session;
                if (MONAD_UNLIKELY(
                        atomic_load_explicit(
                            &session->event_ring.control->prod_next,
                            memory_order_relaxed) == 0)) {
                    // This session is new; push a few initial events
                    write_initial_session_events(session);
                }
            }
            MONAD_SPINLOCK_UNLOCK(&g_sessions.lock);
        }

        // Poll the recorder queue, copying its events into the active sessions
        last_seqno = copy_recorder_events_to_sessions(
            &g_monad_event_recorder.recorder_queue,
            pinned_sessions,
            num_sessions,
            last_seqno);
    }

    for (size_t s = 0; s < num_sessions; ++s) {
        atomic_store_explicit(
            &pinned_sessions[s]->busy, false, memory_order_release);
    }

    return nullptr;
}

int monad_event_session_open(
    uint8_t ring_shift, struct monad_event_session **session_p)
{
    struct monad_event_session *session;
    char ring_id[20];
    int rc;

    MONAD_ASSERT(session_p != nullptr);
    MONAD_SPINLOCK_LOCK(&g_sessions.lock);
    *session_p = session = TAILQ_FIRST(&g_sessions.free_sessions);
    if (session == nullptr) {
        MONAD_SPINLOCK_UNLOCK(&g_sessions.lock);
        return FORMAT_ERRC(
            ENOBUFS,
            "maximum number of sessions %u reached",
            MONAD_EVENT_MAX_SESSIONS);
    }
    if (ring_shift == 0) {
        ring_shift = MONAD_EVENT_CONSUMER_DEFAULT_RING_SHIFT;
    }
    session->session_id = ++g_sessions.last_session_id;
    snprintf(ring_id, sizeof ring_id, "session:%u", session->session_id);
    rc = mmap_event_ring(&session->event_ring, ring_shift, ring_id);
    if (rc != 0) {
        --g_sessions.last_session_id;
        MONAD_SPINLOCK_UNLOCK(&g_sessions.lock);
        return rc;
    }

    TAILQ_REMOVE(&g_sessions.free_sessions, session, next);
    TAILQ_INSERT_TAIL(&g_sessions.active_sessions, session, next);
    MONAD_SPINLOCK_UNLOCK(&g_sessions.lock);
    return 0;
}

void monad_event_session_close(struct monad_event_session *session)
{
    MONAD_ASSERT(session != nullptr);

    atomic_store_explicit(&session->domain_mask, 0, memory_order_release);
    MONAD_SPINLOCK_LOCK(&g_sessions.lock);
    TAILQ_REMOVE(&g_sessions.active_sessions, session, next);
    MONAD_SPINLOCK_UNLOCK(&g_sessions.lock);

    while (atomic_load_explicit(&session->busy, memory_order_acquire)) {
        monad_spinloop_hint();
    }

    unmap_event_ring(&session->event_ring);
    MONAD_SPINLOCK_LOCK(&g_sessions.lock);
    TAILQ_INSERT_TAIL(&g_sessions.free_sessions, session, next);
    MONAD_SPINLOCK_UNLOCK(&g_sessions.lock);
}

void monad_event_session_set_domain_mask(
    struct monad_event_session *session, uint64_t domain_mask)
{
    atomic_store_explicit(
        &session->domain_mask, domain_mask, memory_order_release);
}

char const *monad_event_session_get_last_error()
{
    return g_error_buf;
}

void _monad_event_session_start_sync_thread(pthread_barrier_t *sync_ready_barrier)
{
    int rc;
    if (atomic_exchange_explicit(
            &g_sessions.run_sync_thread, true, memory_order_acq_rel)) {
        return; // Already initialized
    }
    rc = pthread_create(
        &g_sessions.sync_thread, nullptr, session_sync_thread_main, sync_ready_barrier);
    if (rc != 0) {
        extern char const *__progname;
        FORMAT_ERRC(rc, "unable to start session sync thread");
        fprintf(stderr, "%s: [fatal] %s\n", __progname, g_error_buf);
        abort();
    }
}

void _monad_event_session_wait_drain_queue()
{
    uint64_t prod_tail;
    uint64_t consume_next;
    struct monad_event_recorder_queue *const rq =
        &g_monad_event_recorder.recorder_queue;
    if (atomic_load_explicit(&g_sessions.run_sync_thread, memory_order_acquire)) {
        MONAD_DEBUG_ASSERT(g_monad_event_recorder.domain_enable_mask == 0);
        do {
            prod_tail = atomic_load_explicit(&rq->prod_tail, memory_order_relaxed);
            consume_next = atomic_load_explicit(&rq->consume_next, memory_order_relaxed);
        } while (consume_next != prod_tail);
    }
}

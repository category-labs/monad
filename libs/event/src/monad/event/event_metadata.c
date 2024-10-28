#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <errno.h>

#include <monad/event/event.h>
#include <monad/event/event_metadata.h>

#define MONAD_EVENT_MK_META(C_SUFFIX, CAMEL_NAME, TRACE_FLAGS, DESCRIPTION)    \
    {.type = MONAD_EVENT_##C_SUFFIX,                                           \
     .trace_flags = (TRACE_FLAGS),                                             \
     .c_symbol = "MONAD_EVENT_" #C_SUFFIX,                                     \
     .c_name = #C_SUFFIX,                                                      \
     .camel_name = #CAMEL_NAME,                                                \
     .description = DESCRIPTION},

static struct monad_event_metadata const s_internal_events[] = {
#define MONAD_EVENT_DEF(...) MONAD_EVENT_MK_META(__VA_ARGS__)
#include "definitions/internal.def"
};

static struct monad_event_metadata const s_perf_events[] = {
#define MONAD_EVENT_DEF(...) MONAD_EVENT_MK_META(__VA_ARGS__)
#include "definitions/perf.def"
};

static struct monad_event_metadata const s_block_events[] = {
#define MONAD_EVENT_DEF(...) MONAD_EVENT_MK_META(__VA_ARGS__)
#include "definitions/block.def"
};

static struct monad_event_metadata const s_txn_events[] = {
#define MONAD_EVENT_DEF(...) MONAD_EVENT_MK_META(__VA_ARGS__)
#include "definitions/txn.def"
};

static struct monad_event_metadata const s_fiber_events[] = {
#define MONAD_EVENT_DEF(...) MONAD_EVENT_MK_META(__VA_ARGS__)
#include "definitions/fiber.def"
};

static struct monad_event_metadata const s_stats_events[] = {
#define MONAD_EVENT_DEF(...) MONAD_EVENT_MK_META(__VA_ARGS__)
#include "definitions/stats.def"
};

#define MONAD_EVENT_METADATA_COUNT(X)                                          \
    (sizeof(X) / sizeof(struct monad_event_metadata))

struct monad_event_domain_metadata const g_monad_event_domain_meta[] = {
    [MONAD_EVENT_DOMAIN_NONE] =
        {.domain = MONAD_EVENT_DOMAIN_NONE,
         .name = "none",
         .description = "reserved domain code so that 0 remains unmapped",
         .event_meta = nullptr,
         .num_events = 0},

    [MONAD_EVENT_DOMAIN_INTERNAL] =
        {.domain = MONAD_EVENT_DOMAIN_INTERNAL,
         .name = "internal",
         .description =
             "events that occur inside the event recording framework",
         .event_meta = s_internal_events,
         .num_events = MONAD_EVENT_METADATA_COUNT(s_internal_events)},

    [MONAD_EVENT_DOMAIN_PERF] =
        {.domain = MONAD_EVENT_DOMAIN_PERF,
         .name = "perf",
         .description = "events needed for the performance tracer",
         .event_meta = s_perf_events,
         .num_events = MONAD_EVENT_METADATA_COUNT(s_perf_events)},

    [MONAD_EVENT_DOMAIN_BLOCK] =
        {.domain = MONAD_EVENT_DOMAIN_BLOCK,
         .name = "block",
         .description = "events related to block-level execution",
         .event_meta = s_block_events,
         .num_events = MONAD_EVENT_METADATA_COUNT(s_block_events)},

    [MONAD_EVENT_DOMAIN_TXN] =
        {.domain = MONAD_EVENT_DOMAIN_TXN,
         .name = "txn",
         .description = "events related to transaction-level execution",
         .event_meta = s_txn_events,
         .num_events = MONAD_EVENT_METADATA_COUNT(s_txn_events)},

    [MONAD_EVENT_DOMAIN_FIBER] =
        {.domain = MONAD_EVENT_DOMAIN_FIBER,
         .name = "fiber",
         .description =
             "events related to fiber scheduling and synchronization",
         .event_meta = s_fiber_events,
         .num_events = MONAD_EVENT_METADATA_COUNT(s_fiber_events)},

    [MONAD_EVENT_DOMAIN_STATS] =
        {.domain = MONAD_EVENT_DOMAIN_STATS,
         .name = "stats",
         .description = "events with summary statistics payloads",
         .event_meta = s_stats_events,
         .num_events = MONAD_EVENT_METADATA_COUNT(s_stats_events)},
};

size_t const g_monad_event_domain_meta_size =
    sizeof g_monad_event_domain_meta / sizeof g_monad_event_domain_meta[0];

int monad_event_metadata_serialize(
    struct monad_event_domain_metadata const *domain, char **meta_buf,
    size_t *meta_buf_size)
{
    struct monad_event_metadata const *evt_meta;
    struct monad_event_metadata const *evt_meta_end;
    FILE *meta_file;
    long meta_pos;
    int saved_error;

    meta_file = open_memstream(meta_buf, meta_buf_size);
    if (meta_file == nullptr) {
        return errno;
    }

#define DOMAIN_META_WRITE(BUF, LENGTH)                                         \
    do {                                                                       \
        if (fwrite((BUF), (LENGTH), 1, meta_file) != 1) {                      \
            saved_error = errno;                                               \
            goto Error;                                                        \
        }                                                                      \
    }                                                                          \
    while (0)

#define DM_WR_FIELD(FIELD) DOMAIN_META_WRITE(&FIELD, sizeof FIELD)
#define DM_WR_STRING(STR_FIELD)                                                \
    DOMAIN_META_WRITE(STR_FIELD, strlen(STR_FIELD) + 1)

    DM_WR_FIELD(domain->domain);
    DM_WR_STRING(domain->name);
    DM_WR_STRING(domain->description);
    DM_WR_FIELD(domain->num_events);
    for (evt_meta = domain->event_meta,
        evt_meta_end = evt_meta + domain->num_events;
         evt_meta != evt_meta_end;
         ++evt_meta) {
        DM_WR_FIELD(evt_meta->type);
        DM_WR_FIELD(evt_meta->trace_flags);
        DM_WR_STRING(evt_meta->c_symbol);
        DM_WR_STRING(evt_meta->c_name);
        DM_WR_STRING(evt_meta->camel_name);
        DM_WR_STRING(evt_meta->description);
    }

#undef DM_WR_STRING
#undef DM_WR_FIELD
#undef DOMAIN_META_WRITE

    meta_pos = ftell(meta_file);
    if (meta_pos == -1) {
        saved_error = errno;
        goto Error;
    }
    if (fflush(meta_file) == -1) {
        saved_error = errno;
        goto Error;
    }

    // Truncate the number of bytes to the number written, not the buffer size
    *meta_buf_size = (size_t)meta_pos;
    fclose(meta_file);
    return 0;

Error:
    fclose(meta_file);
    free(*meta_buf);
    *meta_buf = nullptr;
    *meta_buf_size = 0;
    return saved_error;
}

int monad_event_metadata_deserialize(
    char const *buf, size_t buf_size,
    struct monad_event_domain_metadata *domain_meta,
    int (*event_alloc_fn)(struct monad_event_domain_metadata *, void *),
    void *alloc_param)
{
    struct monad_event_metadata *evt_meta;
    struct monad_event_metadata *evt_meta_end;
    char const *buf_next = buf;
    char const *const buf_end = buf + buf_size;
    size_t len;
    int rc;

#define DM_RD_FIELD(FIELD)                                                     \
    do {                                                                       \
        if (buf_next + sizeof(FIELD) > buf_end) {                              \
            return EIO;                                                        \
        }                                                                      \
        memcpy((void *)&(FIELD), buf_next, sizeof(FIELD));                     \
        buf_next += sizeof(FIELD);                                             \
    }                                                                          \
    while (0)

#define DM_ASSIGN_STR(FIELD)                                                   \
    do {                                                                       \
        len = strnlen(buf_next, (size_t)(buf_end - buf_next));                 \
        if (len == 0 || len == (size_t)(buf_end - buf_next)) {                 \
            return EIO;                                                        \
        }                                                                      \
        (FIELD) = (char const *)buf_next;                                      \
        buf_next += len + 1;                                                   \
    }                                                                          \
    while (0)

    DM_RD_FIELD(domain_meta->domain);
    DM_ASSIGN_STR(domain_meta->name);
    DM_ASSIGN_STR(domain_meta->description);
    DM_RD_FIELD(domain_meta->num_events);
    if (event_alloc_fn != nullptr) {
        if ((rc = event_alloc_fn(domain_meta, alloc_param)) != 0) {
            return rc;
        }
    }
    if (domain_meta->event_meta == nullptr) {
        return EFAULT;
    }
    for (evt_meta = (struct monad_event_metadata *)domain_meta->event_meta,
        evt_meta_end = evt_meta + domain_meta->num_events;
         evt_meta != evt_meta_end;
         ++evt_meta) {
        DM_RD_FIELD(evt_meta->type);
        DM_RD_FIELD(evt_meta->trace_flags);
        DM_ASSIGN_STR(evt_meta->c_symbol);
        DM_ASSIGN_STR(evt_meta->c_name);
        DM_ASSIGN_STR(evt_meta->camel_name);
        DM_ASSIGN_STR(evt_meta->description);
    }

#undef DM_ASSIGN_STR
#undef DM_RD_FIELD

    return 0;
}

/*
 * Look-up structure: domain lookup is handled via a simple static lookup
 * structure that is like a bucket-chained hash table, but simpler:
 * the first lower-case letter of the domain name indexes the bucket list
 * (just a fixed-size array) of domain pointers for domains starting with that
 * letter.
 */

// Set to the maximum collision length
#define MONAD_EVENT_LOOKUP_BUCKETS 1

static struct monad_event_domain_metadata const
    *s_domain_lookup[][MONAD_EVENT_LOOKUP_BUCKETS] = {
        ['b' - 'a'] = {&g_monad_event_domain_meta[MONAD_EVENT_DOMAIN_BLOCK]},
        ['f' - 'a'] = {&g_monad_event_domain_meta[MONAD_EVENT_DOMAIN_FIBER]},
        ['i' - 'a'] = {&g_monad_event_domain_meta[MONAD_EVENT_DOMAIN_INTERNAL]},
        ['p' - 'a'] = {&g_monad_event_domain_meta[MONAD_EVENT_DOMAIN_PERF]},
        ['s' - 'a'] = {&g_monad_event_domain_meta[MONAD_EVENT_DOMAIN_STATS]},
        ['t' - 'a'] = {&g_monad_event_domain_meta[MONAD_EVENT_DOMAIN_TXN]},
};

struct monad_event_domain_metadata const *
monad_event_metadata_lookup(char const *domain_name)
{
    if (domain_name == nullptr || domain_name[0] < 'a' ||
        domain_name[0] > 'z') {
        return nullptr;
    }
    struct monad_event_domain_metadata const **bucket =
        s_domain_lookup[domain_name[0] - 'a'];
    for (unsigned i = 0; i < MONAD_EVENT_LOOKUP_BUCKETS; ++i) {
        if (bucket[i] && strcmp(bucket[i]->name, domain_name) == 0) {
            return bucket[i];
        }
    }
    return nullptr;
}

int monad_event_parse_domain_mask(char const *input, uint64_t *mask)
{
    if (input == nullptr || mask == nullptr) {
        return EFAULT;
    }
    *mask = 0;
    if (isdigit(*input)) {
        errno = 0;
        *mask = strtoull(input, nullptr, 0);
        return errno;
    }
    if (strcmp(input, "all") == 0) {
        *mask = MONAD_EVENT_DOMAIN_ENABLE_ALL;
        return 0;
    }
    if (strcmp(input, "none") == 0) {
        *mask = MONAD_EVENT_DOMAIN_ENABLE_NONE;
        return 0;
    }
    char *const tokens = strdup(input);
    char *saveptr;
    char *domain_name = strtok_r(tokens, ",", &saveptr);
    struct monad_event_domain_metadata const *domain_meta;
    while (domain_name != nullptr) {
        domain_meta = monad_event_metadata_lookup(domain_name);
        if (domain_meta == nullptr) {
            free(tokens);
            return EINVAL;
        }
        *mask |= MONAD_EVENT_DOMAIN_MASK(domain_meta->domain);
        domain_name = strtok_r(nullptr, ",", &saveptr);
    }
    free(tokens);
    return 0;
}

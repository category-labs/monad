#pragma once

#include <monad/config.h>

#include <stddef.h>

#ifdef __cplusplus
extern "C"
{
#endif

//! \brief Header tag for DB write i/o log. See `storage_pool` for format.
static char const monad_lbl_db_write_io_log[] = "DBWRTIOL";

//! \brief Header at the top of every log file
struct monad_lbl_file_header
{
    //! \brief Magic written for you "MNL0"
    char magic[4];
    //! \brief Reserved for future feature flags, written for you.
    uint32_t flags_reserved_ : 32;
    //! \brief The UTC nanosecond count when the log was opened
    uint64_t utc_ns_count_on_creation;
    //! \brief The CPU ticks when the log was opened
    uint64_t cpu_ticks_on_creation;
    uint32_t reserved_;

    //! \brief Number of user supplied header bytes
    uint32_t user_supplied_header_bytes;
    //! \brief The user supplied header bytes
    char user_supplied_header[];
};
#if __STDC_VERSION__ >= 202300L || defined(__cplusplus)
static_assert(sizeof(struct monad_lbl_file_header) == 32);
    #ifdef __cplusplus
static_assert(alignof(struct monad_lbl_file_header) == 8);
    #endif
#endif

//! \brief Header at the top of every log entry
struct monad_lbl_entry_header
{
    //! \brief The length of this log entry including this header in bytes
    uint64_t length : 21; // max 2Mb
    //! \brief The CPU ticks when this was logged minus that when the last entry
    //! was logged. If a log entry is not done every 2.44 hours, this will wrap.
    uint64_t cpu_ticks_delta : 43;

    //! \brief The user supplied header bytes
    char content[];
};
#if __STDC_VERSION__ >= 202300L || defined(__cplusplus)
static_assert(sizeof(struct monad_lbl_entry_header) == 8);
    #ifdef __cplusplus
static_assert(alignof(struct monad_lbl_entry_header) == 8);
    #endif
#endif

//! \brief OPTIONAL footer at the tail of every log file
struct monad_lbl_file_footer
{
    uint64_t monad_lbl_entry_header_placeholder;

    //! \brief Magic written for you "MNL0"
    char magic[4];
    //! \brief Reserved for future feature flags, written for you.
    uint32_t flags_reserved_ : 32;

    //! \brief The UTC nanosecond count when the log was closed
    uint64_t utc_ns_count_on_close;
    //! \brief The CPU ticks when the log was closed
    uint64_t cpu_ticks_on_close;
    //! \brief Total uncompressed data written
    uint64_t uncompressed_content_length;
};
#if __STDC_VERSION__ >= 202300L || defined(__cplusplus)
static_assert(sizeof(struct monad_lbl_file_footer) == 40);
static_assert(
    offsetof(struct monad_lbl_file_footer, magic) ==
    sizeof(struct monad_lbl_entry_header));
    #ifdef __cplusplus
static_assert(alignof(struct monad_lbl_file_footer) == 8);
    #endif
#endif

//! \brief Public information about the lightweight binary logger
typedef struct monad_lbl_head
{
    //! \brief The file being written into (or tail thereof). Useful to
    //! disambiguate between instances.
    char const path[32];

    //! \brief Total uncompressed bytes written
    uint64_t uncompressed_bytes_written;
    //! \brief Total log file bytes written
    uint64_t file_bytes_written;

    //! \brief Logger write buffer starvation events
    uint32_t write_buffer_starvation_events;
    //! \brief Logger pacing events
    uint32_t pacing_events;
} *monad_lbl;

/*! \brief Create a new lightweight binary logger writing into `path`.

`monad_lbl_file_header` will be appended first, followed by
`user_header` and `user_header_bytes` which can be any header any bytes you
wish. Note that the total header must be under 2Mb total.
*/
BOOST_OUTCOME_C_NODISCARD extern monad_c_result monad_lbl_create(
    monad_lbl *logger, char const *path, void const *user_header,
    size_t user_header_bytes);

/*! \brief Destroy an existing lightweight binary logger.
 */
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_lbl_destroy(monad_lbl logger);

/*! \brief THREADSAFE Add an entry to the lightweight binary logger.

`monad_lbl_entry_header` will be appended first, followed by your content of
choice. It is entirely up to you what that content is. Note that the total
log entry must be under 2Mb total.

Overhead is approx 30 nanoseconds for a four byte content.
*/
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_lbl_add(monad_lbl logger, void const *content, size_t bytes);

/*! \brief THREADSAFE Flush any backlog in the lightweight binary logger.
 */
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_lbl_flush(monad_lbl logger);

#ifdef __cplusplus
}
#endif

#include <errno.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include <fcntl.h>
#include <linux/magic.h>
#include <poll.h>
#include <sys/file.h>
#include <sys/inotify.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/vfs.h>
#include <unistd.h>

#include <category/core/cleanup.h>
#include <category/core/event/event_ring_util.h>
#include <category/core/format_err.h>
#include <category/core/srcloc.h>

// Defined in event_ring.c, so we can share monad_event_ring_get_last_error()
extern thread_local char _g_monad_event_ring_error_buf[1024];

#define FORMAT_ERRC(...)                                                       \
    monad_format_err(                                                          \
        _g_monad_event_ring_error_buf,                                         \
        sizeof(_g_monad_event_ring_error_buf),                                 \
        &MONAD_SOURCE_LOCATION_CURRENT(),                                      \
        __VA_ARGS__)

// Given a path which may not exist, walk backward until we find a parent path
// that does exist; the caller must free(3) parent_path
static int find_existing_parent_path(char const *path, char **parent_path)
{
    struct stat path_stat;

    *parent_path = nullptr;
    if (strlen(path) == 0) {
        return FORMAT_ERRC(EINVAL, "path cannot be nullptr or empty");
    }
    *parent_path = strdup(path);

StatAgain:
    if (stat(*parent_path, &path_stat) == -1) {
        if (errno != ENOENT) {
            // stat failed for some reason other than ENOENT; we just give up
            // in this case
            return FORMAT_ERRC(errno, "stat of `%s` failed", *parent_path);
        }

        // For ENOENT failures, climb up the path until we find a path that
        // does exist. If we were given an absolute path, we'll eventually
        // succeed in stat'ing `/` (and thus won't always get ENOENT). If we
        // were given a relative path, we'll eventually run out of `/`
        // characters, in which case the path of interest is assumed to be
        // the current working directory, "."
        char *const last_path_sep = strrchr(*parent_path, '/');
        if (last_path_sep == nullptr) {
            strcpy(*parent_path, ".");
        }
        else {
            *last_path_sep = '\0';
            goto StatAgain;
        }
    }
    return 0;
}

static bool check_flock_entry(
    char *lock_line, ino_t const ring_ino,
    struct monad_event_flock_info *fl_info)
{
    char *saveptr;
    ino_t lock_ino = 0;
    unsigned tok_num = 0;

    for (char const *tok = strtok_r(lock_line, " ", &saveptr);
         tok != nullptr && tok_num <= 5;
         tok = strtok_r(nullptr, " ", &saveptr), ++tok_num) {
        switch (tok_num) {
        case 1:
            if (strcmp(tok, "FLOCK") != 0) {
                return false;
            }
            break;

        case 2:
            if (strcmp(tok, "ADVISORY") != 0) {
                return false;
            }
            break;

        case 3:
            if (strcmp(tok, "WRITE") == 0) {
                fl_info->lock = LOCK_EX;
            }
            else if (strcmp(tok, "READ") == 0) {
                fl_info->lock = LOCK_SH;
            }
            else {
                return false;
            }
            break;

        case 4:
            if (sscanf(tok, "%d", &fl_info->pid) != 1) {
                return false;
            }
            break;

        case 5:
            if (sscanf(tok, "%*x:%*x:%ju", &lock_ino) != 1) {
                return false;
            }
            break;

        default:
            break;
        }
    }

    return lock_ino == ring_ino;
}

static inline struct timespec
timespec_sub(struct timespec lhs, struct timespec rhs)
{
    struct timespec r = {
        .tv_sec = lhs.tv_sec - rhs.tv_sec,
        .tv_nsec = lhs.tv_nsec - rhs.tv_nsec};
    if (r.tv_nsec < 0) {
        r.tv_sec -= 1;
        r.tv_nsec += 1'000'000'000L;
    }
    return r;
}

static int wait_for_new_file(
    int const inotify_fd, char const *const filename,
    struct timespec const *timeout, sigset_t const *sigmask)
{
    int rc;
    struct timespec poll_start_time;
    struct timespec poll_end_time;
    struct timespec residual_timeout;
    bool const has_timeout = timeout != nullptr;

    struct pollfd pfd = {
        .fd = inotify_fd,
        .events = POLLIN,
    };

    if (has_timeout) {
        residual_timeout = *timeout;
    }

    do {
        alignas(struct inotify_event) uint8_t event_buf[4096];
        uint8_t *p = event_buf;
        ssize_t n_read;

        (void)clock_gettime(CLOCK_MONOTONIC, &poll_start_time);
        rc = ppoll(&pfd, 1, has_timeout ? &residual_timeout : nullptr, sigmask);
        (void)clock_gettime(CLOCK_MONOTONIC, &poll_end_time);
        if (rc == -1) {
            return FORMAT_ERRC(errno, "ppoll error, %s creation", filename);
        }

        n_read = read(inotify_fd, &event_buf, sizeof event_buf);
        if (n_read == -1) {
            return FORMAT_ERRC(
                errno, "read of inotify_fd failed, %s creation", filename);
        }

        while (p < event_buf + (size_t)n_read) {
            struct inotify_event const *const event =
                (struct inotify_event const *)p;
            if (event->len > 0 && strcmp(event->name, filename) == 0 &&
                (event->mask & IN_ISDIR) == 0) {
                return 0;
            }
            if (event->mask & IN_DELETE_SELF) {
                return FORMAT_ERRC(ENOTDIR, "parent directory deleted");
            }
            p += sizeof *event + event->len;
        }

        if (has_timeout) {
            struct timespec const poll_duration =
                timespec_sub(poll_end_time, poll_start_time);
            residual_timeout = timespec_sub(residual_timeout, poll_duration);
        }
    }
    while (!has_timeout || residual_timeout.tv_sec >= 0);

    return FORMAT_ERRC(ETIMEDOUT, "%s creation poll timed out", filename);
}

static int open_excl_writer_file(
    char const *const path, int const open_flags, int *const out_fd,
    pid_t *const out_pid)
{
    int rc;
    int fd;
    pid_t pid;

    fd = open(path, open_flags);
    if (fd == -1) {
        return FORMAT_ERRC(errno, "open of %s failed", path);
    }
    rc = monad_event_ring_query_excl_writer_pid(fd, &pid);
    if (out_pid != nullptr) {
        *out_pid = pid;
    }
    if (rc != 0 || out_fd == nullptr) {
        (void)close(fd);
        return rc;
    }
    *out_fd = fd;
    return 0;
}

int monad_event_ring_query_flocks(
    int ring_fd, struct monad_event_flock_info *flocks, size_t *size)
{
    struct stat ring_stat;
    struct monad_event_flock_info fl_info_buf;
    size_t const capacity = *size;
    char info_buf[128];
    FILE *lock_info_file [[gnu::cleanup(cleanup_fclose)]] = nullptr;

    *size = 0;
    if (fstat(ring_fd, &ring_stat) == -1) {
        return FORMAT_ERRC(errno, "fstat failed");
    }
    lock_info_file = fopen("/proc/locks", "r");
    if (lock_info_file == nullptr) {
        return FORMAT_ERRC(errno, "fopen of /proc/locks failed");
    }
    while (fgets(info_buf, sizeof info_buf, lock_info_file) != nullptr) {
        if (check_flock_entry(info_buf, ring_stat.st_ino, &fl_info_buf)) {
            if (*size == capacity) {
                return FORMAT_ERRC(ERANGE, "more flocks than copy-out space");
            }
            flocks[(*size)++] = fl_info_buf;
        }
    }
    return 0;
}

int monad_event_ring_wait_for_excl_writer(
    char const *const path, struct timespec const *const timeout,
    sigset_t const *const sigmask, int const open_flags, int *const out_fd,
    pid_t *const pid)
{
    constexpr uint32_t NotifyMask =
        IN_CREATE | IN_MOVED_TO | IN_DELETE_SELF | IN_ONLYDIR;

    char const *last_path_sep;
    char const *filename;
    struct stat path_stat;
    int wd;
    int rc;
    int inotify_fd [[gnu::cleanup(cleanup_close)]] = -1;

    if (out_fd != nullptr) {
        *out_fd = -1;
    }
    if (pid != nullptr) {
        *pid = 0;
    }

    inotify_fd = inotify_init1(IN_CLOEXEC);
    if (inotify_fd == -1) {
        return FORMAT_ERRC(errno, "inotify_init1 failed");
    }

    last_path_sep = strrchr(path, '/');
    if (last_path_sep == nullptr) {
        wd = inotify_add_watch(inotify_fd, ".", NotifyMask);
        filename = path;
    }
    else {
        size_t const dirname_len = (size_t)(last_path_sep - path);
        char *dirname [[gnu::cleanup(cleanup_free)]] = malloc(dirname_len + 1);
        *(char *)mempcpy(dirname, path, dirname_len) = '\0';
        wd = inotify_add_watch(inotify_fd, dirname, NotifyMask);
        filename = last_path_sep + 1;
    }
    if (wd == -1) {
        return FORMAT_ERRC(
            errno, "inotify_add_watch failed for parent dir of %s", path);
    }

    // Before waiting for the file to be created, check if it's already there
    rc = stat(path, &path_stat);
    if (rc == -1 && errno != ENOENT) {
        return FORMAT_ERRC(errno, "stat of %s failed", path);
    }
    if (rc == 0) {
        if ((path_stat.st_mode & S_IFMT) != S_IFREG) {
            // The use of EACCES to mean "not a regular file" is unusual, but
            // matches the execve(2) behavior; in the directory case, use EISDIR
            int const error_code =
                path_stat.st_mode == S_IFDIR ? EISDIR : EACCES;
            return FORMAT_ERRC(error_code, "%s is not a regular file", path);
        }
        goto FileReady;
    }

    // ENOENT case: if it's created at any point after the above check, it will
    // create an inotify event; wait for it to appear
    rc = wait_for_new_file(inotify_fd, filename, timeout, sigmask);
    if (rc != 0) {
        return rc;
    }

FileReady:
    return out_fd != nullptr || pid != nullptr
               ? open_excl_writer_file(path, open_flags, out_fd, pid)
               : 0;
}

int monad_check_path_supports_map_hugetlb(char const *path, bool *supported)
{
    char *parent_path;
    struct statfs fs_stat;
    int rc;

    *supported = false;
    rc = find_existing_parent_path(path, &parent_path);
    if (rc != 0) {
        goto Done;
    }
    if (statfs(parent_path, &fs_stat) == -1) {
        rc = FORMAT_ERRC(errno, "statfs of `%s` failed", parent_path);
        goto Done;
    }
    else {
        // Only hugetlbfs supports MAP_HUGETLB
        *supported = fs_stat.f_type == HUGETLBFS_MAGIC;
        rc = 0;
    }
Done:
    free(parent_path);
    return rc;
}

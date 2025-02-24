#include <stdarg.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <errno.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include <zstd.h>

#include <monad/event/event_error.h>
#include <monad/event/event_test_util.h>

static thread_local char g_error_buf[1024];

__attribute__((format(printf, 3, 4))) static int format_errc(
    struct monad_event_source_location const *srcloc, int err,
    char const *format, ...)
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
    format_errc(&MONAD_EVENT_SOURCE_LOCATION_CURRENT(), __VA_ARGS__)

int monad_event_rsm_load_snapshot_from_bytes(
    void const *rsm_bytes, size_t rsm_len, char const *error_name,
    char const *shm_name)
{
    char namebuf[32];
    int rc;
    int shm_fd = -1;
    void *map_base = nullptr;
    struct monad_event_rsm_header const *const header = rsm_bytes;

    if (shm_name == nullptr) {
        return FORMAT_ERRC(EFAULT, "shm_name cannot be nullptr");
    }
    if (error_name == nullptr) {
        snprintf(namebuf, sizeof namebuf, "buffer %p", rsm_bytes);
        error_name = namebuf;
    }
    if (rsm_len < sizeof *header || memcmp(
                                        header->magic,
                                        MONAD_EVENT_RSM_MAGIC,
                                        sizeof MONAD_EVENT_RSM_MAGIC) != 0) {
        rc = FORMAT_ERRC(EPROTO, "%s is not valid RSM file", error_name);
        goto Error;
    }
    shm_fd = shm_open(
        shm_name,
        O_RDWR | O_CREAT | O_TRUNC,
        S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH);
    if (shm_fd == -1) {
        return FORMAT_ERRC(errno, "shm_open could not create %s", shm_name);
    }
    if (ftruncate(shm_fd, (off_t)header->decompressed_size) == -1) {
        rc = FORMAT_ERRC(errno, "ftruncate of %s failed", shm_name);
        goto Error;
    }
    map_base = mmap(
        nullptr,
        header->decompressed_size,
        PROT_READ | PROT_WRITE,
        MAP_SHARED,
        shm_fd,
        0);
    if (map_base == MAP_FAILED) {
        rc = FORMAT_ERRC(errno, "mmap of %s failed", shm_name);
        goto Error;
    }
    size_t const decompress_len = ZSTD_decompress(
        map_base,
        header->decompressed_size,
        (uint8_t *)rsm_bytes + sizeof *header,
        rsm_len - sizeof *header);
    if (ZSTD_isError(decompress_len)) {
        rc = FORMAT_ERRC(
            EIO,
            "zstd decompress error: %s",
            ZSTD_getErrorName(decompress_len));
        goto Error;
    }
    munmap(map_base, header->decompressed_size);
    (void)close(shm_fd);
    return 0;

Error:
    if (map_base != nullptr) {
        munmap(map_base, header->decompressed_size);
    }
    (void)close(shm_fd);
    shm_unlink(shm_name);
    return rc;
}

int monad_event_rsm_load_snapshot_from_fd(
    int fd, char const *error_name, char const *shm_name)
{
    struct stat s;
    void *map_base;
    size_t map_len;
    char name_buf[16];
    if (error_name == nullptr) {
        snprintf(name_buf, sizeof name_buf, "fd %d", fd);
        error_name = name_buf;
    }
    if (fstat(fd, &s) == -1) {
        return FORMAT_ERRC(errno, "stat of %s failed", error_name);
    }
    map_len = (size_t)s.st_size;
    map_base = mmap(nullptr, map_len, PROT_READ, MAP_SHARED, fd, 0);
    if (map_base == MAP_FAILED) {
        return FORMAT_ERRC(errno, "mmap of fd %s failed", error_name);
    }
    int const r = monad_event_rsm_load_snapshot_from_bytes(
        map_base, map_len, error_name, shm_name);
    (void)munmap(map_base, map_len);
    return r;
}

int monad_event_rsm_load_snapshot_from_file(
    char const *path, char const *shm_name)
{
    if (path == nullptr) {
        return FORMAT_ERRC(EFAULT, "path cannot be nullptr");
    }
    int const fd = open(path, O_RDONLY);
    if (fd == -1) {
        return FORMAT_ERRC(errno, "could not open %s", path);
    }
    int const r = monad_event_rsm_load_snapshot_from_fd(fd, path, shm_name);
    (void)close(fd);
    return r;
}

char const *monad_event_rsm_get_last_error()
{
    return g_error_buf;
}

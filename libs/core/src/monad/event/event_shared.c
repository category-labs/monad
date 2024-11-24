#include <stdarg.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>

#include <monad/core/srcloc.h>
#include <monad/event/event_shared.h>

static char const *final_path_component(char const *path)
{
    char const *f = path + strlen(path);
    while (f != path && *f != '/') {
        --f;
    }
    return *f == '/' ? f + 1 : path;
}

extern int _monad_event_vformat_err(
    char *error_buf, size_t size, monad_source_location_t const *srcloc,
    int err, char const *format, va_list ap)
{
    size_t len;
    int rc = 0;

    if (srcloc != nullptr) {
        rc = snprintf(
            error_buf,
            size,
            "%s@%s:%u",
            srcloc->function_name,
            final_path_component(srcloc->file_name),
            srcloc->line);
    }
    len = rc > 0 ? (size_t)rc : 0;
    if (len < size - 2) {
        error_buf[len++] = ':';
        error_buf[len++] = ' ';
        rc = vsnprintf(error_buf + len, size - len, format, ap);
        if (rc >= 0) {
            len += (size_t)rc;
        }
    }
    if (err != 0 && len < size) {
        (void)snprintf(
            error_buf + len, size - len, ": %s (%d)", strerror(err), err);
    }
    return err;
}

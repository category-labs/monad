#include <stdarg.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>

#include <monad/mpt/logger.h>

static log_function_t current_logger = nullptr;

void db_set_logger(log_function_t logger)
{
    current_logger = logger;
}

void log_message(log_level_t const level, char const *format, ...)
{
    va_list args;
    va_start(args, format);

    char buf[10240];
    char *const buf_end = buf + sizeof(buf);
    char *p = stpcpy(buf, "[Db] ");
    vsnprintf(p, (size_t)(buf_end - p), format, args);
    if (current_logger) {
        current_logger(level, buf);
    }
    else {
        fputs(buf, stdout);
    }
    va_end(args);
}

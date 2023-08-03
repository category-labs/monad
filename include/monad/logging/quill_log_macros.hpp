#pragma once

#define MONAD_LOG_TRACE_L3(logger, fmt, ...)                                   \
    QUILL_LOG_TRACE_L3(logger, fmt, ##__VA_ARGS__)
#define MONAD_LOG_TRACE_L2(logger, fmt, ...)                                   \
    QUILL_LOG_TRACE_L2(logger, fmt, ##__VA_ARGS__)
#define MONAD_LOG_TRACE_L1(logger, fmt, ...)                                   \
    QUILL_LOG_TRACE_L1(logger, fmt, ##__VA_ARGS__)
#define MONAD_LOG_DEBUG(logger, fmt, ...)                                      \
    QUILL_LOG_DEBUG(logger, fmt, ##__VA_ARGS__)
#define MONAD_LOG_INFO(logger, fmt, ...)                                       \
    QUILL_LOG_INFO(logger, fmt, ##__VA_ARGS__)
#define MONAD_LOG_WARNING(logger, fmt, ...)                                    \
    QUILL_LOG_WARNING(logger, fmt, ##__VA_ARGS__)
#define MONAD_LOG_ERROR(logger, fmt, ...)                                      \
    QUILL_LOG_ERROR(logger, fmt, ##__VA_ARGS__)
#define MONAD_LOG_CRITICAL(logger, fmt, ...)                                   \
    QUILL_LOG_CRITICAL(logger, fmt, ##__VA_ARGS__)

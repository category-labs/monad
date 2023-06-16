#pragma once

#define MONAD_LOG_HELPER(...) (void)(sizeof(__VA_ARGS__))

#define MONAD_LOG_TRACE_L3(logger, fmt, ...)                                   \
    do {                                                                       \
        MONAD_LOG_HELPER(__VA_ARGS__);                                         \
        (void)sizeof(logger);                                                  \
    }                                                                          \
    while (0)

#define MONAD_LOG_TRACE_L2(logger, fmt, ...)                                   \
    do {                                                                       \
        MONAD_LOG_HELPER(__VA_ARGS__);                                         \
        (void)sizeof(logger);                                                  \
    }                                                                          \
    while (0)

#define MONAD_LOG_TRACE_L1(logger, fmt, ...)                                   \
    do {                                                                       \
        MONAD_LOG_HELPER(__VA_ARGS__);                                         \
        (void)sizeof(logger);                                                  \
    }                                                                          \
    while (0)

#define MONAD_LOG_DEBUG(logger, fmt, ...)                                      \
    do {                                                                       \
        MONAD_LOG_HELPER(__VA_ARGS__);                                         \
        (void)sizeof(logger);                                                  \
    }                                                                          \
    while (0)

#define MONAD_LOG_INFO(logger, fmt, ...)                                       \
    do {                                                                       \
        MONAD_LOG_HELPER(__VA_ARGS__);                                         \
        (void)sizeof(logger);                                                  \
    }                                                                          \
    while (0)

#define MONAD_LOG_WARNING(logger, fmt, ...)                                    \
    do {                                                                       \
        MONAD_LOG_HELPER(__VA_ARGS__);                                         \
        (void)sizeof(logger);                                                  \
    }                                                                          \
    while (0)

#define MONAD_LOG_ERROR(logger, fmt, ...)                                      \
    do {                                                                       \
        MONAD_LOG_HELPER(__VA_ARGS__);                                         \
        (void)sizeof(logger);                                                  \
    }                                                                          \
    while (0)

#define MONAD_LOG_CRITICAL(logger, fmt, ...)                                   \
    do {                                                                       \
        MONAD_LOG_HELPER(__VA_ARGS__);                                         \
        (void)sizeof(logger);                                                  \
    }                                                                          \
    while (0)

#pragma once

#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

enum log_level_t : uint8_t
{
    DEBUG = 0,
    INFO = 1,
    ERROR = 2
};
typedef enum log_level_t log_level_t;

typedef void (*log_function_t)(log_level_t level, char const *msg);

void db_set_logger(log_function_t logger);
void log_message(log_level_t level, char const *format, ...);

#ifdef __cplusplus
}
#endif

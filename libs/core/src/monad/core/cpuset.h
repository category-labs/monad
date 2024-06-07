#pragma once

#include <sched.h>

#ifdef __cplusplus
extern "C"
{
#endif

cpu_set_t monad_parse_cpuset(char *);

#ifdef __cplusplus
}
#endif

#pragma once

#include <sched.h>

#ifdef __cplusplus
extern "C"
{
#endif

cpu_set_t monad_parse_cpuset(char *);

cpu_set_t monad_cpuset_from_cpu(int);

int monad_alloc_cpu(cpu_set_t *);

#ifdef __cplusplus
}
#endif

#pragma once

#include <sched.h>

#ifdef __cplusplus
extern "C"
{
#endif

void monad_cgroup_init();

cpu_set_t monad_cgroup_cpuset();

#ifdef __cplusplus
}
#endif

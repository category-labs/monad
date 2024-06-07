#pragma once

#include <sched.h>

void monad_cgroup_init();

cpu_set_t monad_cgroup_cpuset();
